{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuasiQuotes #-}
module BeamLR where

import Data.Kind
import Data.Record.Generic
import Data.Record.Generic.Show
import qualified Data.Record.Generic.Rep as R
import Data.Record.TH
import Database.Beam.Schema.Tables
import Unsafe.Coerce
import Control.Applicative

type CheckBeamFields tbl = (Constraints (tbl Exposed) CheckBeamField)

class CheckBeamField a
instance CheckBeamField (Exposed x)

checkBeamFields :: CheckBeamFields tbl => Rep I (tbl f) -> Rep (Columnar' f) (tbl Exposed)
checkBeamFields = unsafeCoerce
{-# NOINLINE checkBeamFields #-}

uncheckBeamFields :: CheckBeamFields tbl => Rep (Columnar' f) (tbl Exposed) -> Rep I (tbl f)
uncheckBeamFields = unsafeCoerce
{-# NOINLINE uncheckBeamFields #-}

gzipBeamFieldsM ::
  forall tbl f g h m.
  ( Applicative m
  , Generic (tbl f)
  , Generic (tbl g)
  , Generic (tbl h)
  , Generic (tbl Exposed)
  , CheckBeamFields tbl
  )
  => (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
  -> tbl f -> tbl g -> m (tbl h)
gzipBeamFieldsM combine f g =
  to <$> zipBeamFieldsM_Rep combine (from f) (from g)

zipBeamFieldsM_Rep ::
  forall tbl f g h m.
  ( Applicative m
  , Generic (tbl f)
  , Generic (tbl g)
  , Generic (tbl h)
  , Generic (tbl Exposed)
  , CheckBeamFields tbl
  )
  => (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
  -> Rep I (tbl f) -> Rep I (tbl g) -> m (Rep I (tbl h))
zipBeamFieldsM_Rep combine f g =
  let
    ef :: Rep (Columnar' f) (tbl Exposed)
    ef = checkBeamFields f

    eg :: Rep (Columnar' g) (tbl Exposed)
    eg = checkBeamFields g

    eh :: m (Rep (Columnar' h) (tbl Exposed))
    eh = R.zipWithM combine ef eg

    h :: m (Rep I (tbl h))
    h = uncheckBeamFields <$> eh
  in
    h

gtblSkeleton ::
  forall tbl.
  ( Generic (tbl Ignored)
  , Generic (tbl Exposed)
  , CheckBeamFields tbl
  )
  => TableSkeleton tbl
gtblSkeleton =
  let
    e :: Rep (Columnar' Ignored) (tbl Exposed)
    e = R.pure (Columnar' Ignored)
  in
    to (uncheckBeamFields e)

-- Example

largeRecord defaultLazyOptions [d|
     data LRTable (f :: Type -> Type) =
       MkLRTable
         { fld1 :: Columnar f Int
         , fld2 :: Columnar f Int
         , fld3 :: Columnar f Bool
         , fld4 :: Columnar f Char
         , fld5 :: Columnar f Int
         , fld6 :: Columnar f String
         }
  |]

instance Show (LRTable Maybe) where
  showsPrec = gshowsPrec

instance Beamable LRTable where
  zipBeamFieldsM = gzipBeamFieldsM
  tblSkeleton = gtblSkeleton

ex1 :: LRTable Maybe
ex1 = [lr| MkLRTable |] (Just 2) (Just 2) Nothing (Just 'x') (Just 4) Nothing

ex2 :: LRTable Maybe
ex2 = [lr| MkLRTable |] Nothing (Just 3) Nothing Nothing Nothing (Just "foo")

ex3 :: I (LRTable Maybe)
ex3 = zipBeamFieldsM (\ (Columnar' x) (Columnar' y) -> I (Columnar' (x <|> y))) ex1 ex2
