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
{-# LANGUAGE GADTs #-}
module BeamLR3 where

import Data.Kind
import Data.Record.Generic
import Data.Record.Generic.Show
import qualified Data.Record.Generic.Rep as R
import Data.Record.TH
import Database.Beam.Schema.Tables
import Unsafe.Coerce
import Control.Applicative
import Data.Coerce

type CheckBeamFields f tbl = (Constraints (tbl Exposed) (CheckBeamField f))

class CheckBeamField f b where
  type family OriginalType f b :: Type
  checkBeamField :: OriginalType f b -> BeamField f b
  uncheckBeamField :: BeamField f b -> OriginalType f b

data BeamField :: (Type -> Type) -> Type -> Type where
  SimpleBeamField        :: Columnar' f a -> BeamField f (Exposed a)
  MixinBeamField         :: Beamable tbl => tbl f -> BeamField f (tbl Exposed)
  NullableMixinBeamField :: Beamable tbl => tbl (Nullable f) -> BeamField f (tbl (Nullable Exposed))

combineBeamFields ::
  forall f g h m b.
  (Applicative m)
  => (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
  -> BeamField f b -> BeamField g b -> m (BeamField h b)
combineBeamFields combine (SimpleBeamField f)        (SimpleBeamField g)        = SimpleBeamField <$> combine f g
combineBeamFields combine (MixinBeamField f)         (MixinBeamField g)         = MixinBeamField <$> zipBeamFieldsM combine f g
combineBeamFields combine (NullableMixinBeamField f) (NullableMixinBeamField g) =
  NullableMixinBeamField <$> zipBeamFieldsM (adapt combine) f g
  where
    adapt ::
         (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
      -> (forall a. Columnar' (Nullable f) a -> Columnar' (Nullable g) a -> m (Columnar' (Nullable h) a))
    adapt c fa ga = toNullable <$> c (fromNullable fa) (fromNullable ga)

    toNullable :: forall w a. Columnar' w (Maybe a) -> Columnar' (Nullable w) a
    toNullable = coerce

    fromNullable :: forall w a. Columnar' (Nullable w) a -> Columnar' w (Maybe a)
    fromNullable = coerce


instance CheckBeamField f (Exposed x) where
  type OriginalType f (Exposed x) = Columnar f x
  checkBeamField x = SimpleBeamField (Columnar' x)
  uncheckBeamField (SimpleBeamField (Columnar' x)) = x

instance (Beamable tbl) => CheckBeamField f (tbl Exposed) where
  type OriginalType f (tbl Exposed) = tbl f
  checkBeamField x = MixinBeamField x
  uncheckBeamField (MixinBeamField x) = x

instance (Beamable tbl) => CheckBeamField f (tbl (Nullable Exposed)) where
  type OriginalType f (tbl (Nullable Exposed)) = tbl (Nullable f)
  checkBeamField x = NullableMixinBeamField x
  uncheckBeamField (NullableMixinBeamField x) = x

class IgnoreBeamField (a :: Type) where
  ignoreBeamField :: BeamField Ignored a

instance IgnoreBeamField (Exposed x) where
  ignoreBeamField = SimpleBeamField (Columnar' Ignored)

instance Beamable tbl => IgnoreBeamField (tbl Exposed) where
  ignoreBeamField = MixinBeamField tblSkeleton

instance Beamable tbl => IgnoreBeamField (tbl (Nullable Exposed)) where
  ignoreBeamField = NullableMixinBeamField (unI (zipBeamFieldsM transform tblSkeleton tblSkeleton))
    where
      transform :: Columnar' Ignored a -> Columnar' Ignored a -> I (Columnar' (Nullable Ignored) a)
      transform _ _ = I (Columnar' Ignored)

newtype O f a = O { unO :: OriginalType f a }

expose :: CheckBeamFields f tbl => Rep I (tbl f) -> Rep (O f) (tbl Exposed)
expose = unsafeCoerce
{-# NOINLINE expose #-}

unexpose :: CheckBeamFields f tbl => Rep (O f) (tbl Exposed) -> Rep I (tbl f)
unexpose = unsafeCoerce
{-# NOINLINE unexpose #-}

checkBeamFields ::
  forall f tbl. (Generic (tbl Exposed), CheckBeamFields f tbl)
  => Rep I (tbl f) -> Rep (BeamField f) (tbl Exposed)
checkBeamFields = R.cmap (Proxy @(CheckBeamField f)) (checkBeamField . unO) . expose

uncheckBeamFields :: forall f tbl. (Generic (tbl Exposed), CheckBeamFields f tbl)
  => CheckBeamFields f tbl => Rep (BeamField f) (tbl Exposed) -> Rep I (tbl f)
uncheckBeamFields = unexpose . R.cmap (Proxy @(CheckBeamField f)) (O . uncheckBeamField)

gzipBeamFieldsM ::
  forall tbl f g h m.
  ( Applicative m
  , Generic (tbl f)
  , Generic (tbl g)
  , Generic (tbl h)
  , Generic (tbl Exposed)
  , CheckBeamFields f tbl
  , CheckBeamFields g tbl
  , CheckBeamFields h tbl
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
  , CheckBeamFields f tbl
  , CheckBeamFields g tbl
  , CheckBeamFields h tbl
  )
  => (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
  -> Rep I (tbl f) -> Rep I (tbl g) -> m (Rep I (tbl h))
zipBeamFieldsM_Rep combine f g =
  let
    ef :: Rep (BeamField f) (tbl Exposed)
    ef = checkBeamFields f

    eg :: Rep (BeamField g) (tbl Exposed)
    eg = checkBeamFields g

    eh :: m (Rep (BeamField h) (tbl Exposed))
    eh = R.zipWithM (combineBeamFields combine) ef eg

    h :: m (Rep I (tbl h))
    h = uncheckBeamFields <$> eh
  in
    h

gtblSkeleton ::
  forall tbl.
  ( Generic (tbl Ignored)
  , Generic (tbl Exposed)
  , Constraints (tbl Exposed) IgnoreBeamField
  , CheckBeamFields Ignored tbl
  )
  => TableSkeleton tbl
gtblSkeleton =
  let
    e :: Rep (BeamField Ignored) (tbl Exposed)
    e = R.cpure (Proxy @IgnoreBeamField) ignoreBeamField
  in
    to (uncheckBeamFields e)

-- Example

largeRecord defaultLazyOptions [d|
     data LRTable2 (f :: Type -> Type) =
       MkLRTable2
         { fld21 :: Columnar f Int
         , fld22 :: Columnar f Int
         }
  |]

largeRecord defaultLazyOptions [d|
     data LRTable (f :: Type -> Type) =
       MkLRTable
         { fld1 :: Columnar f Int
         , fld2 :: Columnar f Int
         , fld3 :: Columnar f Bool
         , fld4 :: Columnar f Char
         , fld5 :: Columnar f Int
         , fld6 :: Columnar f String
         , fld7 :: LRTable2 f
         }
  |]

instance Show (LRTable Maybe) where
  showsPrec = gshowsPrec

instance Show (LRTable2 Maybe) where
  showsPrec = gshowsPrec

instance Beamable LRTable where
  zipBeamFieldsM = gzipBeamFieldsM
  tblSkeleton = gtblSkeleton

instance Beamable LRTable2 where
  zipBeamFieldsM = gzipBeamFieldsM
  tblSkeleton = gtblSkeleton

ex1 :: LRTable Maybe
ex1 = [lr| MkLRTable |] (Just 2) (Just 2) Nothing (Just 'x') (Just 4) Nothing ([lr| MkLRTable2 |] (Just 8) Nothing)

ex2 :: LRTable Maybe
ex2 = [lr| MkLRTable |] Nothing (Just 3) Nothing Nothing Nothing (Just "foo") ([lr| MkLRTable2 |] Nothing (Just 9))

ex3 :: I (LRTable Maybe)
ex3 = zipBeamFieldsM (\ (Columnar' x) (Columnar' y) -> I (Columnar' (x <|> y))) ex1 ex2
