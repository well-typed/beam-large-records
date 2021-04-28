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
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
module BeamSOP where

import Database.Beam.Schema.Tables
import Data.Coerce
import Data.Kind
import Data.SOP
import Data.SOP.NP
import Generics.SOP
import qualified GHC.Generics as GHC
import Control.Applicative

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

class CheckBeamField (f :: Type -> Type) (a :: Type) (b :: Type) where
  checkBeamField :: a -> BeamField f b
  uncheckBeamField :: BeamField f b -> a

instance (a ~ Columnar f x) => CheckBeamField f a (Exposed x) where
  checkBeamField x = SimpleBeamField (Columnar' x)
  uncheckBeamField (SimpleBeamField (Columnar' x)) = x

instance (Beamable tbl) => CheckBeamField f (tbl f) (tbl Exposed) where
  checkBeamField x = MixinBeamField x
  uncheckBeamField (MixinBeamField x) = x

instance (Beamable tbl) => CheckBeamField f (tbl (Nullable f)) (tbl (Nullable Exposed)) where
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

class (c b a) => Flip c a b
instance (c b a) => Flip c a b

checkBeamFields :: forall f xs ys. AllZip (CheckBeamField f) xs ys => NP I xs -> NP (BeamField f) ys
checkBeamFields = trans_NP (Proxy @(CheckBeamField f)) (checkBeamField . unI)

uncheckBeamFields :: forall f xs ys. AllZip (Flip (CheckBeamField f)) xs ys => NP (BeamField f) xs -> NP I ys
uncheckBeamFields = trans_NP (Proxy @(Flip (CheckBeamField f))) (I . uncheckBeamField)

zipBeamFieldsM_NP ::
  forall f g h m xs ys zs bs.
  ( Applicative m
  , AllZip (CheckBeamField f) xs bs
  , AllZip (CheckBeamField g) ys bs
  , AllZip (Flip (CheckBeamField h)) bs zs
  )
  => (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
  -> NP I xs -> NP I ys -> m (NP I zs)
zipBeamFieldsM_NP combine npxs npys =
  let
    npbxs :: NP (BeamField f) bs
    npbxs = checkBeamFields npxs

    npbys :: NP (BeamField g) bs
    npbys = checkBeamFields npys

    npmzs :: NP (m :.: BeamField h) bs
    npmzs = zipWith_NP (\ x y -> Comp (combineBeamFields combine x y)) npbxs npbys

    npbzs :: m (NP (BeamField h) bs)
    npbzs = sequence'_NP npmzs

    npzs :: m (NP I zs)
    npzs = uncheckBeamFields <$> npbzs
  in
    npzs

gzipBeamFieldsM ::
  forall tbl f g h m xs ys zs bs.
  ( Applicative m
  , IsProductType (tbl f) xs
  , IsProductType (tbl g) ys
  , IsProductType (tbl h) zs
  , IsProductType (tbl Exposed) bs
  , IsProductType (tbl Exposed) bs
  , IsProductType (tbl Exposed) bs
  , AllZip (CheckBeamField f) xs bs
  , AllZip (CheckBeamField g) ys bs
  , AllZip (Flip (CheckBeamField h)) bs zs
  )
  => (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
  -> tbl f -> tbl g -> m (tbl h)
gzipBeamFieldsM combine f g =
  productTypeTo <$> zipBeamFieldsM_NP @f @g @h @m @xs @ys @zs @bs combine (productTypeFrom f) (productTypeFrom g)

gzipBeamFieldsM' ::
  ( Applicative m
  , IsTableType tbl f
  , IsTableType tbl g
  , IsTableType tbl h
  )
  => (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
  -> tbl f -> tbl g -> m (tbl h)
gzipBeamFieldsM' combine f g =
  gzipBeamFieldsM combine f g

gtblSkeleton ::
  forall tbl xs bs.
  ( IsProductType (tbl Ignored) xs
  , IsProductType (tbl Exposed) bs
  , All IgnoreBeamField bs
  , AllZip (Flip (CheckBeamField Ignored)) bs xs
  )
  =>
  TableSkeleton tbl
gtblSkeleton =
  let
    npbs :: NP (BeamField Ignored) bs
    npbs = cpure_NP (Proxy @IgnoreBeamField) ignoreBeamField

    npxs :: NP I xs
    npxs = uncheckBeamFields npbs
  in
    productTypeTo npxs

gtblSkeleton' ::
  (IsTableType tbl Ignored)
  => TableSkeleton tbl
gtblSkeleton' =
  gtblSkeleton

-- Example

data SOPTable (f :: Type -> Type) =
  MkSOPTable
    { fld1 :: !(Columnar f Int)
    , fld2 :: !(Columnar f Int)
    , fld3 :: !(Columnar f Bool)
    , fld4 :: !(Columnar f Char)
    , fld5 :: !(Columnar f Int)
    , fld6 :: !(Columnar f String)
    , fld7 :: !(SOPTable2 f)
    , fld8 :: !(PrimaryKey SOPTable2 f)
    }
  deriving (GHC.Generic, Generic)

deriving instance Show (SOPTable Maybe)

data SOPTable2 (f :: Type -> Type) =
  MkSOPTable2
    { fld21 :: Columnar f Int
    , fld22 :: Columnar f Int
    }
  deriving (GHC.Generic, Generic)

deriving instance Show (SOPTable2 Maybe)

instance Table SOPTable2 where
  data PrimaryKey SOPTable2 f = SOPTable2Key (Columnar f Int)
    deriving (GHC.Generic, Generic)
  primaryKey = SOPTable2Key . fld21

deriving instance Show (PrimaryKey SOPTable2 Maybe)

instance Beamable (PrimaryKey SOPTable2) where
  zipBeamFieldsM = gzipBeamFieldsM
  tblSkeleton = gtblSkeleton

instance Beamable SOPTable where
  zipBeamFieldsM = gzipBeamFieldsM
  tblSkeleton = gtblSkeleton

instance Beamable SOPTable2 where
  zipBeamFieldsM = gzipBeamFieldsM
  tblSkeleton = gtblSkeleton

ex1 :: SOPTable Maybe
ex1 = MkSOPTable (Just 2) (Just 2) Nothing (Just 'x') (Just 4) Nothing (MkSOPTable2 (Just 8) Nothing) (SOPTable2Key (Just 11))

ex2 :: SOPTable Maybe
ex2 = MkSOPTable Nothing (Just 3) Nothing Nothing Nothing (Just "foo") (MkSOPTable2 Nothing (Just 9)) (SOPTable2Key (Just 22))

ex3 :: I (SOPTable Maybe)
ex3 = zipBeamFieldsM (\ (Columnar' x) (Columnar' y) -> I (Columnar' (x <|> y))) ex1 ex2

-- All the rest if only for DerivingVia, which doesn't work anyway
-- because of the `m` parameter appearing in the type of zipBeamFieldsM,
-- and the resulting roles problems.

newtype SOPGenerically (tbl :: (Type -> Type) -> Type) (f :: (Type -> Type)) =
  SOPGenerically { unSOPGenerically :: tbl f }

class
  ( IsProductType (tbl f) (ProductCode (tbl f))
  , IsProductType (tbl Exposed) (ProductCode (tbl Exposed))
  , AllZip (CheckBeamField f) (ProductCode (tbl f)) (ProductCode (tbl Exposed))
  , AllZip (Flip (CheckBeamField f)) (ProductCode (tbl Exposed)) (ProductCode (tbl f))
  , All IgnoreBeamField (ProductCode (tbl Exposed))
  ) => IsTableType tbl f
instance
  ( IsProductType (tbl f) (ProductCode (tbl f))
  , IsProductType (tbl Exposed) (ProductCode (tbl Exposed))
  , AllZip (CheckBeamField f) (ProductCode (tbl f)) (ProductCode (tbl Exposed))
  , AllZip (Flip (CheckBeamField f)) (ProductCode (tbl Exposed)) (ProductCode (tbl f))
  , All IgnoreBeamField (ProductCode (tbl Exposed))
  ) => IsTableType tbl f

instance
  ( Applicative m
  , forall f. IsTableType tbl f
  )
  => Beamable (SOPGenerically tbl) where
  zipBeamFieldsM combine (SOPGenerically tbl1) (SOPGenerically tbl2) =
    SOPGenerically <$> gzipBeamFieldsM' combine tbl1 tbl2
  tblSkeleton = SOPGenerically gtblSkeleton'

