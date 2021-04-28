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
{-# LANGUAGE StandaloneDeriving #-}
module BeamLR where

import Data.Kind
import Data.Record.Generic
import Data.Record.Generic.Show
import qualified Data.Record.Generic.Rep as R
import Data.Record.TH
import Database.Beam.Schema.Tables
import Unsafe.Coerce
import Control.Applicative
import Data.Coerce
import qualified GHC.Generics as GHC

-- | The generic code for the 'Beamable' class in beam-core distinguishes three different
-- shapes of fields. Simple fields are applications of 'Columnar', mixins / foreign key references
-- are references to other tables that are themselves 'Beamable', and nullable mixins are references
-- to other tables with an additional 'Nullable' flag (which essentially causes 'Maybe') to be
-- applied to all columns within that table.
--
data BeamField :: (Type -> Type) -> Type -> Type where
  SimpleBeamField        :: Columnar' f a -> BeamField f (Exposed a)
  MixinBeamField         :: Beamable tbl => tbl f -> BeamField f (tbl Exposed)
  NullableMixinBeamField :: Beamable tbl => tbl (Nullable f) -> BeamField f (tbl (Nullable Exposed))

-- | Once we know which form of beam fields we have to deal with, we can combine matching beam fields.
-- The code for this function corresponds to three different instances for the
-- 'Database.Beam.Schema.Tables.GZipTables' class, and is almost directly taken from there.
--
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

-- | In the constraint 'CheckBeamField f b', the type @b@ is supposed to be the type
-- of a field of some type @tbl f@ where @f@ has been instantiated to 'Exposed'.
--
-- 'Exposed' is defined within beam-core and can be used to distinguish the different
-- kinds of fields we are interested in.
--
-- From the shape of @b@, we can then learn the shape of @tbl f@ if @f@ is unknown.
--
-- Each of the instances are corresponding to one of the constructors of 'BeamField'.
--
class CheckBeamField f b where
  -- | If @tbl Exposed@ has a field of type @b@, then @tbl f@ is supposed to
  -- have the type @OriginalType f b@.
  type family OriginalType f b :: Type
  checkBeamField :: OriginalType f b -> BeamField f b
  uncheckBeamField :: BeamField f b -> OriginalType f b

-- If a field in the table is of shape @Columnar f x@, then @Columnar Exposed x@
-- reduces to @Exposed x@. So in turn we're assuming that if we observe @Exposed x@,
-- we require the shape of the field to be @Columnar f x@.
--
instance CheckBeamField f (Exposed x) where
  type OriginalType f (Exposed x) = Columnar f x
  checkBeamField x = SimpleBeamField (Columnar' x)
  uncheckBeamField (SimpleBeamField (Columnar' x)) = x

-- If a field in the table is of shape @tbl f@, then we observe @tbl Exposed@
-- on the instantiation to @Exposed@.
--
instance (Beamable tbl) => CheckBeamField f (tbl Exposed) where
  type OriginalType f (tbl Exposed) = tbl f
  checkBeamField x = MixinBeamField x
  uncheckBeamField (MixinBeamField x) = x

-- If a field in the table is of shape @tbl (Nullable f)@, then we observe
-- @tbl (Nullable Exposed)@ on the instantiation to @Exposed@.
--
instance (Beamable tbl) => CheckBeamField f (tbl (Nullable Exposed)) where
  type OriginalType f (tbl (Nullable Exposed)) = tbl (Nullable f)
  checkBeamField x = NullableMixinBeamField x
  uncheckBeamField (NullableMixinBeamField x) = x

-- | Require all fields in a table to be in one of the three beam field
-- cases, by traversing the constraints corresponding to @tbl Exposed@.
--
type CheckBeamFields f tbl = (Constraints (tbl Exposed) (CheckBeamField f))

-- | Corresponds roughly to the 'gTblSkeleton' implementation in the
-- 'GTableSkeleton' class.
--
-- Code is taken from the instances of that class.
--
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

-- | Coercion that makes use of the identity we have for 'OriginalType'.
-- For every field @b@ contained in @tbl Exposed@, we know that @OriginalType f b@
-- is the corresponding field of @tbl f@.
--
expose :: CheckBeamFields f tbl => Rep I (tbl f) -> Rep (O f) (tbl Exposed)
expose = unsafeCoerce
{-# NOINLINE expose #-}

-- | Inverse of 'expose', using the same type identity.
--
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

-- | Generic implementation of 'zipBeamFieldsM' that can be used in 'Beamable' instances.
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

-- | Generic implementation of 'tblSkeleton' that can be used in 'Beamable' instances.
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
     data LRTableA (f :: Type -> Type) =
       MkLRTableA
         { fldA1 :: Columnar f Int
         , fldA2 :: Columnar f Int
         }
  |]

largeRecord defaultLazyOptions [d|
     data LRTableB (f :: Type -> Type) =
       MkLRTableB
         { fldB1 :: Columnar f Int
         , fldB2 :: Columnar f Int
         , fldB3 :: Columnar f Bool
         , fldB4 :: Columnar f Char
         , fldB5 :: Columnar f Int
         , fldB6 :: Columnar f String
         , fldB7 :: LRTableA f
         , fldB8 :: PrimaryKey LRTableA f
         , fldB9 :: LRTableA (Nullable f)
         }
  |]

instance Show (LRTableA Maybe) where
  showsPrec = gshowsPrec

instance Show (LRTableA (Nullable Maybe)) where
  showsPrec = gshowsPrec

instance Show (LRTableB Maybe) where
  showsPrec = gshowsPrec

instance Beamable LRTableA where
  zipBeamFieldsM = gzipBeamFieldsM
  tblSkeleton = gtblSkeleton

instance Beamable LRTableB where
  zipBeamFieldsM = gzipBeamFieldsM
  tblSkeleton = gtblSkeleton

instance Table LRTableA where
  newtype PrimaryKey LRTableA f = LRTableAKey (Columnar f Int)
    deriving (GHC.Generic)
  primaryKey = LRTableAKey . fldA1

instance Beamable (PrimaryKey LRTableA) -- using standard derivation via GHC.Generics
deriving instance Show (PrimaryKey LRTableA Maybe)

ex1 :: LRTableB Maybe
ex1 =
  [lr| MkLRTableB |]
    (Just 2)
    (Just 2)
    Nothing
    (Just 'x')
    (Just 4)
    Nothing
    ([lr| MkLRTableA |] (Just 8) Nothing)
    (LRTableAKey (Just 11))
    ([lr| MkLRTableA |] (Just (Just 8)) Nothing)

ex2 :: LRTableB Maybe
ex2 =
  [lr| MkLRTableB |]
    Nothing
    (Just 3)
    Nothing
    Nothing
    Nothing
    (Just "foo")
    ([lr| MkLRTableA |] Nothing (Just 9))
    (LRTableAKey (Just 22))
    ([lr| MkLRTableA |] (Just Nothing) (Just Nothing))

ex3 :: I (LRTableB Maybe)
ex3 = zipBeamFieldsM (\ (Columnar' x) (Columnar' y) -> I (Columnar' (x <|> y))) ex1 ex2
