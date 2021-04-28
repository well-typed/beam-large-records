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
module BeamLR2 where

import Data.Kind
import Data.Record.Generic
import qualified Data.Record.Generic.Rep as R
import Data.Record.TH
import qualified Data.Vector as V
import Database.Beam.Schema.Tables
import qualified GHC.Generics as GHC
import Unsafe.Coerce

class GenericBeamable (table :: b -> Type) where
  type ConstraintsBeamable table :: (Type -> Type -> Type -> Type -> Constraint) -> b -> b -> b -> Constraint

instance GenericBeamable ManTable where
  type ConstraintsBeamable ManTable = ManTableConstraints

class
  ( c (Columnar Exposed Int)    (Columnar f Int)    (Columnar g Int)    (Columnar h Int)
  , c (Columnar Exposed Bool)   (Columnar f Bool)   (Columnar g Bool)   (Columnar h Int)
  , c (Columnar Exposed Char)   (Columnar f Char)   (Columnar g Char)   (Columnar h Char)
  , c (Columnar Exposed String) (Columnar f String) (Columnar g String) (Columnar h String)
  ) => ManTableConstraints c f g h

unColumnar' :: Columnar' f a -> Columnar f a
unColumnar' (Columnar' fa) = fa

class SingleLRBeamComponent f g h ea fa ga ha where
  zipSingle :: Applicative m => Proxy ea -> (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a)) -> fa -> ga -> m ha
instance (fa ~ Columnar f a, ga ~ Columnar g a, ha ~ Columnar h a) => SingleLRBeamComponent f g h (Exposed a) fa ga ha where
  zipSingle _ combine fa ga = unColumnar' <$> combine @a (Columnar' fa) (Columnar' ga)
instance (Beamable tbl) => SingleLRBeamComponent f g h (tbl Exposed) (tbl f) (tbl g) (tbl h) where
  zipSingle _ combine fa ga = zipBeamFieldsM combine fa ga
-- instance (Beamable tbl) => SingleLRBeamComponent f g h (tbl (Nullable Exposed)) (tbl f) (tbl g) (tbl h) where

gzipBeamFieldsM' ::
  (GenericBeamable table, ConstraintsBeamable table (SingleLRBeamComponent f g h) f g h, Applicative m)
  => (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
  -> Rep I (table f) -> Rep I (table g) -> m (Rep I (table h))
gzipBeamFieldsM' combine rf rg =
  undefined -- sequenceA (R.zipWith apFn (R.zipWith apFn (pure f') _) (R.zip rf rg))

data ManTable (f :: Type -> Type) =
  MkManTable
    { mfld1 :: Columnar f Int
    , mfld2 :: Columnar f Int
    , mfld3 :: Columnar f Bool
    , mfld4 :: Columnar f Char
    , mfld5 :: Columnar f Int
    , mfld6 :: Columnar f String
    }
  deriving (GHC.Generic)

largeRecord defaultLazyOptions [d|
     data LRTable (f :: Type -> Type) =
       MkLRTable
         { fld1 :: Columnar f Int
         , fld2 :: Columnar f Int
         , fld3 :: Columnar f Bool
         , fld4 :: Columnar f Char
         , fld5 :: Columnar f Int
         , fld6 :: Columnar f String
         -- , fld7 :: PrimaryKey ManTable f
         }
  |]

instance Beamable LRTable where
  zipBeamFieldsM ::
    forall m f g h.
    Applicative m
    => (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
    -> LRTable f
    -> LRTable g
    -> m (LRTable h)
  zipBeamFieldsM combine tf tg =
    gZipBeamFieldsM combine tf tg

  tblSkeleton =
    let
      tmp :: Rep (Columnar' Ignored) (LRTable I)
      tmp = R.pure (Columnar' Ignored)
    in
      to (scfIIf tmp)

-- Identity with Exposed:
--
-- Columnar Exposed a ~ Exposed a

type TableConstraint table = (Constraints (table Exposed) ColumnarCoercible)
type TableConstraint' table = (Constraints (table Exposed) (ColumnarCoercible' table))

class ColumnarCoercible a
instance ColumnarCoercible (Exposed a)
-- instance ColumnarCoercible (tbl Exposed)
-- instance ColumnarCoercible (tbl Exposed)

-- Cool idea, but I'm afraid it's nevertheless useless. We have no way of actually
-- establishing (and statically checking) the extra constraints.
--
class ColumnarCoercible' (table :: (Type -> Type) -> Type) a where
  type ExtraConstraints table a (f :: Type -> Type) (g :: Type -> Type) (h :: Type -> Type) fa ga ha :: Constraint
  apply ::
    (ExtraConstraints table a f g h fa ga ha, Applicative m)
    => (forall x. Columnar' f x -> Columnar' g x -> m (Columnar' h x)) -> fa -> ga -> m ha

instance ColumnarCoercible' table (Exposed a) where
  type ExtraConstraints table (Exposed a) f g h fa ga ha = (fa ~ Columnar f a, ga ~ Columnar g a, ha ~ Columnar h a)
  apply combine fa ga = unColumnar' <$> combine @a (Columnar' fa) (Columnar' ga)

instance Beamable tbl => ColumnarCoercible' table (tbl Exposed) where
  type ExtraConstraints table (tbl Exposed) f g h fa ga ha = (fa ~ tbl f, ga ~ tbl g, ha ~ tbl h)
  apply combine fa ga = zipBeamFieldsM combine fa ga

type family UnExposed (a :: Type) :: Type where
  UnExposed (Exposed a) = a

scfIIf :: TableConstraint table => Rep (Columnar' f) (table I) -> Rep I (table f)
scfIIf = unsafeCoerce
{-# NOINLINE scfIIf #-}

scIffI :: TableConstraint table => Rep I (table f) -> Rep (Columnar' f) (table I)
scIffI = unsafeCoerce
{-# NOINLINE scIffI #-}

data RefTable (f :: Type -> Type) =
  MkRefTable
    { rfld1 :: Columnar f Int
    , rfld2 :: Columnar f Int
    , rfld3 :: Columnar f Bool
    , rfld4 :: Columnar f Char
    , rfld5 :: Columnar f Int
    , rfld6 :: Columnar f String
    }
  deriving (GHC.Generic, Beamable)

instance Beamable ManTable where
  zipBeamFieldsM ::
    forall m f g h.
    Applicative m
    => (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
    -> ManTable f
    -> ManTable g
    -> m (ManTable h)
  zipBeamFieldsM combine tf tg =
    pure MkManTable
    <*> coe @Int    combine (mfld1 tf) (mfld1 tg)
    <*> coe @Int    combine (mfld2 tf) (mfld2 tg)
    <*> coe @Bool   combine (mfld3 tf) (mfld3 tg)
    <*> coe @Char   combine (mfld4 tf) (mfld4 tg)
    <*> coe @Int    combine (mfld5 tf) (mfld5 tg)
    <*> coe @String combine (mfld6 tf) (mfld6 tg)
    where
      coe ::
        forall a. (Columnar' f a -> Columnar' g a -> m (Columnar' h a))
        -> Columnar f a -> Columnar g a -> m (Columnar h a)
      coe op fa ga = unColumnar' <$> op (Columnar' fa) (Columnar' ga)

  tblSkeleton ::
    TableSkeleton ManTable
  tblSkeleton =
    MkManTable
      Ignored
      Ignored
      Ignored
      Ignored
      Ignored
      Ignored

newtype FromLRGeneric (table :: (a -> Type) -> Type) (f :: a -> Type) = FromLRGeneric (table f)

type HasLRBeamFields table f g h =
  ( Generic (table f)
  , Generic (table g)
  , Generic (table h)
  , TableConstraint table
  )

class IsLRBeamField (f :: a -> Type) (x :: Type) where
  reveal :: x -> f (Reveal f x)
  hide :: f (Reveal f x) -> x

instance (f ~ g, Reveal f (g y) ~ y) => IsLRBeamField (f :: a -> Type) (g y :: Type) where
  reveal x = x
  hide x = x

type family Reveal (f :: a -> Type) (x :: Type) where
  Reveal f (f x) = x

gZipBeamFieldsM ::
  forall table f g h m.
  (HasLRBeamFields table f g h, Applicative m)
  => (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
  -> table f
  -> table g
  -> m (table h)
gZipBeamFieldsM combine tf tg =
  let
    rtf :: Rep I (table f)
    rtf = from tf

    rtg :: Rep I (table g)
    rtg = from tg

    rtf' :: Rep (Columnar' f) (table I)
    rtf' = scIffI rtf

    rtg' :: Rep (Columnar' g) (table I)
    rtg' = scIffI rtg

    rth' :: m (Rep (Columnar' h) (table I))
    rth' = R.zipWithM combine rtf' rtg'

    rth :: m (Rep I (table h))
    rth = scfIIf <$> rth'
  in
    to <$> rth

{-
czipWithM' ::
  (Applicative m, Constraints a c
  => Proxy c
  -> (forall x. c x => f x -> g x -> m (h x))
  -> Rep f (table f') -> Rep g (table g') -> m (Rep h (table h'))
czipWithM' f (Rep a) (Rep b) =
  Rep <$> Prelude.sequenceA (V.zipWith f a b)
-}
