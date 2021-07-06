{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Utility functions for working with beam
--
-- These are not exported from Data.Record.Beam, and should be considered
-- internal use only.
module Data.Record.Beam.Internal (
    -- * Working with Columnar'
    getColumnar'
  , liftColumnarA2
  , liftNullableA2
  , unliftColumnarA2
    -- * Working with 'Beamable'
  , mapBeamFieldsM
  , mapBeamFields
    -- * Beam internal functions
  , unCamelCaseSel
  , SubTableStrategy(..)
  , ChooseSubTableStrategy
  , CheckNullable
  ) where

import Data.Bifunctor
import Data.Char (isUpper, toLower)
import Data.Coerce (coerce)
import Data.Functor.Identity
import Data.Kind
import Data.Proxy
import Data.Text (Text)
import Database.Beam.Schema.Tables
import GHC.TypeLits

import qualified Data.Text as T

{-------------------------------------------------------------------------------
  Working with Columnar'
-------------------------------------------------------------------------------}

getColumnar' :: Columnar' f a -> Columnar f a
getColumnar' (Columnar' x) = x

liftColumnarA2 ::
     Functor m
  => Proxy x
  -> (Columnar' f x -> Columnar' g x -> m (Columnar' h x))
  -> (Columnar  f x -> Columnar  g x -> m (Columnar  h x))
liftColumnarA2 _ f fx gx = getColumnar' <$> f (Columnar' fx) (Columnar' gx)

liftNullableA2 ::
     Functor m
  => (forall x. Columnar'           f  x -> Columnar'           g  x -> m (Columnar'           h  x))
  -> (forall x. Columnar' (Nullable f) x -> Columnar' (Nullable g) x -> m (Columnar' (Nullable h) x))
liftNullableA2 f x y = toNullable <$> f (fromNullable x) (fromNullable y)
  where
    toNullable :: Columnar' w (Maybe a) -> Columnar' (Nullable w) a
    toNullable = coerce

    fromNullable :: Columnar' (Nullable w) a -> Columnar' w (Maybe a)
    fromNullable = coerce

unliftColumnarA2 ::
     Functor m
  => (Columnar  f x -> Columnar  g x -> m (Columnar  h x))
  -> (Columnar' f x -> Columnar' g x -> m (Columnar' h x))
unliftColumnarA2 f fx gx = Columnar' <$> f (getColumnar' fx) (getColumnar' gx)

{-------------------------------------------------------------------------------
  Working with 'Beamable'
-------------------------------------------------------------------------------}

mapBeamFieldsM ::
     (Applicative m, Beamable table)
  => (forall x. Columnar' f x -> m (Columnar' g x))
  -> table f -> m (table g)
mapBeamFieldsM f x = zipBeamFieldsM (const f) x x

mapBeamFields ::
     Beamable table
  => (forall x. Columnar' f x -> Columnar' g x)
  -> table f -> table g
mapBeamFields f = runIdentity . mapBeamFieldsM (Identity . f)

{-------------------------------------------------------------------------------
  Beam-internal functions

  These are straight copies of functions defined in beam but not exported.
-------------------------------------------------------------------------------}

unCamelCase :: T.Text -> [T.Text]
unCamelCase "" = []
unCamelCase s
    | (comp, next) <- T.break isUpper s, not (T.null comp) =
          let next' = maybe mempty (uncurry T.cons . first toLower) (T.uncons next)
          in T.toLower comp:unCamelCase next'
    | otherwise =
          let (comp, next) = T.span isUpper s
              next' = maybe mempty (uncurry T.cons . first toLower) (T.uncons next)
          in T.toLower comp:unCamelCase next'

unCamelCaseSel :: Text -> Text
unCamelCaseSel original =
  let symbolLeft = T.dropWhile (=='_') original
  in if T.null symbolLeft
     then original
     else if T.any (=='_') symbolLeft
          then symbolLeft
          else case unCamelCase symbolLeft of
                 [] -> symbolLeft
                 [xs] -> xs
                 _:xs -> T.intercalate "_" xs

data SubTableStrategy
  = PrimaryKeyStrategy
  | BeamableStrategy
  | RecursiveKeyStrategy

type family ChooseSubTableStrategy (tbl :: (Type -> Type) -> Type) (sub :: (Type -> Type) -> Type) :: SubTableStrategy where
  ChooseSubTableStrategy tbl (PrimaryKey tbl) = 'RecursiveKeyStrategy
  ChooseSubTableStrategy tbl (PrimaryKey rel) = 'PrimaryKeyStrategy
  ChooseSubTableStrategy tbl sub = 'BeamableStrategy

type family CheckNullable (f :: Type -> Type) :: Constraint where
  CheckNullable (Nullable f) = ()
  CheckNullable f = TypeError ('Text "Recursive references without Nullable constraint form an infinite loop." ':$$:
                               'Text "Hint: Only embed nullable 'PrimaryKey tbl' within the definition of 'tbl'." ':$$:
                               'Text "      For example, replace 'PrimaryKey tbl f' with 'PrimaryKey tbl (Nullable f)'")
