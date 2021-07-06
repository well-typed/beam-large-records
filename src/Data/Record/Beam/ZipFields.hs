{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Data.Record.Beam.ZipFields (gzipBeamFieldsM, ZipBeamFieldsI) where

import Data.Kind
import Data.Proxy
import Data.Record.Generic
import Data.Record.Generic.Transform
import Database.Beam.Schema.Tables

import qualified Data.Record.Generic.Rep as Rep

import Data.Record.Beam.Internal
import Data.Record.Beam.Interpretation

-- | Generic implementation of the 'Beamable' 'zipBeamFieldsM' class method
gzipBeamFieldsM ::
     ( Applicative m
       -- Constraints required to do a generic transform
     , Generic (table f)
     , Generic (table g)
     , Generic (table h)
     , Generic (table Uninterpreted)
     , Constraints (table Uninterpreted) ZipBeamFieldsI
     , HasNormalForm (BeamInterpretation f) (table f) (table Uninterpreted)
     , HasNormalForm (BeamInterpretation g) (table g) (table Uninterpreted)
     , HasNormalForm (BeamInterpretation h) (table h) (table Uninterpreted)
     )
  => (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
  -> table f -> table g -> m (table h)
gzipBeamFieldsM f x y =
    fmap (to . denormalize1 (Proxy @BeamInterpretation)) $
      Rep.czipWithM
        (Proxy @ZipBeamFieldsI)
        (zipBeamFieldsI f)
        (normalize1 (Proxy @BeamInterpretation) (from x))
        (normalize1 (Proxy @BeamInterpretation) (from y))

{-------------------------------------------------------------------------------
  Internal: cases for 'gzipBeamFieldsM'
-------------------------------------------------------------------------------}

class ZipBeamFieldsI (a :: Type) where
  zipBeamFieldsI ::
       Applicative m
    => (forall x. Columnar' f x -> Columnar' g x -> m (Columnar' h x))
    -> Interpret (BeamInterpretation f) a
    -> Interpret (BeamInterpretation g) a
    -> m (Interpret (BeamInterpretation h) a)

instance ZipBeamFieldsI (Uninterpreted x) where
  zipBeamFieldsI f = liftInterpretedA2 $ liftColumnarA2 (Proxy @x) f

instance Beamable table => ZipBeamFieldsI (table Uninterpreted) where
  zipBeamFieldsI f = liftInterpretedA2 $ zipBeamFieldsM f

instance Beamable table => ZipBeamFieldsI (table (Nullable Uninterpreted)) where
  zipBeamFieldsI f = liftInterpretedA2 $ zipBeamFieldsM (liftNullableA2 f)