{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Record.Beam.Constraints (
    FieldsFulfillConstraint
  , gwithConstraints
  , gwithConstrainedFields
  , WithConstraintsI
  , WithTblConstraints
  , IsPrimaryKey
  ) where

import Data.Functor.Identity
import Data.Kind
import Data.Record.Generic
import Data.Record.Generic.Transform
import Database.Beam.Schema.Tables hiding (FieldsFulfillConstraint)

import qualified Data.Record.Generic.Rep as Rep
import qualified Database.Beam.Schema.Tables as Beam

import Data.Record.Beam.Interpretation

type FieldsFulfillConstraint c tbl = (
    Generic (tbl (HasConstraint c))
  , Generic (tbl Uninterpreted)
  , Constraints (tbl Uninterpreted) (WithConstraintsI c)
  , HasNormalForm (BeamInterpretation (HasConstraint c)) (tbl (HasConstraint c)) (tbl Uninterpreted)
  )

gwithConstraints :: forall c tbl.
     FieldsFulfillConstraint c tbl
  => tbl (HasConstraint c)
gwithConstraints =
    to . denormalize1 (Proxy @BeamInterpretation) $
      Rep.cpure (Proxy @(WithConstraintsI c)) withConstraintsI

gwithConstrainedFields :: forall tbl c.
     (FieldsFulfillConstraint c tbl, Beamable tbl)
  => tbl Identity -> tbl (WithConstraint c)
gwithConstrainedFields tbl = runIdentity $
    zipBeamFieldsM aux tbl gwithConstraints
  where
    aux :: Columnar' Identity a -> Columnar' (HasConstraint c) a -> Identity (Columnar' (WithConstraint c) a)
    aux (Columnar' x) (Columnar' HasConstraint) = Identity $
        Columnar' (WithConstraint x)

{-------------------------------------------------------------------------------
  Internal: cases for gwithConstraints
-------------------------------------------------------------------------------}

class WithConstraintsI c a where
  withConstraintsI :: Interpret (BeamInterpretation (HasConstraint c)) a

instance c a => WithConstraintsI c (Uninterpreted a) where
  withConstraintsI = Interpret HasConstraint

instance ( isPrimaryKey ~ ComputeIsPrimaryKey (tbl Uninterpreted)
         , WithTblConstraints c isPrimaryKey (tbl Uninterpreted)
         ) => WithConstraintsI c (tbl Uninterpreted) where
  withConstraintsI = withTblConstraints (Proxy @isPrimaryKey)

instance ( isPrimaryKey ~ ComputeIsPrimaryKey (tbl (Nullable Uninterpreted))
         , WithTblConstraints c isPrimaryKey (tbl (Nullable Uninterpreted))
         ) => WithConstraintsI c (tbl (Nullable Uninterpreted)) where
  withConstraintsI = withTblConstraints (Proxy @isPrimaryKey)

{-------------------------------------------------------------------------------
  Internal: subcases of 'withContraintsI' for tables

  Primary keys are not defined as large records, and use standard GHC generics,
  so we want to use a different approach there then for the tables themselves.
-------------------------------------------------------------------------------}

data IsPrimaryKey = IsPrimaryKey | NotPrimaryKey

type family ComputeIsPrimaryKey (tbl :: Type) :: IsPrimaryKey where
   ComputeIsPrimaryKey (PrimaryKey tbl f) = 'IsPrimaryKey
   ComputeIsPrimaryKey _                  = 'NotPrimaryKey

class WithTblConstraints c (isPrimaryKey :: IsPrimaryKey) a where
  withTblConstraints :: Proxy isPrimaryKey -> Interpret (BeamInterpretation (HasConstraint c)) a

instance ( -- Constraints from 'gwithConstraints'
           Generic (tbl (HasConstraint c))
         , Generic (tbl Uninterpreted)
         , Constraints (tbl Uninterpreted) (WithConstraintsI c)
         , HasNormalForm (BeamInterpretation (HasConstraint c)) (tbl (HasConstraint c)) (tbl Uninterpreted)
         ) => WithTblConstraints c 'NotPrimaryKey (tbl Uninterpreted) where
  withTblConstraints _ = Interpret $ gwithConstraints

instance ( -- Constraints from 'withConstraints'
           Beamable tbl
         , Beam.FieldsFulfillConstraint c tbl
         ) => WithTblConstraints c 'IsPrimaryKey (tbl Uninterpreted) where
  withTblConstraints _ = Interpret $ withConstraints

instance ( -- Constraints from 'withNullableConstraints'
           Beamable tbl
         , Beam.FieldsFulfillConstraintNullable c tbl
         ) => WithTblConstraints c 'IsPrimaryKey (tbl (Nullable Uninterpreted)) where
  withTblConstraints _ = Interpret $ withNullableConstraints
