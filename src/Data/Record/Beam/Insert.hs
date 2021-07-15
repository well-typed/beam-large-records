{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Record.Beam.Insert (
    insertValues
  ) where

import Data.Functor.Identity
import Database.Beam.Backend.SQL
import Database.Beam.Schema.Tables hiding (FieldsFulfillConstraint)
import Database.Beam.Query hiding (insertValues)

import Data.Record.Beam.Constraints

-- | Variation on 'Database.Beam.Query.insertValues' that uses LR generics
insertValues ::
     ( BeamSqlBackend be
     , Beamable table
     , FieldsFulfillConstraint (BeamSqlBackendCanSerialize be) table
     )
  => [table Identity]
  -> SqlInsertValues be (table (QExpr be s))
insertValues xs = insertExpressions (map valTable xs)

{-------------------------------------------------------------------------------
  Variation on 'SqlValable' does that not depend on GHC generics
-------------------------------------------------------------------------------}

valTable :: forall table be s.
     ( BeamSqlBackend be
     , FieldsFulfillConstraint (BeamSqlBackendCanSerialize be) table
     , Beamable table
     )
  => table Identity -> table (QExpr be s)
valTable tbl =
    changeBeamRep aux fields
  where
    fields :: table (WithConstraint (BeamSqlBackendCanSerialize be))
    fields = gwithConstrainedFields tbl

    aux :: Columnar' (WithConstraint (BeamSqlBackendCanSerialize be)) a
        -> Columnar' (QExpr be s) a
    aux (Columnar' (WithConstraint x)) = Columnar' $
        QExpr $ pure (valueE $ sqlValueSyntax x)
