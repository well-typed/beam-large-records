{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}

module Data.Record.Beam.ZipTables (gzipTables, ZipTablesI) where

import Data.Proxy
import Data.Record.Generic
import Data.Record.Generic.Transform
import Database.Beam.Schema.Tables

import qualified Data.Record.Generic.Rep as Rep

-- | Generic implementation of the 'Database' 'zipTables' class method
gzipTables ::
     ( Applicative m
     , Generic (db f)
     , Generic (db g)
     , Generic (db h)
     , Generic (db Uninterpreted)
     , Constraints (db Uninterpreted) ZipTablesI
     , HasNormalForm (DefaultInterpretation f) (db f) (db Uninterpreted)
     , HasNormalForm (DefaultInterpretation g) (db g) (db Uninterpreted)
     , HasNormalForm (DefaultInterpretation h) (db h) (db Uninterpreted)
     )
  => Proxy be
  -> (forall tbl. (IsDatabaseEntity be tbl, DatabaseEntityRegularRequirements be tbl) => f tbl -> g tbl -> m (h tbl))
  -> db f -> db g -> m (db h)
gzipTables p f x y =
    fmap (to . denormalize1 (Proxy @DefaultInterpretation)) $
      Rep.czipWithM
        (Proxy @ZipTablesI)
        (zipTablesI p f)
        (normalize1 (Proxy @DefaultInterpretation) (from x))
        (normalize1 (Proxy @DefaultInterpretation) (from y))

{-------------------------------------------------------------------------------
  Internal: cases for 'gzipTables'
-------------------------------------------------------------------------------}

class ZipTablesI a where
  zipTablesI ::
        Applicative m
     => Proxy be
     -> (forall tbl. (IsDatabaseEntity be tbl, DatabaseEntityRegularRequirements be tbl) => f tbl -> g tbl -> m (h tbl))
     -> Interpret (DefaultInterpretation f) a
     -> Interpret (DefaultInterpretation g) a
     -> m (Interpret (DefaultInterpretation h) a)

instance Table tbl => ZipTablesI (Uninterpreted (TableEntity tbl)) where
  zipTablesI _ = liftInterpretedA2

instance Beamable tbl => ZipTablesI (Uninterpreted (ViewEntity tbl)) where
  zipTablesI _ = liftInterpretedA2

instance ZipTablesI (Uninterpreted (DomainTypeEntity a)) where
  zipTablesI _ = liftInterpretedA2