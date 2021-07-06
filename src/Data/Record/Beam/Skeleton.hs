{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications  #-}

module Data.Record.Beam.Skeleton (gtblSkeleton, TblSkeletonI) where

import Data.Proxy
import Data.Record.Generic
import Data.Record.Generic.Transform
import Database.Beam.Schema.Tables

import qualified Data.Record.Generic.Rep as Rep

import Data.Record.Beam.Internal
import Data.Record.Beam.Interpretation

-- | Generic implementation of the 'Beamable' 'tblSkeleton' class method
gtblSkeleton ::
     ( Generic (table Ignored)
     , Generic (table Uninterpreted)
     , Constraints (table Uninterpreted) TblSkeletonI
     , HasNormalForm (BeamInterpretation Ignored) (table Ignored) (table Uninterpreted)
     )
  => TableSkeleton table
gtblSkeleton =
    to . denormalize1 (Proxy @BeamInterpretation) $
      Rep.cpure (Proxy @TblSkeletonI) tblSkeletonI

{-------------------------------------------------------------------------------
  Internal: cases for 'gtblSkeleton'
-------------------------------------------------------------------------------}

class TblSkeletonI a where
  tblSkeletonI :: Interpret (BeamInterpretation Ignored) a

instance TblSkeletonI (Uninterpreted x) where
  tblSkeletonI = Interpret $ Ignored

instance Beamable table => TblSkeletonI (table Uninterpreted) where
  tblSkeletonI = Interpret $ tblSkeleton

instance Beamable table => TblSkeletonI (table (Nullable Uninterpreted)) where
  tblSkeletonI = Interpret $ mkNullable tblSkeleton
    where
      mkNullable :: Beamable table => table Ignored -> table (Nullable Ignored)
      mkNullable = mapBeamFields $ const (Columnar' Ignored)

