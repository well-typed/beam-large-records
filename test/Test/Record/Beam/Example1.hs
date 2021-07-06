{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -F -pgmF=record-dot-preprocessor #-}

module Test.Record.Beam.Example1 (tests) where

import Data.Functor.Identity
import Data.Kind
import Data.Record.TH
import Database.Beam.Schema.Tables
import Test.Tasty
import Test.Tasty.HUnit

import qualified GHC.Generics as GHC

import Data.Record.Beam.Internal
import Data.Record.Beam

{-------------------------------------------------------------------------------
  Example proper
-------------------------------------------------------------------------------}

largeRecord defaultPureScript [d|
    data TableA (f :: Type -> Type) = TableA {
          taPrim  :: PrimaryKey TableA f
        , taField :: Columnar f Bool
        , taMixin :: TableB f
        }
      deriving (Show, Eq)

    data TableB (f :: Type -> Type) = TableB {
          tbField :: Columnar f Char
        }
      deriving (Show, Eq)
  |]

endOfBindingGroup

instance Table TableA where
  data PrimaryKey TableA f = PrimA (Columnar f Int)
    deriving stock (GHC.Generic)
    deriving anyclass (Beamable)

  primaryKey ta = ta.taPrim

deriving instance Show (Columnar f Int) => Show (PrimaryKey TableA f)
deriving instance Eq   (Columnar f Int) => Eq   (PrimaryKey TableA f)

instance Beamable TableA where
  zipBeamFieldsM = gzipBeamFieldsM
  tblSkeleton    = gtblSkeleton

instance Beamable TableB where
  zipBeamFieldsM = gzipBeamFieldsM
  tblSkeleton    = gtblSkeleton

{-------------------------------------------------------------------------------
  Sanity check that the functions work
-------------------------------------------------------------------------------}

tests :: TestTree
tests = testGroup "Test.Record.Beam.Example1" [
      testCase "zipBeamFields" test_zipBeamFields
    ]

test_zipBeamFields :: Assertion
test_zipBeamFields =
    assertEqual "" (runIdentity (zipBeamFieldsM apply fnA argA)) resA
  where
    apply :: forall a.
         Columnar' EndoFn a
      -> Columnar' Identity a
      -> Identity (Columnar' Identity a)
    apply = unliftColumnarA2 $ \(EndoFn f) x -> Identity (f x)

    fnA :: TableA EndoFn
    fnA = [lr| TableA {
          taPrim  = PrimA (EndoFn succ)
        , taField = EndoFn not
        , taMixin = fnB
        } |]

    fnB :: TableB EndoFn
    fnB = [lr| TableB {
          tbField = EndoFn pred
        } |]

    argA :: TableA Identity
    argA = [lr| TableA {
          taPrim  = PrimA 5
        , taField = True
        , taMixin = argB
        } |]

    argB :: TableB Identity
    argB = [lr| TableB {
          tbField = 'y'
        } |]

    resA :: TableA Identity
    resA = [lr| TableA {
          taPrim  = PrimA 6
        , taField = False
        , taMixin = resB
        } |]

    resB :: TableB Identity
    resB = [lr| TableB {
          tbField = 'x'
        } |]

newtype EndoFn a = EndoFn (a -> a)

