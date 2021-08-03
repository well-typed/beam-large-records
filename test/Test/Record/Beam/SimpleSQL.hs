{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -F -pgmF=record-dot-preprocessor #-}

-- | Simple but complete example that does an SQL INSERT and SELECT
module Test.Record.Beam.SimpleSQL (tests) where

import Data.Int
import Data.Record.TH
import Data.Text (Text)
import Database.Beam
import Test.Tasty
import Test.Tasty.HUnit

import qualified Database.SQLite.Simple as SQLite
import qualified GHC.Generics           as GHC

import Data.Record.Beam ()

import Test.Record.Beam.Util.SQLite

{-------------------------------------------------------------------------------
  Large record example
-------------------------------------------------------------------------------}

largeRecord defaultPureScript $ [d|
      data LargeTable (f :: * -> *) = MkLargeTable {
            largeTableId    :: Columnar f Int32
          , largeTableField :: Columnar f Text
          }
        deriving stock (Show, Eq)
        deriving anyclass (Beamable)
    |]

endOfBindingGroup

large1, large2 :: LargeTable Identity
large1 = [lr| MkLargeTable |] 1 "hi"
large2 = [lr| MkLargeTable |] 2 "ho"

instance Table LargeTable where
  newtype PrimaryKey LargeTable f = LargeTableKey (Columnar f Int32)
    deriving stock (GHC.Generic)
    deriving anyclass (Beamable)

  primaryKey tbl = LargeTableKey tbl.largeTableId

{-------------------------------------------------------------------------------
  The full database
-------------------------------------------------------------------------------}

largeRecord defaultPureScript [d|
    data ExampleDb (f :: * -> *) = MkExampleDb {
          exampleDbLargeTable  :: f (TableEntity LargeTable)
        }
      deriving (Show)
  |]

instance Database be ExampleDb

exampleDb :: DatabaseSettings be ExampleDb
exampleDb = defaultDbSettings

{-------------------------------------------------------------------------------
  Tests proper
-------------------------------------------------------------------------------}

tests :: TestTree
tests = testGroup "Test.Record.Beam.SimpleSQL" [
      testCase "insert_select" test_insert_select
    ]

test_insert_select :: Assertion
test_insert_select = runInMemory $ \conn -> do
    liftIO $ SQLite.execute_ conn $
      "CREATE TABLE db_large_table (table_id INT PRIMARY KEY NOT NULL, table_field VARCHAR NOT NULL);"

    runInsert $
      insert exampleDb.exampleDbLargeTable $ insertValues [
          large1
        , large2
        ]

    allLarge <- runSelectReturningList $ select $
      orderBy_ (\x -> asc_ (x.largeTableId)) $ all_ exampleDb.exampleDbLargeTable
    liftIO $ assertEqual "allLarge" allLarge [large1, large2]

