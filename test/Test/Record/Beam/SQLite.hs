{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -F -pgmF=record-dot-preprocessor #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Record.Beam.SQLite (tests) where

import Control.Exception
import Data.Int
import Data.Record.Generic
import Data.Record.TH
import Data.Text (Text)
import Database.Beam hiding (Generic)
import Database.Beam.Schema.Tables
import Database.Beam.Sqlite
import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Record.Beam as LR
import qualified Database.SQLite.Simple as SQLite
import qualified GHC.Generics as GHC

import Test.Record.Beam.Util.Orphans ()

{-------------------------------------------------------------------------------
  General comment: the beam architecture does not introduce classes for its
  various concepts, but instead uses GHC generics rather directly. At the
  moment, beam-large-records follows the same strategy, but insisting on LR
  generics instead of GHC generics. This means that we have a choice: _either_
  use GHC generics, _or_ use LR generics; we cannot mix both in one system, with
  some tables declared as large tables and others being regular tables. If we
  wanted to change this, we'd have to introduce indirection through a bunch of
  additional classes; this may well be worth doing, but it's questionable
  whether it should be done in beam-large-records; ideally, this would be done
  upstream in beam-core itself.
-------------------------------------------------------------------------------}

{-------------------------------------------------------------------------------
  Large record example
-------------------------------------------------------------------------------}

largeRecord defaultPureScript $ [d|
      data LargeTable (f :: * -> *) = MkLargeTable {
            largeTableId    :: Columnar f Int32
          , largeTableField :: Columnar f Text
          }
        deriving (Show, Eq)
    |]

endOfBindingGroup

large1, large2 :: LargeTable Identity
large1 = [lr| MkLargeTable |] 1 "hi"
large2 = [lr| MkLargeTable |] 2 "ho"

instance Beamable LargeTable where
  zipBeamFieldsM = LR.gzipBeamFieldsM
  tblSkeleton    = LR.gtblSkeleton

instance Table LargeTable where
  newtype PrimaryKey LargeTable f = LargeTableKey (Columnar f Int32)
    deriving stock (GHC.Generic)
    deriving anyclass (Beamable)

  primaryKey tbl = LargeTableKey tbl.largeTableId

{-------------------------------------------------------------------------------
  The full database
-------------------------------------------------------------------------------}

-- TODO: Make this a large record too
largeRecord defaultPureScript [d|
    data ExampleDb (f :: * -> *) = MkExampleDb {
          exampleDbLargeTable  :: f (TableEntity LargeTable)
        }
      deriving (Show)
  |]

instance Database be ExampleDb where
  zipTables = LR.gzipTables

-- TODO: Using the /standard/ 'defaultDbSettings' but where tables are large
-- does not work.
exampleDb :: DatabaseSettings be ExampleDb
exampleDb = LR.autoDbSettings

{-------------------------------------------------------------------------------
  Auxiliary
-------------------------------------------------------------------------------}

runInMemory :: (SQLite.Connection -> SqliteM a) -> IO a
runInMemory f =
    bracket (SQLite.open ":memory:") SQLite.close $ \conn ->
      runBeamSqlite conn $ f conn

{-------------------------------------------------------------------------------
  Oooof. Here's where things really get nasty.
-------------------------------------------------------------------------------}

-- Uses the backend to make this instance more concrete than the completely
-- polymorphic instance in beam-core 🤦
--
-- (Alternative would be to define this instance for specific tables instead.)
instance {-# OVERLAPPING #-}
     ( Generic (tbl Identity)
     , Constraints (tbl Identity) (FromBackendRow Sqlite)
     ) => FromBackendRow Sqlite (tbl Identity) where
  fromBackendRow = LR.gfromBackendRow
  valuesNeeded   = LR.gvaluesNeeded

{-------------------------------------------------------------------------------
  Tests proper
-------------------------------------------------------------------------------}

tests :: TestTree
tests = testGroup "Test.Record.Beam.SQLite" [
      testCase "insert_select" test_insert_select
    ]

test_insert_select :: Assertion
test_insert_select = runInMemory $ \conn -> do
    liftIO $ SQLite.execute_ conn $
      "CREATE TABLE db_large_table (table_id INT PRIMARY KEY NOT NULL, table_field VARCHAR NOT NULL);"

    runInsert $
      insert exampleDb.exampleDbLargeTable $ LR.insertValues [
          large1
        , large2
        ]

    allLarge <- runSelectReturningList $ select $
      orderBy_ (\x -> asc_ (x.largeTableId)) $ all_ exampleDb.exampleDbLargeTable
    liftIO $ assertEqual "allLarge" allLarge [large1, large2]
