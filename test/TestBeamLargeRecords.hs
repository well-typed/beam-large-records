module Main (main) where

import Test.Tasty

import qualified Test.Record.Beam.Example1
import qualified Test.Record.Beam.Example2
import qualified Test.Record.Beam.SQLite

main :: IO ()
main = defaultMain $ testGroup "test-beam-large-records" [
      Test.Record.Beam.Example1.tests
    , Test.Record.Beam.Example2.tests
    , Test.Record.Beam.SQLite.tests
    ]