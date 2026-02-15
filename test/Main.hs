module Main ( main ) where

import Test.Tasty
import Test.Tasty.HUnit
import Sefer.Expr

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Typechecker tests"
  [ testCase "2 + 3 = 5" $
    2 + 3 @?= 5
  ]
