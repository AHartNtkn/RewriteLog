{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}

module AddRelSpec (spec) where

import Test.Hspec
import SExpF
import RelExp (RelExp(..), var, rw, mkOr, mkComp, run, dual)
import Control.Monad.Free (Free(..))
import Constraint (EmptyConstraint(..))

-- | Convert a natural number to Peano representation
toPeano :: Int -> Free SExpF Int
toPeano 0 = atom "z"
toPeano n = cons (atom "s") (toPeano (n-1))

-- | Addition relation for Peano arithmetic
addRel :: RelExp SExpF EmptyConstraint
addRel = mkOr
  [ -- Rule: (0 + X) ~~> X
    rw (cons (atom "z") (var 0)) (var 0)
  , -- Rule: (s X) + Y ~~> s (X + Y)
    mkComp
      [ rw (cons (cons (atom "s") (var 0)) (var 1))
           (cons (var 0) (var 1))
      , addRel
      , rw (var 0) (cons (atom "s") (var 0))
      ]
  ]

spec :: Spec
spec = do
  describe "Addition Relation" $ do
    it "computes 3 + 2 = 5" $ do
      let input = cons (toPeano 3) (toPeano 2)
          expected = toPeano 5
          results = run (Comp (rw input input) addRel)
      putStrLn $ "Input: " ++ ppSExp input
      putStrLn $ "Expected: " ++ ppSExp expected
      results `shouldNotBe` []
      head results `shouldBe` rw input expected

    it "generates all pairs summing to 5 by running addition backwards" $ do
      let target = toPeano 5
          results = run (Comp (rw target target) (dual addRel))
          expected = [cons (toPeano x) (toPeano (5-x)) | x <- [0..5]]
      
      -- Each result should be a rewrite rule with target on left
      -- and a pair of numbers on right that sum to 5
      let pairs = [term | Rw _ term _ <- results]
      
      -- Print the actual and expected results in a readable format
      putStrLn "Expected pairs:"
      mapM_ (putStrLn . ("  " ++) . ppSExp) expected
      putStrLn "Actual pairs:"
      mapM_ (putStrLn . ("  " ++) . ppSExp) pairs
      
      pairs `shouldMatchList` expected
