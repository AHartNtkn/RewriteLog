{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}

module AddRelSpec (spec) where

import Test.Hspec
import Control.Monad.Free (Free(..))
import RelExp (RelExp(..), mkOr, mkComp, run, var)
import SExpF (SExpF(..), atom, cons, ppSExp)
import Data.Fix (Fix(..))

-- | Convert a natural number to Peano representation
toPeano :: Int -> Free SExpF Int
toPeano 0 = atom "z"
toPeano n = cons (atom "s") (toPeano (n-1))

-- | Addition relation for Peano arithmetic
addRel :: RelExp SExpF
addRel = mkOr
  [ -- Rule: (0 + X) ~~> X
    Rw (cons (atom "z") (var 0)) (var 0)
  , -- Rule: (s X) + Y ~~> s (X + Y)
    mkComp
      [ Rw (cons (cons (atom "s") (var 0)) (var 1))
           (cons (var 0) (var 1))
      , addRel
      , Rw (var 0) (cons (atom "s") (var 0))
      ]
  ]

-- | Addition relation for Peano arithmetic, backwards
addRelDuel :: RelExp SExpF
addRelDuel = mkOr
  [ -- Rule: X ~~> (0 + X)
    Rw (var 0) (cons (atom "z") (var 0))
  , -- Rule: s X ~~> find Y,Z where X = s(Y) and result = (s Z + Y)
    mkComp
      [ Rw (cons (atom "s") (var 0)) (var 0)  -- Match s X and extract X
      , addRelDuel                             -- Recursively find pairs for X
      , Rw (cons (var 0) (var 1))             -- For pair (A,B), make (s A, B)
           (cons (cons (atom "s") (var 0)) (var 1))
      ]
  ]

spec :: Spec
spec = do
  describe "Addition Relation" $ do
    it "computes 3 + 2 = 5" $ do
      let input = cons (toPeano 3) (toPeano 2)
          expected = toPeano 5
          results = run (Comp (Rw input input) addRel)
      putStrLn $ "Input: " ++ ppSExp input
      putStrLn $ "Expected: " ++ ppSExp expected
      results `shouldNotBe` []
      head results `shouldBe` Rw input expected

    it "generates all pairs summing to 5" $ do
      let target = toPeano 5
          results = run (Comp (Rw target target) addRelDuel)
          expected = [cons (toPeano x) (toPeano (5-x)) | x <- [0..5]]
      
      -- Each result should be a rewrite rule with target on left
      -- and a pair of numbers on right that sum to 5
      let pairs = [term | Rw _ term <- results]
      
      -- Print the actual and expected results in a readable format
      putStrLn "Expected pairs:"
      mapM_ (putStrLn . ("  " ++) . ppSExp) expected
      putStrLn "Actual pairs:"
      mapM_ (putStrLn . ("  " ++) . ppSExp) pairs
      
      pairs `shouldMatchList` expected
