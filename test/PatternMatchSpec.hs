{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module PatternMatchSpec (spec) where

import Test.Hspec
import RelExp
import Control.Monad.Free (Free(..))
import qualified Data.Map as Map
import Data.Functor.Classes (Show1(..), Eq1(..))

-- Single functor type that can represent all operations
data Term a = F a a | G a | R a a | S a | K a
  deriving (Show, Eq, Functor, Foldable, Traversable)

instance Show1 Term where
  liftShowsPrec sp _ d (F x y) = showParen (d > 10) $
    showString "F " . sp 11 x . showChar ' ' . sp 11 y
  liftShowsPrec sp _ d (G x) = showParen (d > 10) $
    showString "G " . sp 11 x
  liftShowsPrec sp _ d (R x y) = showParen (d > 10) $
    showString "R " . sp 11 x . showChar ' ' . sp 11 y
  liftShowsPrec sp _ d (S x) = showParen (d > 10) $
    showString "S " . sp 11 x
  liftShowsPrec sp _ d (K x) = showParen (d > 10) $
    showString "K " . sp 11 x

instance Eq1 Term where
  liftEq eq (F x1 y1) (F x2 y2) = eq x1 x2 && eq y1 y2
  liftEq eq (G x1) (G x2) = eq x1 x2
  liftEq eq (R x1 y1) (R x2 y2) = eq x1 x2 && eq y1 y2
  liftEq eq (S x1) (S x2) = eq x1 x2
  liftEq eq (K x1) (K x2) = eq x1 x2
  liftEq _ _ _ = False

spec :: Spec
spec = do
  describe "Pattern Matching" $ do
    it "matches a variable with any term" $ do
      let t1 = var 0
      let t2 = Free $ G (var 1)
      match t1 t2 `shouldBe` Just (Map.singleton 0 (Free $ G (var 1)))

    it "matches identical constructors" $ do
      let t1 = Free $ F (var 0) (var 1)
      let t2 = Free $ F (Free $ G (var 2)) (var 3)
      case match t1 t2 of
        Nothing -> expectationFailure "Expected a match but got Nothing"
        Just subst -> applySubst subst t1 `shouldBe` applySubst subst t2

    it "matches terms with repeated variables" $ do
      let t1 = Free $ F (var 0) (var 0)  -- F x x
      let t2 = Free $ F (var 1) (var 1)  -- F y y
      let t3 = Free $ F (var 1) (var 2)  -- F y z
      
      -- For identical terms with repeated variables
      case match t1 t2 of
        Nothing -> expectationFailure "Expected a match but got Nothing"
        Just subst1 -> applySubst subst1 t1 `shouldBe` applySubst subst1 t2
      
      -- For terms with different variables that unify
      case match t1 t3 of
        Nothing -> expectationFailure "Expected a match but got Nothing"
        Just subst2 -> applySubst subst2 t1 `shouldBe` applySubst subst2 t3

    it "matches nested terms with repeated variables" $ do
      let t1 = Free $ F (var 0) (Free $ G (var 0))  -- F x (G x)
      let t2 = Free $ F (var 1) (Free $ G (var 1))  -- F y (G y)
      case match t1 t2 of
        Nothing -> expectationFailure "Expected a match but got Nothing"
        Just subst -> applySubst subst t1 `shouldBe` applySubst subst t2

    it "fails on different constructors" $ do
      let t1 = Free $ F (var 0) (var 1)
      let t2 = Free $ G (var 2)
      match t1 t2 `shouldBe` Nothing

    it "matches constructor with variable" $ do
      let t1 = Free $ F (var 0) (var 1)
      let t2 = var 2
      case match t1 t2 of
        Nothing -> expectationFailure "Expected a match but got none"
        Just subst -> applySubst subst t2 `shouldBe` applySubst subst t1

  describe "Variable Normalization" $ do
    it "normalizes variables in a term" $ do
      let term = Free $ F (var 5) (Free $ G (var 3))
      let expected = Free $ F (var 0) (Free $ G (var 1))
      normalizeVars term `shouldBe` expected

    it "preserves repeated variables when normalizing" $ do
      let term = Free $ F (var 5) (var 5)  -- F x x
      let expected = Free $ F (var 0) (var 0)  -- F 0 0
      normalizeVars term `shouldBe` expected

    it "handles empty terms" $ do
      let term = Pure 42 :: Free Term Int
      let expected = Pure 0 :: Free Term Int
      normalizeVars term `shouldBe` expected

  describe "Pattern Composition" $ do
    it "composes pattern relations correctly" $ do
      let p1 = Rw 
            (Free $ F (Free $ G (var 0)) (var 1))
            (Free $ R (var 1) (var 0))
      
      let p2 = Rw
            (Free $ R (Free $ S (var 0)) (var 1))
            (Free $ K (var 0))
      
      let expected = Rw
            (Free $ F (Free $ G (var 0)) (Free $ S (var 1)))
            (Free $ K (var 1))
      
      composePatterns p1 p2 `shouldBe` Just expected

  describe "Pattern Composition 2" $ do
    it "variables names in first pattern don't matter" $ do
      let p1 = Rw 
            (Free $ F (Free $ G (var 2)) (var 3))
            (Free $ R (var 3) (var 2))
      
      let p2 = Rw
            (Free $ R (Free $ S (var 0)) (var 1))
            (Free $ K (var 0))
      
      let expected = Rw
            (Free $ F (Free $ G (var 0)) (Free $ S (var 1)))
            (Free $ K (var 1))
      
      composePatterns p1 p2 `shouldBe` Just expected

    it "handles repeated variables in composition" $ do
      let p1 = Rw
            (Free $ F (var 0) (var 0))  -- F x x
            (Free $ G (var 0))          -- G x
      
      let p2 = Rw
            (Free $ G (var 0))          -- G y
            (Free $ K (var 0))          -- K y
      
      let expected = Rw
            (Free $ F (var 0) (var 0))  -- F x x
            (Free $ K (var 0))          -- K x
      
      composePatterns p1 p2 `shouldBe` Just expected

    it "fails composition when patterns don't match" $ do
      let p1 = Rw (var 0) (Free $ F (var 0) (var 1))
      let p2 = Rw (Free $ G (var 0)) (var 0)
      composePatterns p1 p2 `shouldBe` Nothing

  describe "Pattern Conjunction" $ do
    it "combines simple patterns conjunctively" $ do
      let p1 = Rw 
            (Free $ F (var 0) (var 1))  -- F x y
            (Free $ G (var 0))          -- G x
      
      let p2 = Rw
            (Free $ F (var 0) (var 1))  -- F x y
            (Free $ G (var 1))          -- G y
      
      let expected = Rw
            (Free $ F (var 0) (var 0))  -- F x y
            (Free $ G (var 0))          -- G x where x=y
      
      andPattern p1 p2 `shouldBe` Just expected

  describe "Pattern Conjunction 2" $ do
    it "Variable assignments for first pattern don't matter" $ do
      let p1 = Rw 
            (Free $ F (var 2) (var 3))  -- F x y
            (Free $ G (var 2))          -- G x
      
      let p2 = Rw
            (Free $ F (var 0) (var 1))  -- F x y
            (Free $ G (var 1))          -- G y
      
      let expected = Rw
            (Free $ F (var 0) (var 0))  -- F x y
            (Free $ G (var 0))          -- G x where x=y
      
      andPattern p1 p2 `shouldBe` Just expected

    it "fails conjunction when patterns can't be unified" $ do
      let p1 = Rw
            (Free $ F (var 0) (var 1))      -- F x y
            (Free $ G (var 0))              -- G x
      
      let p2 = Rw
            (Free $ F (var 0) (var 1))      -- F x y
            (Free $ K (var 0))              -- K x
      
      andPattern p1 p2 `shouldBe` Nothing

    it "handles complex nested terms in conjunction" $ do
      let p1 = Rw
            (Free $ F (Free $ G (var 0)) (var 1))  -- F (G x) y
            (Free $ R (var 0) (var 1))             -- R x y
      
      let p2 = Rw
            (Free $ F (Free $ G (var 0)) (var 1))  -- F (G x) y
            (Free $ R (Free $ K (var 1)) (var 0))  -- R (K y) x
      
      let expected = Rw
            (Free $ F (Free $ G (Free $ K (var 0))) (var 0))  -- F (G (K x)) x
            (Free $ R (Free $ K (var 0)) (var 0))             -- R (K x) x
      
      andPattern p1 p2 `shouldBe` Just expected 