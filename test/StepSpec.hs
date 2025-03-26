{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module StepSpec (spec) where

import Test.Hspec
import RelExp
import Control.Monad.Free (Free(..))
import Control.Monad.State (runState)
import qualified Data.Map as Map
import Data.Functor.Classes (Show1(..), Eq1(..))
import Constraint (EmptyConstraint(..))

-- Simple functor for testing
data TestF a = A a | B a a
  deriving (Show, Eq, Functor, Foldable, Traversable)

instance Show1 TestF where
  liftShowsPrec sp _ d (A x) = showParen (d > 10) $
    showString "A " . sp 11 x
  liftShowsPrec sp _ d (B x y) = showParen (d > 10) $
    showString "B " . sp 11 x . showChar ' ' . sp 11 y

instance Eq1 TestF where
  liftEq eq (A x1) (A x2) = eq x1 x2
  liftEq eq (B x1 y1) (B x2 y2) = eq x1 x2 && eq y1 y2
  liftEq _ _ _ = False

stepi :: Bool -> RelExp TestF EmptyConstraint -> (Maybe (RelExp TestF EmptyConstraint), RelExp TestF EmptyConstraint)
stepi collect expr = 
  let (next, output) = runState (step collect expr) Nothing
  in (output, next)

spec :: Spec
spec = do
  describe "step function" $ do
    it "handles base case Fail" $ do
      let (result, next) = stepi True Fail
      result `shouldBe` Nothing
      next `shouldBe` Fail

    it "handles base case Rw with collect=True" $ do
      let pat = rw (var 0) (var 1)
      let (result, next) = stepi True pat
      result `shouldBe` Just pat
      next `shouldBe` Fail

    it "handles base case Rw with collect=False" $ do
      let pat = rw (var 0) (var 1)
      let (result, next) = stepi False pat
      result `shouldBe` Nothing
      next `shouldBe` pat

    it "handles Comp with Fail on left" $ do
      let expr = Comp Fail (rw (var 0) (var 1))
      let (result, next) = stepi True expr
      result `shouldBe` Nothing
      next `shouldBe` Fail

    it "handles Comp with Fail on right" $ do
      let expr = Comp (rw (var 0) (var 1)) Fail
      let (result, next) = stepi True expr
      result `shouldBe` Nothing
      next `shouldBe` Fail

    it "handles nested Comp normalization" $ do
      let expr = Comp (Comp (rw (var 0) (var 1)) (rw (var 1) (var 2))) (rw (var 2) (var 3))
      let (result, next) = stepi True expr
      result `shouldBe` Nothing
      next `shouldNotBe` expr  -- Should be restructured

    it "handles rewrite fusion" $ do
      let expr = Comp (rw (var 0) (var 1)) (rw (var 1) (var 2))
      let (result, next) = stepi True expr
      result `shouldBe` Nothing
      next `shouldBe` rw (var 0) (var 1)

    it "handles And with Fail" $ do
      let expr = And False Fail (rw (var 0) (var 1))
      let (result, next) = stepi True expr
      result `shouldBe` Nothing
      next `shouldBe` Fail

    it "handles And with identical patterns" $ do
      let expr = And False (rw (var 0) (var 1)) (rw (var 0) (var 1))
      let (result, next) = stepi True expr
      result `shouldBe` Nothing
      next `shouldBe` rw (var 0) (var 1)

    it "handles And distribution over Or" $ do
      let expr = And False (Or (rw (var 0) (var 1)) (rw (var 1) (var 2))) (rw (var 2) (var 3))
      let (result, next) = stepi True expr
      result `shouldBe` Nothing
      next `shouldNotBe` expr  -- Should be distributed

    it "handles And absorption with identity" $ do
      let expr = Comp (rw (var 0) (var 1)) (And False (rw (var 1) (var 2)) (rw (var 1) (var 3)))
      let (result, next) = stepi True expr
      result `shouldBe` Nothing
      next `shouldNotBe` expr  -- Should be absorbed

    it "handles Or with Fail" $ do
      let expr = Or Fail (rw (var 0) (var 1))
      let (result, next) = stepi True expr
      result `shouldBe` (Just (rw (var 0) (var 1)))
      next `shouldBe` Fail

    it "handles Or distribution over Comp" $ do
      let expr = Comp (Or (rw (var 0) (var 1)) (rw (var 1) (var 2))) (rw (var 2) (var 3))
      let (result, next) = stepi True expr
      result `shouldBe` Nothing
      next `shouldNotBe` expr  -- Should be distributed

    it "handles Or absorption" $ do
      let expr = Comp (rw (var 0) (var 1)) (Or (rw (var 1) (var 2)) (rw (var 1) (var 3)))
      let (result, next) = stepi True expr
      result `shouldBe` Nothing
      next `shouldNotBe` expr  -- Should be absorbed

    it "handles complex nested expressions" $ do
      let expr = Comp 
            (Or 
              (rw (var 0) (var 1))
              (And False 
                (rw (var 0) (var 2))
                (rw (var 2) (var 1))))
            (Comp 
              (rw (var 1) (var 3))
              (Or 
                (rw (var 3) (var 4))
                (rw (var 3) (var 5))))
      let (result, next) = stepi True expr
      result `shouldBe` Nothing
      next `shouldNotBe` expr  -- Should be transformed

    it "handles pattern matching with TestF functor" $ do
      let expr = Comp 
            (rw (Free $ A (var 0)) (Free $ B (var 0) (var 1)))
            (rw (Free $ B (var 0) (var 1)) (Free $ A (var 1)))
      let (result, next) = stepi True expr
      result `shouldBe` Nothing
      next `shouldBe` rw (Free $ A (var 0)) (Free $ A (var 1))

    it "Successor test" $ do
      let expr = Comp 
            (rw (Free $ B (Free $ A (var 0)) (var 1)) (Free $ B (var 0) (var 1)))
            (rw (Free $ B (Free $ A (var 0)) (var 1)) (Free $ B (var 0) (var 1)))
      let (result, next) = stepi True expr
      result `shouldBe` Nothing
      next `shouldBe` (rw (Free $ B (Free $ A (Free $ A (var 0))) (var 1)) (Free $ B (var 0) (var 1)))