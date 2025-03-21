{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module StepSpec (spec) where

import Test.Hspec
import RelExp
import Control.Monad.Free (Free(..))
import qualified Data.Map as Map
import Data.Functor.Classes (Show1(..), Eq1(..))

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

spec :: Spec
spec = do
  describe "step function" $ do
    it "handles base case Fail" $ do
      let (result, next) = step True (Fail :: RelExp TestF)
      result `shouldBe` Nothing
      next `shouldBe` Fail

    it "handles base case Rw with collect=True" $ do
      let pat = Rw (var 0) (var 1) :: RelExp TestF
      let (result, next) = step True pat
      result `shouldBe` Just pat
      next `shouldBe` Fail

    it "handles base case Rw with collect=False" $ do
      let pat = Rw (var 0) (var 1) :: RelExp TestF
      let (result, next) = step False pat
      result `shouldBe` Nothing
      next `shouldBe` pat

    it "handles Comp with Fail on left" $ do
      let expr = Comp Fail (Rw (var 0) (var 1)) :: RelExp TestF
      let (result, next) = step True expr
      result `shouldBe` Nothing
      next `shouldBe` Fail

    it "handles Comp with Fail on right" $ do
      let expr = Comp (Rw (var 0) (var 1)) Fail :: RelExp TestF
      let (result, next) = step True expr
      result `shouldBe` Nothing
      next `shouldBe` Fail

    it "handles nested Comp normalization" $ do
      let expr = Comp (Comp (Rw (var 0) (var 1)) (Rw (var 1) (var 2))) (Rw (var 2) (var 3)) :: RelExp TestF
      let (result, next) = step True expr
      result `shouldBe` Nothing
      next `shouldNotBe` expr  -- Should be restructured

    it "handles rewrite fusion" $ do
      let expr = Comp (Rw (var 0) (var 1)) (Rw (var 1) (var 2)) :: RelExp TestF
      let (result, next) = step True expr
      result `shouldBe` Nothing
      next `shouldBe` Rw (var 0) (var 1)

    it "handles And with Fail" $ do
      let expr = And False Fail (Rw (var 0) (var 1)) :: RelExp TestF
      let (result, next) = step True expr
      result `shouldBe` Nothing
      next `shouldBe` Fail

    it "handles And between two rewrites" $ do
      let expr = And False (Rw (var 0) (var 1)) (Rw (var 0) (var 1)) :: RelExp TestF
      let (result, next) = step True expr
      result `shouldBe` Nothing
      next `shouldBe` Rw (var 0) (var 1)

    it "handles And distribution over Or" $ do
      let expr = And False (Or (Rw (var 0) (var 1)) (Rw (var 1) (var 2))) (Rw (var 2) (var 3)) :: RelExp TestF
      let (result, next) = step True expr
      result `shouldBe` Nothing
      next `shouldNotBe` expr  -- Should be distributed

    it "handles And absorption with identity" $ do
      let expr = Comp (Rw (var 0) (var 1)) (And False (Rw (var 1) (var 2)) (Rw (var 1) (var 3))) :: RelExp TestF
      let (result, next) = step True expr
      result `shouldBe` Nothing
      next `shouldNotBe` expr  -- Should be absorbed

    it "handles Or with Fail" $ do
      let expr = Or Fail (Rw (var 0) (var 1)) :: RelExp TestF
      let (result, next) = step True expr
      result `shouldBe` (Just (Rw (var 0) (var 1)))
      next `shouldBe` Fail

    it "handles Or distribution over Comp" $ do
      let expr = Comp (Or (Rw (var 0) (var 1)) (Rw (var 1) (var 2))) (Rw (var 2) (var 3)) :: RelExp TestF
      let (result, next) = step True expr
      result `shouldBe` Nothing
      next `shouldNotBe` expr  -- Should be distributed

    it "handles Or absorption" $ do
      let expr = Comp (Rw (var 0) (var 1)) (Or (Rw (var 1) (var 2)) (Rw (var 1) (var 3))) :: RelExp TestF
      let (result, next) = step True expr
      result `shouldBe` Nothing
      next `shouldNotBe` expr  -- Should be absorbed

    it "handles complex nested expressions" $ do
      let expr = Comp 
            (Or 
              (Rw (var 0) (var 1))
              (And False 
                (Rw (var 0) (var 2))
                (Rw (var 2) (var 1))))
            (Comp 
              (Rw (var 1) (var 3))
              (Or 
                (Rw (var 3) (var 4))
                (Rw (var 3) (var 5)))) :: RelExp TestF
      let (result, next) = step True expr
      result `shouldBe` Nothing
      next `shouldNotBe` expr  -- Should be transformed

    it "handles pattern matching with TestF functor" $ do
      let expr = Comp 
            (Rw (Free $ A (var 0)) (Free $ B (var 0) (var 1)))
            (Rw (Free $ B (var 0) (var 1)) (Free $ A (var 1))) :: RelExp TestF
      let (result, next) = step True expr
      result `shouldBe` Nothing
      next `shouldBe` Rw (Free $ A (var 0)) (Free $ A (var 1)) 

    it "Successor test" $ do
      let expr = Comp 
            (Rw (Free $ B (Free $ A (var 0)) (var 1)) (Free $ B (var 0) (var 1)))
            (Rw (Free $ B (Free $ A (var 0)) (var 1)) (Free $ B (var 0) (var 1))) :: RelExp TestF
      let (result, next) = step True expr
      result `shouldBe` Nothing
      next `shouldBe` (Rw (Free $ B (Free $ A (Free $ A (var 0))) (var 1)) (Free $ B (var 0) (var 1)))