{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module Main (main) where

import Test.Hspec
import qualified AddRelSpec
import qualified StepSpec
import qualified PatternMatchSpec

main :: IO ()
main = hspec $ do
  describe "Pattern Matching Tests" PatternMatchSpec.spec
  describe "Step Tests" StepSpec.spec
  describe "AddRel Tests" AddRelSpec.spec
