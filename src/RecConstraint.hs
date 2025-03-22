{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module RecConstraint (
  SimpRec(..),
  RecConstraint(..),
  mkRecConstraint
) where

import Control.Monad.Free (Free(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid (Monoid(..))
import Data.Semigroup (Semigroup(..))
import Constraint (Constraint(..))

-- | Simple recursive constraint function type
newtype SimpRec f = SimpRec { 
  runSimpRec :: f (Free f Int) -> Maybe ([(SimpRec f, Free f Int)], Map Int (Free f Int))
}

-- | Recursive constraint type that holds a list of recursive functions and their target terms
newtype RecConstraint f = RecConstraint [(SimpRec f, Free f Int)]

-- | Smart constructor for RecConstraint
mkRecConstraint :: [(SimpRec f, Free f Int)] -> RecConstraint f
mkRecConstraint = RecConstraint

instance Semigroup (RecConstraint f) where
  (<>) (RecConstraint xs) (RecConstraint ys) = RecConstraint (xs ++ ys)

instance Monoid (RecConstraint f) where
  mempty = RecConstraint []

-- | Process a term until it becomes pure or fails
processTerm :: Functor f 
            => (SimpRec f, Free f Int)
            -> Maybe (Map Int (SimpRec f), Map Int (Free f Int))
processTerm (rec, Pure i) = Just (Map.singleton i rec, mempty)
processTerm (rec, Free f) = case runSimpRec rec f of
  Nothing -> Nothing
  Just (newPairs, subst) -> do
    -- Process each new pair recursively
    results <- traverse processTerm newPairs
    -- Combine all results
    let (pureMaps, substs) = unzip results
        combinedPureMap = Map.unions pureMaps
        combinedSubst = subst <> mconcat substs
    return (combinedPureMap, combinedSubst)

-- | Process a list of constraints once, collecting pure terms and substitutions
processOnce :: Functor f 
            => [(SimpRec f, Free f Int)]
            -> Maybe (Map Int (SimpRec f), Map Int (Free f Int))
processOnce [] = Just (Map.empty, mempty)
processOnce (pair:rest) = do
  -- Process current pair
  (pureMap1, subst1) <- processTerm pair
  -- Process rest with substitutions applied
  let restWithSubst = [(r, applySubst subst1 t) | (r, t) <- rest]
  (pureMap2, subst2) <- processOnce restWithSubst
  -- Combine results
  return (Map.union pureMap1 pureMap2, subst1 <> subst2)

-- | Check if any pure terms have substitutions and generate new pairs
checkPures :: Functor f 
           => Map Int (SimpRec f)  -- Pure terms map
           -> Map Int (Free f Int)  -- Substitution map
           -> ([(SimpRec f, Free f Int)], Map Int (SimpRec f), Map Int (Free f Int))
checkPures pureMap subst =
  let 
    -- Find pure terms that have substitutions
    (matching, nonMatching) = Map.partitionWithKey (\k _ -> Map.member k subst) pureMap
    -- Generate new pairs from matching terms
    newPairs = [(rec, applySubst subst (Pure v)) 
               | (v, rec) <- Map.toList matching]
    -- Remove used substitutions
    remainingSubst = foldr Map.delete subst (Map.keys matching)
  in
    (newPairs, nonMatching, remainingSubst)

-- | Normalize constraints until reaching a fixed point
normalizeLoop :: Functor f 
              => [(SimpRec f, Free f Int)]  -- Current constraints
              -> Map Int (SimpRec f)        -- Pure terms map
              -> Map Int (Free f Int)       -- Current substitution map
              -> Maybe ([(SimpRec f, Free f Int)], Map Int (Free f Int))
normalizeLoop [] pureMap subst = 
  -- No more constraints to process, check pures one last time
  let (newPairs, finalPures, finalSubst) = checkPures pureMap subst
  in if null newPairs
     then 
       -- We're done - convert pure map back to pairs
       let purePairs = [(rec, Pure v) | (v, rec) <- Map.toList finalPures]
       in Just (purePairs, finalSubst)
     else 
       -- Process new pairs
       normalizeLoop newPairs finalPures finalSubst
normalizeLoop pairs pureMap subst = do
  -- Process current batch of constraints
  (newPureMap, newSubst) <- processOnce pairs
  let combinedPureMap = Map.union newPureMap pureMap  -- Take newer mappings in case of conflict
      combinedSubst = subst <> newSubst
      -- Check if any pure terms have substitutions
      (newPairs, remainingPures, remainingSubst) = checkPures combinedPureMap combinedSubst
  -- Continue with new pairs and updated maps
  normalizeLoop newPairs remainingPures remainingSubst

instance (Functor f) => Constraint (RecConstraint f) f where
  normalize (RecConstraint pairs) = do
    (normPairs, subst) <- normalizeLoop pairs Map.empty Map.empty
    return (RecConstraint normPairs, subst)

  substCnstr s (RecConstraint pairs) = 
    RecConstraint [(r, applySubst s t) | (r, t) <- pairs]

-- | Helper to apply a substitution to a Free term
applySubst :: Functor f => Map Int (Free f Int) -> Free f Int -> Free f Int
applySubst s (Pure i) = Map.findWithDefault (Pure i) i s
applySubst s (Free t) = Free $ fmap (applySubst s) t 