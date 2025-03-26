{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module RecConstraint (
  SimpRec(..),
  RecConstraint(..),
  RecConstraint
) where

import Control.Monad.Free (Free(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Constraint (Constraint(..))
import RelExp (applySubst)
import Data.Functor.Classes (Show1)

-- | Simple recursive constraint function type
newtype SimpRec f = SimpRec { 
  runSimpRec :: f (Free f Int) -> Maybe ([(String, SimpRec f, Free f Int)], Map Int (Free f Int))
}

-- | Recursive constraint type that holds a list of recursive functions and their target terms
newtype RecConstraint f = RecConstraint [(String, SimpRec f, Free f Int)]

instance Semigroup (RecConstraint f) where
  (<>) (RecConstraint xs) (RecConstraint ys) = RecConstraint (xs ++ ys)

instance Monoid (RecConstraint f) where
  mempty = RecConstraint []

instance Eq (RecConstraint f) where
  _ == _ = True

instance Show1 f => Show (RecConstraint f) where
  show (RecConstraint pairs) = "{ " ++ unlines (map (\(s,_,i) -> s ++ "(" ++ show i ++ ")") pairs) ++ " }"

-- | Process a term until it becomes pure or fails
processTerm :: Functor f 
            => (String, SimpRec f, Free f Int)
            -> Maybe (Map (Int, String) (SimpRec f), Map Int (Free f Int))
processTerm (s, r, Pure i) = Just (Map.singleton (i, s) r, mempty)
processTerm (s, r, Free f) = case runSimpRec r f of
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
            => [(String, SimpRec f, Free f Int)]
            -> Maybe (Map (Int, String) (SimpRec f), Map Int (Free f Int))
processOnce [] = Just (Map.empty, mempty)
processOnce (tups:rest) = do
  -- Process current pair
  (pureMap1, subst1) <- processTerm tups
  -- Process rest with substitutions applied
  let restWithSubst = [(n, r, applySubst subst1 t) | (n, r, t) <- rest]
  (pureMap2, subst2) <- processOnce restWithSubst
  -- Combine results
  return (Map.union pureMap1 pureMap2, subst1 <> subst2)

-- | Check if any pure terms have substitutions and generate new pairs
checkPures :: Functor f 
           => Map (Int, String) (SimpRec f)  -- Pure terms map
           -> Map Int (Free f Int)  -- Substitution map
           -> ([(String, SimpRec f, Free f Int)], Map (Int, String) (SimpRec f), Map Int (Free f Int))
checkPures pureMap subst =
  let 
    -- Find pure terms that have substitutions
    (matching, nonMatching) = Map.partitionWithKey (\(k, _) _ -> Map.member k subst) pureMap
    -- Generate new pairs from matching terms
    newPairs = [(name, r, applySubst subst (Pure v)) 
               | ((v, name), r) <- Map.toList matching]
    -- Remove used substitutions
    remainingSubst = foldr Map.delete subst (map fst $ Map.keys matching)
  in
    (newPairs, nonMatching, remainingSubst)

-- | Normalize constraints until reaching a fixed point
normalizeLoop :: Functor f 
              => [(String, SimpRec f, Free f Int)]  -- Current constraints
              -> Map (Int, String) (SimpRec f)        -- Pure terms map
              -> Map Int (Free f Int)       -- Current substitution map
              -> Maybe ([(String, SimpRec f, Free f Int)], Map Int (Free f Int))
normalizeLoop [] pureMap subst = 
  -- No more constraints to process, check pures one last time
  let (newPairs, finalPures, finalSubst) = checkPures pureMap subst
  in if null newPairs
     then 
       -- We're done - convert pure map back to pairs
       let purePairs = [(name, r, Pure v) | ((v, name), r) <- Map.toList finalPures]
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
    RecConstraint [(name, r, applySubst s t) | (name, r, t) <- pairs]