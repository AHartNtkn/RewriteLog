{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

module RelExp (
  RelExp(..),
  match,
  composePatterns,
  normalizeVars,
  zipMatch,
  applySubst
) where

import Control.Monad.Free (Free(..))
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Foldable (toList)
import Data.Functor.Classes (Eq1(..))

-- | Relational expressions indexed by an endofunctor f
data RelExp f
  = Empty
  | Rw (Free f Int) (Free f Int)
  | Or (RelExp f) (RelExp f)
  | And (RelExp f) (RelExp f)
  | Comp (RelExp f) (RelExp f)
  deriving (Show, Eq)

-- | A substitution maps variable indices to terms
type Subst f = Map Int (Free f Int)

-- | An equation represents a matching constraint between two terms
type Equation f = (Free f Int, Free f Int)

-- | Match up corresponding elements in two functors
zipMatch :: (Traversable f, Eq1 f) => f a -> f a -> Maybe [(a, a)]
zipMatch f1 f2 
  | fmap (const ()) f1 == fmap (const ()) f2 = 
    -- If the shapes match, zip the elements
    Just $ zip (toList f1) (toList f2)
  | otherwise = Nothing

-- | Try to match two Free terms, returning possible substitutions for the first term's variables
match :: (Eq1 f, Traversable f) => Free f Int -> Free f Int -> [Map.Map Int (Free f Int)]
match t1 t2 = solveEquations [(t1, t2)]

-- | Solve a system of matching equations
solveEquations :: (Eq1 f, Traversable f) => [Equation f] -> [Map.Map Int (Free f Int)]
solveEquations [] = [Map.empty]  -- Empty equation set means we succeeded
solveEquations ((t1, t2):eqs) = do
  -- First solve the remaining equations
  subst <- solveEquations eqs
  -- Apply substitution to both terms
  let t1' = applySubst subst t1
      t2' = applySubst subst t2
  case (t1', t2') of
    -- Both terms are variables
    (Pure v1, Pure v2) ->
      if v1 == v2
        then [subst]  -- Variables are already equal
        else  -- Make higher-numbered variable equal to lower-numbered one
          let (from, to) = if v1 > v2 then (v1, v2) else (v2, v1) in
          [Map.insert from (Pure to) subst]
    -- First term is a variable
    (Pure v, t) -> [Map.insert v t subst]
    -- Second term is a variable
    (t, Pure v) -> [Map.insert v t subst]
    -- Both terms are constructors
    (Free f1, Free f2)
      | fmap (const ()) f1 == fmap (const ()) f2 ->
        -- If constructors match, add equations for subterms
        solveEquations (zip (toList f1) (toList f2) ++ eqs)
      | otherwise -> []  -- Constructor mismatch
    -- Any other case is a mismatch
    _ -> []

-- | Apply a substitution to a Free term
applySubst :: Functor f => Subst f -> Free f Int -> Free f Int
applySubst s (Pure i) = fromMaybe (Pure i) (Map.lookup i s)
applySubst s (Free t) = Free $ fmap (applySubst s) t

-- | Collect all variables in a Free term
collectVars :: (Functor f, Foldable f) => Free f Int -> [Int]
collectVars (Pure i) = [i]
collectVars (Free t) = concat $ map collectVars $ toList t

-- | Create a mapping from old variables to new normalized variables
mkVarMap :: [Int] -> Map Int Int
mkVarMap = Map.fromList . flip zip [0..] . uniqueElems
  where
    uniqueElems [] = []
    uniqueElems (x:xs) = x : uniqueElems (filter (/= x) xs)

-- | Normalize variables in a Free term, starting from 0
normalizeVars :: (Functor f, Foldable f) => Free f Int -> Free f Int
normalizeVars t = 
  let vars = collectVars t
      varMap = mkVarMap vars
  in applySubst (fmap Pure varMap) t

-- | Compose two pattern relations
composePatterns :: (Eq1 f, Traversable f) => RelExp f -> RelExp f -> [RelExp f]
composePatterns (Rw p1 p2) (Rw p3 p4) = do
  -- First rename variables in the second pattern to avoid name clashes
  let maxVar = maximum (collectVars p1 ++ collectVars p2)
      shiftMap = Map.fromList [(i, i + maxVar + 1) | i <- collectVars p3 ++ collectVars p4]
      p3' = applySubst (fmap Pure shiftMap) p3
      p4' = applySubst (fmap Pure shiftMap) p4
  -- Now match with renamed variables
  subst <- match p2 p3'
  let p1Final = applySubst subst p1
      p4Final = applySubst subst p4'
      -- Collect variables in order of appearance
      vars = collectVars p1Final ++ filter (`notElem` collectVars p1Final) (collectVars p4Final)
      varMap = mkVarMap vars
  return $ Rw (applySubst (fmap Pure varMap) p1Final) (applySubst (fmap Pure varMap) p4Final)
composePatterns _ _ = []
