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
  applySubst,
  andPattern,
  run,
  mkAnd,
  mkOr,
  mkComp
) where

import Control.Monad.Free (Free(..))
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Foldable (toList)
import Data.Functor.Classes (Eq1(..))
import Data.List (splitAt)

-- | Relational expressions indexed by an endofunctor f
data RelExp f
  = Fail
  | Rw (Free f Int) (Free f Int)
  | Or (RelExp f) (RelExp f)
  | And Bool (RelExp f) (RelExp f)  -- Boolean indicates if And has been processed
  | Comp (RelExp f) (RelExp f)
  deriving (Show, Eq)

-- | Smart constructor for And that creates a balanced tree
mkAnd :: [RelExp f] -> RelExp f
mkAnd [] = error "mkAnd: empty list"
mkAnd [x] = x
mkAnd xs = 
  let n = length xs
      (left, right) = splitAt (n `div` 2) xs
  in And False (mkAnd left) (mkAnd right)

-- | Smart constructor for Or that creates a balanced tree
mkOr :: [RelExp f] -> RelExp f
mkOr [] = error "mkOr: empty list"
mkOr [x] = x
mkOr xs = 
  let n = length xs
      (left, right) = splitAt (n `div` 2) xs
  in Or (mkOr left) (mkOr right)

-- | Smart constructor for Comp that creates a balanced tree
mkComp :: [RelExp f] -> RelExp f
mkComp [] = error "mkComp: empty list"
mkComp [x] = x
mkComp xs = 
  let n = length xs
      (left, right) = splitAt (n `div` 2) xs
  in Comp (mkComp left) (mkComp right)

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
match :: (Eq1 f, Traversable f) => Free f Int -> Free f Int -> Maybe (Map.Map Int (Free f Int))
match t1 t2 = solveEquations [(t1, t2)]

-- | Solve a system of matching equations
solveEquations :: (Eq1 f, Traversable f) => [Equation f] -> Maybe (Map.Map Int (Free f Int))
solveEquations [] = Just Map.empty  -- Empty equation set means we succeeded
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
        then Just subst  -- Variables are already equal
        else  -- Make higher-numbered variable equal to lower-numbered one
          let (from, to) = if v1 > v2 then (v1, v2) else (v2, v1) in
          Just (Map.insert from (Pure to) subst)
    -- First term is a variable
    (Pure v, t) -> Just (Map.insert v t subst)
    -- Second term is a variable
    (t, Pure v) -> Just (Map.insert v t subst)
    -- Both terms are constructors
    (Free f1, Free f2)
      | fmap (const ()) f1 == fmap (const ()) f2 ->
        -- If constructors match, add equations for subterms
        solveEquations (zip (toList f1) (toList f2) ++ eqs)
      | otherwise -> Nothing  -- Constructor mismatch

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
composePatterns :: (Eq1 f, Traversable f) => RelExp f -> RelExp f -> Maybe (RelExp f)
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
composePatterns _ _ = Nothing

-- | Combine two pattern relations conjunctively
andPattern :: (Eq1 f, Traversable f) => RelExp f -> RelExp f -> Maybe (RelExp f)
andPattern (Rw p1 p2) (Rw p3 p4) = do
  -- First rename variables in the second pattern to avoid name clashes
  let maxVar = maximum (collectVars p1 ++ collectVars p2)
      shiftMap = Map.fromList [(i, i + maxVar + 1) | i <- collectVars p3 ++ collectVars p4]
      p3' = applySubst (fmap Pure shiftMap) p3
      p4' = applySubst (fmap Pure shiftMap) p4
  -- Match corresponding terms with renamed variables
  subst1 <- match p1 p3'
  let p2WithSubst1 = applySubst subst1 p2
      p4WithSubst1 = applySubst subst1 p4'
  subst2 <- match p2WithSubst1 p4WithSubst1
  -- Apply both substitutions
  let p1Final = applySubst subst2 (applySubst subst1 p1)
      p2Final = applySubst subst2 p2WithSubst1
      -- Collect variables in order of appearance
      vars = collectVars p1Final ++ filter (`notElem` collectVars p1Final) (collectVars p2Final)
      varMap = mkVarMap vars
  return $ Rw (applySubst (fmap Pure varMap) p1Final) (applySubst (fmap Pure varMap) p2Final)
andPattern _ _ = Nothing

rwLeaf :: RelExp f -> Bool
rwLeaf (Rw _ _) = True
rwLeaf (Or x _) = rwLeaf x
rwLeaf _ = False

distributeComp :: RelExp f -> RelExp f -> RelExp f
distributeComp (Or x y) a = Or (distributeComp x a) (Comp y a)
distributeComp x a = Comp x a

step :: (Eq1 f, Traversable f) => Bool -> RelExp f -> (Maybe (RelExp f), RelExp f)
-- Base cases
step collect Fail = (Nothing, Fail)
step collect (Rw x y) = if collect then (Just (Rw x y), Fail) else (Nothing, Rw x y)
-- Failure cases
step collect (Comp Fail _) = (Nothing, Fail)
step collect (Comp _ Fail) = (Nothing, Fail)
step collect (Comp _ (Comp Fail _)) = (Nothing, Fail)
step collect (Comp _ (Comp _ Fail)) = (Nothing, Fail)
-- Composition normalization
step collect (Comp (Comp p1 p2) p3) = step collect (Comp p1 (Comp p2 p3))
step collect (Comp p1 (Comp (Comp p2 p3) p4)) = step collect (Comp p1 (Comp p2 (Comp p3 p4)))
-- Rewrite fusion
step collect (Comp (Rw p1 p2) (Rw p3 p4)) = 
  case composePatterns (Rw p1 p2) (Rw p3 p4) of
    Nothing -> (Nothing, Fail)
    Just composed -> (Nothing, composed)
step collect (Comp (Rw p1 p2) (Comp (Rw p3 p4) r)) = 
  case composePatterns (Rw p1 p2) (Rw p3 p4) of
    Nothing -> (Nothing, Fail)
    Just composed -> (Nothing, Comp composed r)
-- And evaluation
step collect (And _ Fail _) = (Nothing, Fail)
step collect (And _ _ Fail) = (Nothing, Fail)
step collect (And _ (Rw p1 p2) (Rw p3 p4)) = 
  case andPattern (Rw p1 p2) (Rw p3 p4) of
    Nothing -> (Nothing, Fail)
    Just pat -> (Nothing, pat)
step collect (Comp (And _ (Rw p1 p2) (Rw p3 p4)) r) = 
  case andPattern (Rw p1 p2) (Rw p3 p4) of
    Nothing -> (Nothing, Fail)
    Just pat -> (Nothing, Comp pat r)
step collect (And b x y) = 
  let (rx, x') = step False x
      (ry, y') = step False y
  in (Nothing, And b x' y')
step collect (Comp (And b x y) r) = 
  let (rx, x') = step False x
      (ry, y') = step False y
  in (Nothing, Comp (And b x' y') r)
step collect (And b (Or x y) z) = step collect (Or (And b x z) (And b y z))
step collect (And b x (Or y z)) = step collect (Or (And b x y) (And b x z))
-- And absorption
-- (Rw a b) (S ∩ T) ~> (Rw a b) (((Rw b b) S) ∩ ((Rw b b) T))
-- which is valid since (Rw b b) ⊆ Id. This is an optimization.
step collect (Comp (Rw p1 p2) (And False a b)) = 
  let (_, stepped) = step False (And True (Comp (Rw p2 p2) a) (Comp (Rw p2 p2) b))
  -- When And hasn't been processed, add identity composition
  in (Nothing, Comp (Rw p1 p2) stepped)
-- In general, we only have that R(S ∩ T) ⊆ RS ∩ RT, not R(S ∩ T) = RS ∩ RT
-- So we have to evaluate And until it's no longer there.
step collect (Comp (Rw p1 p2) (And True a b)) = 
  -- When And has been processed
  let (_, a') = step False a
      (_, b') = step False b
  in (Nothing, Comp (Rw p1 p2) (And True a' b'))
step collect (Comp (Rw p1 p2) (Comp (And False a b) r)) = 
  let (_, stepped) = step False (Comp (And True (Comp (Rw p2 p2) a) (Comp (Rw p2 p2) b)) r)
  -- When And hasn't been processed, add identity composition
  in (Nothing, Comp (Rw p1 p2) stepped)
step collect (Comp (Rw p1 p2) (Comp (And True a b) r)) = 
  -- When And has been processed
  let (_, a') = step False a
      (_, b') = step False b
  in (Nothing, Comp (Rw p1 p2) (Comp (And True a' b') r))
-- Or case
step collect (Or Fail p) = step collect p
step collect (Or x y) = 
  let (rx, x') = step collect x
  in (rx, Or y x')
step collect (Comp (Or x y) r) =
  if rwLeaf x
  then 
    case r of
      Comp a r -> 
        let (rt, stepped) = step collect (distributeComp (Or x y) a)
        in (rt, Comp stepped r)
      r -> 
        let (rt, stepped) = step collect (distributeComp (Or x y) r)
        in (rt, stepped)
  else 
    let (rx, xy') = step collect (Or x y)
    in (rx, Comp xy' r)
-- Or absorption
step collect (Comp (Rw p1 p2) (Or a b)) = step collect (Or (Comp (Rw p1 p2) a) (Comp (Rw p1 p2) b))
step collect (Comp (Rw p1 p2) (Comp (Or a b) r)) = step collect (Comp (Or (Comp (Rw p1 p2) a) (Comp (Rw p1 p2) b)) r)

-- | Run a relational expression to completion, collecting all normalized patterns
run :: (Eq1 f, Traversable f) => RelExp f -> [RelExp f]
run expr = case step True expr of
  (Just v, rest) -> v : run rest
  (Nothing, Fail) -> []  -- Stop when we hit Fail
  (Nothing, rest) -> run rest
