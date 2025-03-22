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
  mkComp,
  var,
  step,
  rw,
  cnstr
) where

import Control.Monad.Free (Free(..))
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Foldable (toList)
import Data.Functor.Classes (Eq1(..))
import Data.List (splitAt)
import Data.Monoid (Monoid(..))
import Constraint (Constraint(..))

-- | Relational expressions indexed by an endofunctor f and constraint type c
data RelExp f c
  = Fail
  | Rw (Free f Int) (Free f Int) c
  | Or (RelExp f c) (RelExp f c)
  | And Bool (RelExp f c) (RelExp f c)  -- Boolean indicates if And has been processed
  | Comp (RelExp f c) (RelExp f c)
  deriving (Show, Eq)

-- | Smart constructor for And that creates a balanced tree
mkAnd :: [RelExp f c] -> RelExp f c
mkAnd [] = error "mkAnd: empty list"
mkAnd [x] = x
mkAnd xs = 
  let n = length xs
      (left, right) = splitAt (n `div` 2) xs
  in And False (mkAnd left) (mkAnd right)

-- | Smart constructor for Or that creates a balanced tree
mkOr :: [RelExp f c] -> RelExp f c
mkOr [] = error "mkOr: empty list"
mkOr [x] = x
mkOr xs = 
  let n = length xs
      (left, right) = splitAt (n `div` 2) xs
  in Or (mkOr left) (mkOr right)

-- | Smart constructor for Comp that creates a balanced tree
mkComp :: [RelExp f c] -> RelExp f c
mkComp [] = error "mkComp: empty list"
mkComp [x] = x
mkComp xs = 
  let n = length xs
      (left, right) = splitAt (n `div` 2) xs
  in Comp (mkComp left) (mkComp right)

-- | Helper to create a rewrite rule with empty constraint
rw :: (Monoid c) => Free f Int -> Free f Int -> RelExp f c
rw l r = Rw l r mempty

-- | Helper to create a rewrite rule with a given constraint
cnstr :: c -> RelExp f c
cnstr c = Rw (var 0) (var 0) c

var :: Int -> Free f Int
var i = Pure i

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
composePatterns :: forall f c. (Eq1 f, Traversable f, Constraint c f) => RelExp f c -> RelExp f c -> Maybe (RelExp f c)
composePatterns (Rw p1 p2 c1) (Rw p3 p4 c2) = do
  -- First rename variables in the second pattern to avoid name clashes
  let vars1 = collectVars p1 ++ collectVars p2
      maxVar = if null vars1 then -1 else maximum vars1
      shiftMap :: Map Int (Free f Int)
      shiftMap = fmap Pure $ Map.fromList [(i, i + maxVar + 1) | i <- collectVars p3 ++ collectVars p4]
      p3' = applySubst shiftMap p3
      p4' = applySubst shiftMap p4
      c2' = substCnstr shiftMap c2
  -- Now match with renamed variables
  subst <- match p2 p3'
  let p1Final = applySubst subst p1
      p4Final = applySubst subst p4'
      c1' = substCnstr subst c1
      c2'' = substCnstr subst c2'
      -- Collect variables in order of appearance
      vars = collectVars p1Final ++ filter (`notElem` collectVars p1Final) (collectVars p4Final)
      varMap :: Map Int (Free f Int)
      varMap = fmap Pure $ mkVarMap vars
      -- Apply final variable normalization to terms and constraints
      p1Norm = applySubst varMap p1Final
      p4Norm = applySubst varMap p4Final
      c1Norm = substCnstr varMap c1'
      c2Norm = substCnstr varMap c2''
  -- Normalize the combined constraint
  (cFinal, normSubst) <- normalize (mappend c1Norm c2Norm)
  -- Apply any substitutions from constraint normalization
  return $ Rw (applySubst normSubst p1Norm) (applySubst normSubst p4Norm) cFinal
composePatterns _ _ = Nothing

-- | Combine two pattern relations conjunctively
andPattern :: forall f c. (Eq1 f, Traversable f, Constraint c f) => RelExp f c -> RelExp f c -> Maybe (RelExp f c)
andPattern (Rw p1 p2 c1) (Rw p3 p4 c2) = do
  -- First rename variables in the second pattern to avoid name clashes
  let maxVar = maximum (collectVars p1 ++ collectVars p2)
      shiftMap :: Map Int (Free f Int)
      shiftMap = fmap Pure $ Map.fromList [(i, i + maxVar + 1) | i <- collectVars p3 ++ collectVars p4]
      p3' = applySubst shiftMap p3
      p4' = applySubst shiftMap p4
      c2' = substCnstr shiftMap c2
  -- Match corresponding terms with renamed variables
  subst1 <- match p1 p3'
  let p2WithSubst1 = applySubst subst1 p2
      p4WithSubst1 = applySubst subst1 p4'
      c1' = substCnstr subst1 c1
      c2'' = substCnstr subst1 c2'
  subst2 <- match p2WithSubst1 p4WithSubst1
  -- Apply both substitutions
  let p1Final = applySubst subst2 (applySubst subst1 p1)
      p2Final = applySubst subst2 p2WithSubst1
      c1'' = substCnstr subst2 c1'
      c2''' = substCnstr subst2 c2''
      -- Collect variables in order of appearance
      vars = collectVars p1Final ++ filter (`notElem` collectVars p1Final) (collectVars p2Final)
      varMap :: Map Int (Free f Int)
      varMap = fmap Pure $ mkVarMap vars
      -- Apply final variable normalization to terms and constraints
      p1Norm = applySubst varMap p1Final
      p2Norm = applySubst varMap p2Final
      c1Norm = substCnstr varMap c1''
      c2Norm = substCnstr varMap c2'''
  -- Normalize the combined constraint
  (cFinal, normSubst) <- normalize (mappend c1Norm c2Norm)
  -- Apply any substitutions from constraint normalization
  return $ Rw (applySubst normSubst p1Norm) (applySubst normSubst p2Norm) cFinal
andPattern _ _ = Nothing

rwLeaf :: RelExp f c -> Bool
rwLeaf (Rw _ _ _) = True
rwLeaf (Or x _) = rwLeaf x
rwLeaf _ = False

distributeComp :: RelExp f c -> RelExp f c -> RelExp f c
distributeComp (Or x y) a = Or (distributeComp x a) (Comp y a)
distributeComp x a = Comp x a

step :: (Eq1 f, Traversable f, Constraint c f) => Bool -> RelExp f c -> (Maybe (RelExp f c), RelExp f c)
-- Base cases
step collect Fail = (Nothing, Fail)
step collect (Rw x y c) = if collect then (Just (Rw x y c), Fail) else (Nothing, Rw x y c)
-- Failure cases
step collect (Comp Fail _) = (Nothing, Fail)
step collect (Comp _ Fail) = (Nothing, Fail)
step collect (Comp _ (Comp Fail _)) = (Nothing, Fail)
-- Composition normalization
step collect (Comp (Comp p1 p2) p3) = step collect (Comp p1 (Comp p2 p3))
step collect (Comp p1 (Comp (Comp p2 p3) p4)) = step collect (Comp p1 (Comp p2 (Comp p3 p4)))
-- Rewrite fusion
step collect (Comp (Rw p1 p2 c1) (Rw p3 p4 c2)) = 
  case composePatterns (Rw p1 p2 c1) (Rw p3 p4 c2) of
    Nothing -> (Nothing, Fail)
    Just composed -> (Nothing, composed)
step collect (Comp (Rw p1 p2 c1) (Comp (Rw p3 p4 c2) r)) = 
  case composePatterns (Rw p1 p2 c1) (Rw p3 p4 c2) of
    Nothing -> (Nothing, Fail)
    Just composed -> (Nothing, Comp composed r)
-- And evaluation
step collect (And _ Fail _) = (Nothing, Fail)
step collect (And _ _ Fail) = (Nothing, Fail)
step collect (And _ (Rw p1 p2 c1) (Rw p3 p4 c2)) = 
  case andPattern (Rw p1 p2 c1) (Rw p3 p4 c2) of
    Nothing -> (Nothing, Fail)
    Just pat -> (Nothing, pat)
step collect (And b x y) = 
  let (_, x') = step False x
      (_, y') = step False y
  in (Nothing, And b x' y')
step collect (Comp (And b x y) r) = 
  let (_, a') = step False (And b x y)
  in (Nothing, Comp a' r)
step collect (And b (Or x y) z) = step collect (Or (And b x z) (And b y z))
step collect (And b x (Or y z)) = step collect (Or (And b x y) (And b x z))
-- And absorption
-- (Rw a b c) (S ∩ T) ~> (Rw a b c) (((Rw b b c) S) ∩ ((Rw b b c) T))
-- which is valid since (Rw b b c) ⊆ Id. This is an optimization.
step collect (Comp (Rw p1 p2 c) (And False a b)) = 
  let (_, stepped) = step False (And True (Comp (Rw p2 p2 c) a) (Comp (Rw p2 p2 c) b))
  in (Nothing, Comp (Rw p1 p2 c) stepped)
step collect (Comp (Rw p1 p2 c) (Comp (And False a b) r)) = 
  let (_, stepped) = step False (Comp (And True (Comp (Rw p2 p2 c) a) (Comp (Rw p2 p2 c) b)) r)
  in (Nothing, Comp (Rw p1 p2 c) stepped)
-- In general, we only have that R(S ∩ T) ⊆ RS ∩ RT, not R(S ∩ T) = RS ∩ RT
-- So we have to evaluate And until it's no longer there.
step collect (Comp (Rw p1 p2 c) (And True a b)) = 
  let (_, a') = step False (And True a b)
  in (Nothing, Comp (Rw p1 p2 c) a')
step collect (Comp (Rw p1 p2 c) (Comp (And True a b) r)) = 
  let (_, a') = step False (And True a b)
  in (Nothing, Comp (Rw p1 p2 c) (Comp a' r))
-- Or case
step collect (Or Fail p) = step collect p
step collect (Or x y) = 
  let (rx, x') = step collect x
  in case x' of
    Fail -> (rx, y)
    _ -> (rx, Or y x') -- Swap x and y for interleaving search
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
step collect (Comp (Rw p1 p2 c) (Or a b)) = step collect (Or (Comp (Rw p1 p2 c) a) (Comp (Rw p1 p2 c) b))
step collect (Comp (Rw p1 p2 c) (Comp (Or a b) r)) = step collect (Comp (Or (Comp (Rw p1 p2 c) a) (Comp (Rw p1 p2 c) b)) r)

-- | Run a relational expression to completion, collecting all normalized patterns
run :: (Eq1 f, Traversable f, Constraint c f) => RelExp f c -> [RelExp f c]
run expr = case step True expr of
  (Just v, rest) -> v : run rest
  (Nothing, Fail) -> []  -- Stop when we hit Fail
  (Nothing, rest) -> run rest
