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
  runTrace,
  mkAnd,
  mkOr,
  mkComp,
  var,
  step,
  rw,
  cnstr,
  prettyPrintRelExp,
  dual,
  collectVars
) where

import Control.Monad.Free (Free(..))
import Control.Monad.State (State, get, put, runState)
import Control.Monad (when)
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Foldable (toList)
import Data.Functor.Classes (Eq1(..), Show1(..))
import Data.List (splitAt, intercalate, intersperse)
import Data.Monoid (Monoid(..))
import Constraint (Constraint(..), VarFilter(..))
import qualified Data.Set as Set
import Data.Set (Set)

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

dual :: RelExp f c -> RelExp f c
dual Fail = Fail
dual (Rw p1 p2 c) = Rw p2 p1 c
dual (Or x y) = Or (dual x) (dual y)
dual (And b x y) = And b (dual x) (dual y)
dual (Comp x y) = Comp (dual y) (dual x)

-- | Pretty print a RelExp up to a specified depth
prettyPrintRelExp :: (Show1 f, Show c) => Int -> RelExp f c -> String
prettyPrintRelExp _ Fail = "Fail"
prettyPrintRelExp depth (Rw p1 p2 c) = 
  if depth <= 0 
  then "..." 
  else "Rw (" ++ showsPrec1 1 p1 "" ++ ") (" ++ showsPrec1 1 p2 "" ++ ") " ++ show c
prettyPrintRelExp depth (Or p1 p2) = 
  if depth <= 0 
  then "..." 
  else "Or (" ++ prettyPrintRelExp (depth-1) p1 ++ ") (" ++ prettyPrintRelExp (depth-1) p2 ++ ")"
prettyPrintRelExp depth (And b p1 p2) = 
  if depth <= 0 
  then "..." 
  else "And " ++ show b ++ " (" ++ prettyPrintRelExp (depth-1) p1 ++ ") (" ++ prettyPrintRelExp (depth-1) p2 ++ ")"
prettyPrintRelExp depth (Comp p1 p2) = 
  if depth <= 0 
  then "..." 
  else "Comp (" ++ prettyPrintRelExp (depth-1) p1 ++ ") (" ++ prettyPrintRelExp (depth-1) p2 ++ ")"

-- | Helper function to show Free terms using Show1
showsPrec1 :: Show1 f => Int -> Free f Int -> ShowS
showsPrec1 d (Pure i) = shows i
showsPrec1 d (Free f) = showsPrec1String d f

-- | Helper function to show Free terms using Show1
showsPrec1String :: Show1 f => Int -> f (Free f Int) -> ShowS
showsPrec1String d f = 
  let showsPrecFree = showsPrec1
      showList1_ xs = showChar '[' 
                    . foldr (.) id (intersperse (showChar ',') (map (showsPrec1 0) xs))
                    . showChar ']'
  in liftShowsPrec showsPrecFree showList1_ d f

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
collectVars :: (Functor f, Foldable f) => Free f Int -> Set.Set Int
collectVars (Pure i) = Set.singleton i
collectVars (Free t) = Set.unions $ map collectVars $ toList t

-- | Create a mapping from old variables to new normalized variables
mkVarMap :: Set Int -> Map Int Int
mkVarMap = Map.fromList . flip zip [0..] . Set.toAscList

-- | Normalize variables in a Free term, starting from 0
normalizeVars :: (Functor f, Foldable f) => Free f Int -> Free f Int
normalizeVars t = 
  let vars = Set.toAscList $ collectVars t
      varMap = Map.fromList $ zip vars [0..]
  in applySubst (fmap Pure varMap) t

-- | Compose two pattern relations
composePatterns :: forall f c. (Eq1 f, Traversable f, Constraint c f) => RelExp f c -> RelExp f c -> Maybe (RelExp f c)
composePatterns (Rw p1 p2 c1) (Rw p3 p4 c2) = do
  -- First rename variables in the second pattern to avoid name clashes
  let vars1 = collectVars p1 `Set.union` collectVars p2
      maxVar = if Set.null vars1 then -1 else Set.findMax vars1
      shiftMap :: Map Int (Free f Int)
      shiftMap = fmap Pure $ Map.fromList [(i, i + maxVar + 1) | i <- Set.toList $ collectVars p3 `Set.union` collectVars p4]
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
      varsSet = collectVars p1Final `Set.union` 
               (collectVars p4Final `Set.difference` collectVars p1Final)
      varMap :: Map Int (Free f Int)
      varMap = fmap Pure $ mkVarMap varsSet
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
  let vars1 = collectVars p1 `Set.union` collectVars p2
      maxVar = if Set.null vars1 then -1 else Set.findMax vars1
      shiftMap :: Map Int (Free f Int)
      shiftMap = fmap Pure $ Map.fromList [(i, i + maxVar + 1) | i <- Set.toList $ collectVars p3 `Set.union` collectVars p4]
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
      varsSet = collectVars p1Final `Set.union` 
               (collectVars p2Final `Set.difference` collectVars p1Final)
      varMap :: Map Int (Free f Int)
      varMap = fmap Pure $ mkVarMap varsSet
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

step :: (Eq1 f, Traversable f, Constraint c f) => Bool -> RelExp f c -> State (Maybe (RelExp f c)) (RelExp f c)
-- Base cases
step collect Fail = return Fail
step collect (Rw x y c) = do
  when collect $ put (Just (Rw x y c))
  return $ if collect then Fail else Rw x y c
-- Failure cases
step collect (Comp Fail _) = return Fail
step collect (Comp _ Fail) = return Fail
step collect (Comp _ (Comp Fail _)) = return Fail
-- Composition normalization
step collect (Comp (Comp p1 p2) p3) = step collect (Comp p1 (Comp p2 p3))
step collect (Comp p1 (Comp (Comp p2 p3) p4)) = step collect (Comp p1 (Comp p2 (Comp p3 p4)))
-- Rewrite fusion
step collect (Comp (Rw p1 p2 c1) (Rw p3 p4 c2)) = 
  case composePatterns (Rw p1 p2 c1) (Rw p3 p4 c2) of
    Nothing -> return Fail
    Just composed -> return composed
step collect (Comp (Rw p1 p2 c1) (Comp (Rw p3 p4 c2) r)) = 
  case composePatterns (Rw p1 p2 c1) (Rw p3 p4 c2) of
    Nothing -> return Fail
    Just composed -> return $ Comp composed r
-- And evaluation
step collect (And _ Fail _) = return Fail
step collect (And _ _ Fail) = return Fail
step collect (And _ (Rw p1 p2 c1) (Rw p3 p4 c2)) = 
  case andPattern (Rw p1 p2 c1) (Rw p3 p4 c2) of
    Nothing -> return Fail
    Just pat -> return pat
-- These cases allow the different and branches to talk with eachother.
step collect (And b (Rw p1 p2 c1) r) = 
  let c' = filterVars (collectVars p1) c1 in
  return $ Comp (Rw p1 p1 c') $ And b r (Rw p1 p2 c1)
step collect (And b (Comp (Rw p1 p2 c1) r) s) =
  (Comp (Rw p1 p1 c1) . And b s) <$> step False (Comp (Rw p1 p2 c1) r)
step collect (And b (Or x y) z) = step collect (Or (And b z x) (And b z y))
step collect (And b x y) = And b y <$> step False x
step collect (Comp (And b x y) r) = flip Comp r <$> step False (And b x y)
-- And absorption
-- (Rw a b) (S ∩ T) ~> (Rw a b) (((Rw b b) S) ∩ ((Rw b b) T))
-- which is valid since (Rw b b) ⊆ Id. This is an optimization.
step collect (Comp (Rw p1 p2 c) (And False a b)) =
  Comp (Rw p1 p2 c) <$> step False (And True (Comp (Rw p2 p2 c) a) (Comp (Rw p2 p2 c) b))
step collect (Comp (Rw p1 p2 c) (Comp (And False a b) r)) =
  Comp (Rw p1 p2 c) <$> step False (Comp (And True (Comp (Rw p2 p2 c) a) (Comp (Rw p2 p2 c) b)) r)
-- In general, we only have that R(S ∩ T) ⊆ RS ∩ RT, not R(S ∩ T) = RS ∩ RT
-- So we have to evaluate And until it's no longer there.
step collect (Comp (Rw p1 p2 c) (And True a b)) =
  Comp (Rw p1 p2 c) <$> step False (And True a b)
step collect (Comp (Rw p1 p2 c) (Comp (And True a b) r)) =
  (Comp (Rw p1 p2 c) . flip Comp r) <$> step False (And True a b)
-- Or case
step collect (Or Fail p) = step collect p
step collect (Or x y) = do
  x' <- step collect x
  case x' of
    Fail -> return y
    _ -> return $ Or y x' -- Swap x and y for interleaving search
step collect (Comp (Or x y) r) =
  if rwLeaf x
  then 
    case r of
      Comp a r -> flip Comp r <$> step collect (distributeComp (Or x y) a)
      r -> step collect (distributeComp (Or x y) r)
  else flip Comp r <$> step collect (Or x y)
-- Or absorption
step collect (Comp (Rw p1 p2 c) (Or a b)) = step collect (Or (Comp (Rw p1 p2 c) a) (Comp (Rw p1 p2 c) b))
step collect (Comp (Rw p1 p2 c) (Comp (Or a b) r)) = step collect (Comp (Or (Comp (Rw p1 p2 c) a) (Comp (Rw p1 p2 c) b)) r)

-- | Run a relational expression to completion, collecting all normalized patterns
run :: (Eq1 f, Traversable f, Constraint c f) => RelExp f c -> [RelExp f c]
run expr = case runState (step True expr) Nothing of
  (next, Just v) -> v : run next
  (Fail, Nothing) -> []  -- Stop when we hit Fail
  (next, Nothing) -> run next

-- | Run a relational expression to completion, returning a list of tuples containing
-- the intermediate state and any output produced at that step
runTrace :: (Eq1 f, Traversable f, Constraint c f) => RelExp f c -> [(RelExp f c, Maybe (RelExp f c))]
runTrace expr = case runState (step True expr) Nothing of
  (next, output) -> (next, output) : case next of
    Fail -> []  -- Stop when we hit Fail
    _ -> runTrace next
