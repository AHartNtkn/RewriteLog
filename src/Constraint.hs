{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

module Constraint (
  Constraint(..),
  ProdConstraint(..),
  EmptyConstraint(..)
) where

import Control.Monad.Free (Free)
import Data.Map (Map)
import Data.Monoid (Monoid(..))
import Data.Semigroup (Semigroup(..))

-- | Type class for constraints that can be normalized and have substitutions applied
class Monoid c => Constraint c f where
  -- | Normalize a constraint, potentially producing a substitution
  normalize :: c -> Maybe (c, Map Int (Free f Int))
  
  -- | Apply a substitution to a constraint
  substCnstr :: Map Int (Free f Int) -> c -> c

-- | Product of two constraints
data ProdConstraint c1 c2 = ProdConstraint c1 c2
  deriving (Show, Eq)

-- | Make ProdConstraint a semigroup
instance (Semigroup c1, Semigroup c2) => Semigroup (ProdConstraint c1 c2) where
  (<>) (ProdConstraint a1 b1) (ProdConstraint a2 b2) = 
    ProdConstraint (a1 <> a2) (b1 <> b2)

-- | Make ProdConstraint a monoid
instance (Monoid c1, Monoid c2) => Monoid (ProdConstraint c1 c2) where
  mempty = ProdConstraint mempty mempty

-- | Make ProdConstraint an instance of Constraint if both components are
instance (Constraint c1 f, Constraint c2 f) => Constraint (ProdConstraint c1 c2) f where
  normalize (ProdConstraint c1 c2) = do
    (c1', s1) <- normalize c1
    let c2' = substCnstr s1 c2
    (c2'', s2) <- normalize c2'
    let c1'' = substCnstr s2 c1'
    return (ProdConstraint c1'' c2'', s1 <> s2)
  
  substCnstr s (ProdConstraint c1 c2) = 
    ProdConstraint (substCnstr s c1) (substCnstr s c2)

-- | Empty constraint that always succeeds with no substitutions
data EmptyConstraint = EmptyConstraint
  deriving (Show, Eq)

instance Semigroup EmptyConstraint where
  (<>) _ _ = EmptyConstraint

instance Monoid EmptyConstraint where
  mempty = EmptyConstraint

-- | Make EmptyConstraint an instance of Constraint for any functor f
instance Constraint EmptyConstraint f where
  normalize c = Just (c, mempty)  -- Always succeeds with no substitution
  substCnstr _ c = c  -- No variables to substitute 