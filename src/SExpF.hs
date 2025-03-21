{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module SExpF
  ( SExpF(..)
  , atom
  , cons
  , ppSExp  -- Export the pretty printer
  ) where

import Data.Functor.Classes (Eq1(..), Show1(..))
import Control.Monad.Free (Free(..))
import RelExp (RelExp(..), mkOr, mkComp)

-- | S-expression functor
data SExpF x = Atom String | Cons x x
  deriving (Eq, Functor, Foldable, Traversable)

deriving instance Show x => Show (SExpF x)

-- | Make SExpF an instance of Eq1
instance Eq1 SExpF where
  liftEq eq (Atom s1) (Atom s2) = s1 == s2
  liftEq eq (Cons h1 t1) (Cons h2 t2) = eq h1 h2 && eq t1 t2
  liftEq _ _ _ = False

-- | Make SExpF an instance of Show1
instance Show1 SExpF where
  liftShowsPrec sp _ _ (Atom s) = showString s
  liftShowsPrec sp _ _ (Cons x y) = showChar '(' . sp 0 x . showChar ' ' . sp 0 y . showChar ')'

-- | Pretty print an S-expression
ppSExp :: Free SExpF Int -> String
ppSExp (Pure n) = show n
ppSExp (Free (Atom s)) = s
ppSExp (Free (Cons x y)) = "(" ++ ppSExp x ++ " " ++ ppSExp y ++ ")"

-- | Smart constructor for atomic terms
atom :: String -> Free SExpF Int
atom s = Free (Atom s)

-- | Smart constructor for cons cells
cons :: Free SExpF Int -> Free SExpF Int -> Free SExpF Int
cons x y = Free (Cons x y)

