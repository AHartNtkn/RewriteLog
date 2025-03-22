{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}

module TreeCalc
  ( TreeCalcF(..)
  , TreeCalc
  , c
  , l
  , b
  , f
  , treeCalcApp
  , prettyPrintTreeCalc
  ) where

import Control.Monad.Free (Free(..))
import Data.Functor.Classes (Eq1(..))
import RelExp (RelExp(..), mkOr, mkComp, mkAnd, var)

-- | Tree calculus functor
data TreeCalcF x = C Int | L | B x | F x x
  deriving (Eq, Functor, Foldable, Show, Traversable)

instance Eq1 TreeCalcF where
  liftEq eq (C n) (C n') = n == n'
  liftEq eq L L = True
  liftEq eq (B x) (B y) = eq x y
  liftEq eq (F x y) (F x' y') = eq x x' && eq y y'
  liftEq _ _ _ = False

type TreeCalc = Free TreeCalcF

-- Smart constructors
c :: Int -> TreeCalc Int
c n = Free (C n)

l :: TreeCalc Int
l = Free L

b :: TreeCalc Int -> TreeCalc Int
b x = Free (B x)

f :: TreeCalc Int -> TreeCalc Int -> TreeCalc Int
f x y = Free (F x y)

prettyPrintTreeCalc :: TreeCalc Int -> String
prettyPrintTreeCalc (Pure n) = show n
prettyPrintTreeCalc (Free (C n)) = "C_" ++ show n
prettyPrintTreeCalc (Free L) = "L"
prettyPrintTreeCalc (Free (B x)) = "B[" ++ prettyPrintTreeCalc x ++ "]"
prettyPrintTreeCalc (Free (F x y)) = "F[" ++ prettyPrintTreeCalc x ++ ", " ++ prettyPrintTreeCalc y ++ "]"

-- | Tree calculus application rules using RelExp
treeCalcApp :: RelExp TreeCalcF
treeCalcApp = mkOr
  [ -- app[L, z_] := B[z]
    Rw (f l (var 0))
       (b (var 0))

  , -- app[B[y_], z_] := F[y, z]
    Rw (f (b (var 0)) (var 1))
       (f (var 0) (var 1))

  , -- app[F[L, y_], z_] := y
    Rw (f (f l (var 0)) (var 1))
       (var 0)

  , -- app[F[F[w_, x_], y_], L] := w
    Rw (f (f (f (var 0) (var 1)) (var 2)) l)
       (var 0)

  , -- app[F[B[x_], y_], z_] := app[app[x, z], app[y, z]]
    mkComp [
      mkAnd [
        mkComp [ -- app[x, z]
          Rw (f (f (b (var 0)) (var 1)) (var 2))
             (f (var 0) (var 2)),
          treeCalcApp,
          Rw (var 0) (f (var 0) (var 1))
        ],
        mkComp [ -- app[y, z]
          Rw (f (f (b (var 0)) (var 1)) (var 2))
             (f (var 1) (var 2)),
          treeCalcApp,
          Rw (var 1) (f (var 0) (var 1))
        ]
      ],
      treeCalcApp
    ]

  , -- app[F[F[w_, x_], y_], B[u_]] := app[x, u]
    mkComp [
      Rw (f (f (f (var 0) (var 1)) (var 2)) (b (var 3)))
         (f (var 1) (var 3)),
      treeCalcApp
    ]

  , -- app[F[F[w_, x_], y_], F[u_, v_]] := app[app[y, u], v]
    mkComp [
      mkAnd [
        mkComp [ -- app[y, u]
          Rw (f (f (f (var 0) (var 1)) (var 2)) (f (var 3) (var 4)))
             (f (var 2) (var 3)),
          treeCalcApp,
          Rw (var 0) (f (var 0) (var 1))
        ]
        , -- v
        Rw (f (f (f (var 0) (var 1)) (var 2)) (f (var 3) (var 4)))
           (f (var 5) (var 4))
      ],
      treeCalcApp
    ]
  ] 