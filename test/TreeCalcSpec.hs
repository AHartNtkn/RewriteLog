module TreeCalcSpec (spec) where

import Test.Hspec
import TreeCalc
import RelExp
import Constraint (EmptyConstraint(..))

spec :: Spec
spec = do
  describe "TreeCalc application rules" $ do
    it "(f (f l (b l)) (b (b l))) ~> (b l)" $ do
      let input = f (f l (b l)) (b (b l))
      let expected = b l
      let results = run (Comp (rw input input) treeCalcApp) :: [RelExp TreeCalcF EmptyConstraint]
      results `shouldNotBe` []
      head results `shouldBe` rw input expected

    it "(f (f l (f l l)) (b (b (b l)))) ~> (f l l)" $ do
      let input = f (f l (f l l)) (b (b (b l)))
      let expected = f l l
      let results = run (Comp (rw input input) treeCalcApp) :: [RelExp TreeCalcF EmptyConstraint]
      results `shouldNotBe` []
      head results `shouldBe` rw input expected

    it "(f (f (f l l) l) (b (b l))) ~> (b (b l))" $ do
      let input = f (f (f l l) l) (b (b l))
      let expected = b (b l)
      let results = run (Comp (rw input input) treeCalcApp) :: [RelExp TreeCalcF EmptyConstraint]
      results `shouldNotBe` []
      head results `shouldBe` rw input expected

    it "(f (f l (b l)) (b (b l))) ~> (b l)" $ do
      let input = f (f l (b l)) (b (b l))
      let expected = b l
      let results = run (Comp (rw input input) treeCalcApp) :: [RelExp TreeCalcF EmptyConstraint]
      results `shouldNotBe` []
      head results `shouldBe` rw input expected

    it "(f (b (f l l)) (f l l)) ~> (f (f l l) (f l l))" $ do
      let input = f (b (f l l)) (f l l)
      let expected = f (f l l) (f l l)
      let results = run (Comp (rw input input) treeCalcApp) :: [RelExp TreeCalcF EmptyConstraint]
      results `shouldNotBe` []
      head results `shouldBe` rw input expected

    it "(f (f l l) (f (b l) (b l))) ~> l" $ do
      let input = f (f l l) (f (b l) (b l))
      let expected = l
      let results = run (Comp (rw input input) treeCalcApp) :: [RelExp TreeCalcF EmptyConstraint]
      results `shouldNotBe` []
      head results `shouldBe` rw input expected

    it "(f (f l (b l)) (f (b l) (b l))) ~> (b l)" $ do
      let input = f (f l (b l)) (f (b l) (b l))
      let expected = b l
      let results = run (Comp (rw input input) treeCalcApp) :: [RelExp TreeCalcF EmptyConstraint]
      results `shouldNotBe` []
      head results `shouldBe` rw input expected

    it "(f (b l) (b (b (b l)))) ~> (f l (b (b (b l))))" $ do
      let input = f (b l) (b (b (b l)))
      let expected = f l (b (b (b l)))
      let results = run (Comp (rw input input) treeCalcApp) :: [RelExp TreeCalcF EmptyConstraint]
      results `shouldNotBe` []
      head results `shouldBe` rw input expected

    it "(f (f (f l (f l l)) (f l (b l))) (f (f l l) (b (f l l)))) ~> (f l (b (f l l)))" $ do
      let input = f (f (f l (f l l)) (f l (b l))) (f (f l l) (b (f l l)))
      let expected = f l (b (f l l))
      let results = run (Comp (rw input input) treeCalcApp) :: [RelExp TreeCalcF EmptyConstraint]
      results `shouldNotBe` []
      head results `shouldBe` rw input expected

    it "(f (f (f l (b l)) (f (b l) (b l))) (f l (f (b l) (b l)))) ~> (f l l)" $ do
      let input = f (f (f l (b l)) (f (b l) (b l))) (f l (f (b l) (b l)))
      let expected = f l l
      let results = run (Comp (rw input input) treeCalcApp) :: [RelExp TreeCalcF EmptyConstraint]
      results `shouldNotBe` []
      head results `shouldBe` rw input expected 
      