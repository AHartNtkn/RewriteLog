module TreeCalcSpec (spec) where

import Test.Hspec
import TreeCalc (f, b, l, c, treeCalcApp, TreeCalcF, noUniVar)
import RelExp
import Constraint (EmptyConstraint(..))
import RecConstraint (RecConstraint, RecConstraint(..))

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

    it "(f (f (b (b l)) l) (c 0)) ~> (c 0)" $ do
      let input = f (f (b (b l)) l) (c 0)
      let expected = c 0
      let results = run (Comp (rw input input) treeCalcApp) :: [RelExp TreeCalcF EmptyConstraint]
      results `shouldNotBe` []
      head results `shouldBe` rw input expected 
      
    it "Search for Identity Function" $ do
      let idSearch = 
            mkComp [
              -- Create constraint that input has no universal variables
              cnstr (RecConstraint [("noUniVar", noUniVar, var 0)]),
              -- Apply program to universally quantified variable
              rw (var 0) (f (var 0) (c 0)),
              -- Apply TreeCalc application rules
              treeCalcApp,
              -- Expect output to be input variable
              rw (c 0) (c 0)
            ] :: RelExp TreeCalcF (RecConstraint TreeCalcF)
      
      let results = run idSearch :: [RelExp TreeCalcF (RecConstraint TreeCalcF)]
      results `shouldNotBe` []
      let firstResult = head results
      case firstResult of
        Rw prog _ _ -> do
          -- The identity function should be F[B[B[L]], L]
          let expectedId = f (b (b l)) l
          prog `shouldBe` expectedId
        _ -> expectationFailure "Expected a rewrite rule result"
      
      