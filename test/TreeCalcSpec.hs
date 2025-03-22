module TreeCalcSpec (spec) where

import Test.Hspec
import TreeCalc
import RelExp (RelExp(..), run)

spec :: Spec
spec = do
  describe "TreeCalc application rules" $ do
    it "(f (f l (b l)) (b (b l))) ~> (b l)" $ do
      let input = f (f l (b l)) (b (b l))
          expected = b l
          results = run (Comp (Rw input input) treeCalcApp)
      results `shouldNotBe` []
      head results `shouldBe` Rw input expected

    it "(f (f l (f l l)) (b (b (b l)))) ~> (f l l)" $ do
      let input = f (f l (f l l)) (b (b (b l)))
          expected = f l l
          results = run (Comp (Rw input input) treeCalcApp)
      results `shouldNotBe` []
      head results `shouldBe` Rw input expected

    it "(f (f (f l l) l) (b (b l))) ~> (b (b l))" $ do
      let input = f (f (f l l) l) (b (b l))
          expected = b (b l)
          results = run (Comp (Rw input input) treeCalcApp)
      results `shouldNotBe` []
      head results `shouldBe` Rw input expected

    it "(f (f l (b l)) (b (b l))) ~> (b l)" $ do
      let input = f (f l (b l)) (b (b l))
          expected = b l
          results = run (Comp (Rw input input) treeCalcApp)
      results `shouldNotBe` []
      head results `shouldBe` Rw input expected

    it "(f (b (f l l)) (f l l)) ~> (f (f l l) (f l l))" $ do
      let input = f (b (f l l)) (f l l)
          expected = f (f l l) (f l l)
          results = run (Comp (Rw input input) treeCalcApp)
      results `shouldNotBe` []
      head results `shouldBe` Rw input expected

    it "(f (f l l) (f (b l) (b l))) ~> l" $ do
      let input = f (f l l) (f (b l) (b l))
          expected = l
          results = run (Comp (Rw input input) treeCalcApp)
      results `shouldNotBe` []
      head results `shouldBe` Rw input expected

    it "(f (f l (b l)) (f (b l) (b l))) ~> (b l)" $ do
      let input = f (f l (b l)) (f (b l) (b l))
          expected = b l
          results = run (Comp (Rw input input) treeCalcApp)
      results `shouldNotBe` []
      head results `shouldBe` Rw input expected

    it "(f (b l) (b (b (b l)))) ~> (f l (b (b (b l))))" $ do
      let input = f (b l) (b (b (b l)))
          expected = f l (b (b (b l)))
          results = run (Comp (Rw input input) treeCalcApp)
      results `shouldNotBe` []
      head results `shouldBe` Rw input expected 