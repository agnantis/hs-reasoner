module LogicSpec (spec) where

import Test.Hspec

spec :: Spec
spec =
  describe "Haskell" $ 
    it "should be able to add numbers" $
       3+2 `shouldBe` (5 :: Int)


