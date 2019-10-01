{-# LANGUAGE TypeApplications #-}

module UtilsSpec (spec) where

import Test.Hspec
import Test.QuickCheck

import Data.Tuple      (swap)
import HsReasoner.Utils

---------------
-- Test data --
---------------

pairwiseList :: [(Int, Int)]
pairwiseList =
             [ (1,2)
             , (2,3)
             , (3,4)
             , (4,5)
             ]

pairwiseUnorderedList :: [(Int, Int)]
pairwiseUnorderedList =
             [ (1,2)
             , (2,3)
             , (3,4)
             , (4,5)
             ]


fullList :: [(Int, Int)]
fullList =
             [ (1,2)
             , (1,3)
             , (1,4)
             , (2,3)
             , (2,4)
             , (3,4)
             ]

-------------------
-- Testing specs --
-------------------

spec :: Spec
spec = do
  props
  unitTests

----------------------
-- Property testing --
----------------------

props :: Spec
props = 
  describe "distinct sets" $ do
    it "order of pairs should not matter" $
      property $ \x -> distinctSets @[(Int, Int)] x == distinctSets (reverse x)
    it "pairwise order should not matter" $
      property $ \x -> distinctSets @[(Int, Int)] x == distinctSets (swap <$> x)
    it "order of pairs and pairwise order should not matter" $
      property $ \x -> distinctSets @[(Int, Int)] x == distinctSets (reverse $ swap <$> x)
      

------------------
-- Unit testing --
------------------

unitTests :: Spec
unitTests = 
  describe "Test distinct elements" $ do
    it "will return max two distinct elements for ordered pairwise lists" $ 
      maxDistinctSet pairwiseList `shouldBe` [1,2]
    it "will return max two distinct elements for not-ordered pairwise lists" $ 
      maxDistinctSet pairwiseList `shouldBe` [1,2]
    it "will return all elements if all combinations are present" $
      maxDistinctSet fullList `shouldBe` [1,2,3,4]
    it "will return all elements if all combinations are present but reversed" $
      distinctSets (reverse fullList) `shouldBe` distinctSets fullList
