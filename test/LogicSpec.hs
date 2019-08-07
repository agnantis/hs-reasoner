{-# OPTIONS_GHC -fno-warn-orphans #-}
module LogicSpec (spec) where

import Test.Hspec
import Test.QuickCheck

import Logic

-------------------------
-- Arbitrary instances --
-------------------------

instance Arbitrary Concept where
  arbitrary = do
    lbl <- arbitrary
    c1  <- arbitrary
    c2  <- arbitrary
    r1  <- arbitrary
    let
      conj = Conjunction c1 c2
      dis  = Disjunction c1 c2
      nt   = Not c1
      impl = Implies c1 c2
      ifif = IfOnlyIf c1 c2
      atl  = Exists r1 c1
      fora = ForAll r1 c1
      atm  = Atomic lbl
    oneof . fmap pure $ [atm, nt]  -- conj, dis, nt, impl, ifif, atl, fora, atm]
                                  -- NOTE: not included otherwise property test never ends 
     
instance Arbitrary Role where
  arbitrary = Role <$> arbitrary


-------------------------
-- Auxiliary functions --
-------------------------


-- Example A --
vegan, person, vegeterian, plant, diary :: Concept
vegan      = Atomic "vegan"
person     = Atomic "person"
vegeterian = Atomic "vegeterian"
plant      = Atomic "plant"
diary      = Atomic "diary"

eats :: Role
eats = Role "eats"

veganClass :: CGI
veganClass = vegan `isEquivalentTo` Conjunction person (ForAll eats plant)

vegeterianClass :: CGI
vegeterianClass = vegeterian `isEquivalentTo` Conjunction person (ForAll eats (Disjunction plant diary))

vegeterianIsVegan :: CGI
vegeterianIsVegan = vegeterian `isSubsumedBy` vegan

veganIsVegeterian :: CGI
veganIsVegeterian = vegan `isSubsumedBy` vegeterian 

-- Example B --
human :: Concept
human = Atomic "human"

parent :: Role
parent = Role "parent"

humanHasHumanParent :: CGI
humanHasHumanParent = human `isSubsumedBy` Exists parent human

humanCGI :: CGI
humanCGI = SimpleCGI human -- `isSubsumedBy` Top

simpleExistsCGI :: CGI
simpleExistsCGI = SimpleCGI $ Exists parent human
-- Example C --
classA, classB :: Concept
classA = Atomic "A"
classB = Atomic "B"

cgiA, cgiB, cgiC :: CGI
cgiA = simpleCGI $ classA `Implies` classB
cgiB = simpleCGI classA
cgiC = simpleCGI $ Not classB
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
  describe "inverse" $ 
    it "when inversed is like id" $
      property $ \x -> (inverse . inverse) (toDNF x) == toDNF (x :: Concept)

------------------
-- Unit testing --
------------------

unitTests :: Spec
unitTests = 
  describe "The assertion" $ do
    it "with Exists should terminate" $ 
      pPrint (isValidModelS [simpleExistsCGI] []) `shouldBe` ""
      
    it "that a vegan is always a vegeterian should hold" $
      isProvable veganIsVegeterian [veganClass, vegeterianClass] [] `shouldBe` True

    it "that a vegeterian is always vegan should not hold" $
      isProvable vegeterianIsVegan [veganClass, vegeterianClass] [] `shouldNotBe` True

--    it "that a human has at least one human parent should hold" $
--      pPrint (isValidModelS [humanCGI, humanHasHumanParent] []) `shouldBe` ""

    it "that invalidates 'implies' should not hold" $
      isValidModel [cgiA, cgiB, cgiC] [] `shouldNotBe` True
  
