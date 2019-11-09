{-# OPTIONS_GHC -fno-warn-orphans #-}
module TableauSpec (spec) where

import Test.Hspec
import Test.QuickCheck

import HsReasoner.Types
import HsReasoner.Tableau

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

-- Example D --
roleR :: Role
roleR = Role "R"

concept1, concept2, concept3, concept4 :: Concept
concept1 = Exists roleR classA
concept2 = Exists roleR classB
concept3 = AtMost 1 roleR Top
concept4 = Exists roleR (Conjunction classA classB)

exampleD :: CGI
exampleD = Conjunction concept1 concept2 `isSubsumedBy` concept4

exampleE :: CGI
exampleE = Conjunction concept1 (Conjunction concept2 concept3) `isSubsumedBy` concept4

exFconcept1, exFconcept2 :: Concept
exFconcept1 = AtLeast 3 roleR Top
exFconcept2 = AtMost 2 roleR Top

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
      isValidModel [simpleExistsCGI] [] `shouldBe` True
      
    it "that a vegan is always a vegeterian should hold" $
      isProvable veganIsVegeterian [veganClass, vegeterianClass] [] `shouldBe` True

    it "that a vegeterian is always vegan should not hold" $
      isProvable vegeterianIsVegan [veganClass, vegeterianClass] [] `shouldNotBe` True

--    it "that a human has at least one human parent should hold" $
--      pPrint (isValidModelS [humanCGI, humanHasHumanParent] []) `shouldBe` ""

    it "that invalidates 'implies' should not hold" $
      isValidModel [cgiA, cgiB, cgiC] [] `shouldNotBe` True

    it "of exampleD should not hold" $
      isProvable exampleD [] [] `shouldNotBe` True
  
-- AtMost: not implemented yet
--    it "of exampleE should hold" $
--      isProvable exampleE [] [] `shouldBe` True
--  
--    it "temp: of exampleE should not hold" $
--      pPrint (isProvableS exampleE [] []) `shouldBe` ""

--    it "with >=nC && <=(n-1)C should not be valid" $
--      isValidModel (SimpleCGI <$> [exFconcept1, exFconcept2]) [] `shouldNotBe` True
