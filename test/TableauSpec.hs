{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
module TableauSpec (spec) where

import Test.Hspec
import Test.QuickCheck

import qualified Data.Map     as M (empty, fromList, (!))
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

veganClass :: (Concept, Concept)
veganClass = (vegan, Conjunction person (ForAll eats plant))

vegeterianClass :: (Concept, Concept)
vegeterianClass = (vegeterian, Conjunction person (ForAll eats (Disjunction plant diary)))

vegeterianEqualsVegan :: CGI
vegeterianEqualsVegan = vegeterian `isEquivalentTo` vegan

vegeterianDisjointVegan :: CGI
vegeterianDisjointVegan = vegeterian `isDisjointWith` vegan

vegeterianIsVegan :: CGI
vegeterianIsVegan = vegeterian `isSubsumedBy` vegan

veganIsVegeterian :: CGI
veganIsVegeterian = vegan `isSubsumedBy` vegeterian 

-- Example B --
human :: Concept
human = Atomic "human"

parentR :: Role
parentR = Role "parent"

humanHasHumanParent :: CGI
humanHasHumanParent = human `isSubsumedBy` Exists parentR human

humanCGI :: CGI
humanCGI = SimpleCGI human -- `isSubsumedBy` Top

simpleExists :: Concept
simpleExists = Exists parentR human
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

-----------------
-- Family TBox --
-----------------
woman, man, mother, father, parent, grandMother, motherWithManyChildren, motherWithoutDaughter, wife, female :: Concept
woman = Atomic "Woman"
man = Atomic "Man"
mother = Atomic "Mother"
father = Atomic "Father"
parent = Atomic "Parent"
grandMother = Atomic "Grandmother"
motherWithManyChildren = Atomic "MotherWithManyChildren"
motherWithoutDaughter = Atomic "MotherWithoutDaughter"
wife = Atomic "Wife"
female = Atomic "Female"

hasChild, hasHusband :: Role
hasChild = Role "hasChild"
hasHusband = Role "hasHusband"

familyTBox :: TBox
familyTBox = M.fromList
  [ (woman, Conjunction person female)
  , (man, Conjunction person (Not woman))
  , (mother, Conjunction woman (Exists hasChild person))
  , (father, Conjunction man (Exists hasChild person))
  , (parent, Disjunction father mother)
  , (grandMother, Conjunction mother (Exists hasChild parent))
  , (motherWithManyChildren, Conjunction mother (AtLeast 3 hasChild Top))
  , (motherWithoutDaughter, Conjunction mother (ForAll hasChild (Not woman)))
  , (wife, Conjunction woman (Exists hasHusband man))
  ]

expandedFamilyTBox :: TBox
expandedFamilyTBox = M.fromList
  [ (woman, Conjunction person female)
  , (man, Conjunction
            person
            (Not (Conjunction person female)))
  , (mother, Conjunction
              (Conjunction person female)
              (Exists hasChild person))
  , (father, Conjunction
              (Conjunction
                person
                (Not (Conjunction person female)))
              (Exists hasChild person))
  , (parent, Disjunction
               (Conjunction
                 (Conjunction person (Not (Conjunction person female)))
                 (Exists hasChild person))
               (Conjunction
                 (Conjunction person female)
                 (Exists hasChild person)))
  , (grandMother, Conjunction
                    (Conjunction
                      (Conjunction person female)
                      (Exists hasChild person))
                    (Exists hasChild
                      (Disjunction
                        (Conjunction
                          (Conjunction
                            person
                            (Not (Conjunction person female)))
                          (Exists hasChild person))
                        (Conjunction
                          (Conjunction person female)
                          (Exists hasChild person)))))
  , (motherWithManyChildren, Conjunction
                              (Conjunction
                                (Conjunction person female)
                                (Exists hasChild person))
                              (AtLeast 3 hasChild Top))
  , (motherWithoutDaughter, Conjunction
                              (Conjunction
                                (Conjunction person female)
                                (Exists hasChild person))
                              (ForAll hasChild (Not (Conjunction person female))))
  , (wife, Conjunction
             (Conjunction person female)
             (Exists hasHusband (Conjunction person (Not (Conjunction person female)))))
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
  describe "inverse" $ 
    it "when inversed is like id" $
      property $ \x -> (inverse . inverse) (toDNF x) == toDNF (x :: Concept)

------------------
-- Unit testing --
------------------

unitTests :: Spec
unitTests = do
  describe "Concept expansion with" $ do
    it "expanded TBox should be correct" $
      expandTBox familyTBox `shouldBe` expandedFamilyTBox
    it "empty TBox should return the same concept" $ do
      let t = Atomic "A"
          sampleTBox = M.empty
      expandConcept sampleTBox t `shouldBe` t
    it "a single definition should get expanded" $ do
      let sampleTBox = M.fromList [(Atomic "A", Disjunction (Atomic "B") (Atomic "C"))]
      expandConcept sampleTBox (sampleTBox M.! Atomic "A") `shouldBe` Disjunction (Atomic "B") (Atomic "C")
    it "many definitions should get expanded till the end" $ do
      let sampleTBox = M.fromList
             [ (Atomic "A", Disjunction (Atomic "B") (Atomic "C"))
             , (Atomic "B", Not (Atomic "D"))
             , (Atomic "C", Not (Atomic "E"))
             , (Atomic "D", Conjunction (Atomic "F") (Atomic "C"))]
      expandConcept sampleTBox (sampleTBox M.! Atomic "A") `shouldBe`
        Disjunction
          (Not (Conjunction (Atomic "F") (Not (Atomic "E"))))
          (Not (Atomic "E"))

  describe "CGI assertion" $ do
    it "that a vegan is always vegeterian should hold" $
      isProvable veganIsVegeterian (M.fromList [veganClass, vegeterianClass]) `shouldBe` True

    it "that a vegeterian is always vegan should not hold" $
      isProvable vegeterianIsVegan (M.fromList [veganClass, vegeterianClass]) `shouldNotBe` True

    it "that a vegeterian and a vegan are the same should not hold" $
      isProvable vegeterianEqualsVegan (M.fromList [veganClass, vegeterianClass]) `shouldNotBe` True

    it "that a vegeterian and a vegan have nothing in common should not hold" $
      isProvable vegeterianDisjointVegan (M.fromList [veganClass, vegeterianClass]) `shouldNotBe` True

--  describe "Concept assertion" $ do

--
--  |||||||      
--  |||||||unitTests :: Spec
--  |||||||unitTests = 
--  |||||||  describe "The assertion" $ do
--  |||||||    it "with Exists should terminate" $ 
--  |||||||      isValidModel [simpleExistsCGI] [] `shouldBe` True
--  |||||||      
--  |||||||--    it "that a human has at least one human parentR should hold" $
--  |||||||--      pPrint (isValidModelS [humanCGI, humanHasHumanParent] []) `shouldBe` ""
--  |||||||
--  |||||||    it "that invalidates 'implies' should not hold" $
--  |||||||      isValidModel [cgiA, cgiB, cgiC] [] `shouldNotBe` True
--  |||||||
--  |||||||    it "of exampleD should not hold" $
--  |||||||      isProvable exampleD [] [] `shouldNotBe` True
--  |||||||  
--  |||||||-- AtMost: not implemented yet
--  |||||||--    it "of exampleE should hold" $
--  |||||||--      isProvable exampleE [] [] `shouldBe` True
--  |||||||--  
--  |||||||--    it "temp: of exampleE should not hold" $
--  |||||||--      pPrint (isProvableS exampleE [] []) `shouldBe` ""
--  |||||||
--  |||||||--    it "with >=nC && <=(n-1)C should not be valid" $
--  |||||||--      isValidModel (SimpleCGI <$> [exFconcept1, exFconcept2]) [] `shouldNotBe` True