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
      atl  = AtLeast r1 c1
      fora = ForAll r1 c1
      atm  = Atomic lbl
    oneof . fmap pure $ [atm, nt]  -- conj, dis, nt, impl, ifif, atl, fora, atm]
                                  -- NOTE: not included otherwise property test never ends 
     
instance Arbitrary Role where
  arbitrary = Role <$> arbitrary


-------------------------
-- Auxiliary functions --
-------------------------

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

testState :: TableauxState
testState = initialState {
    _frontier = [CAssertion x initialIndividual | x <- asrts]
  , _intrp    = []
  , _inds     = [initialIndividual]
  , _status   = Active
  , _roles    = []
  , _indRoles = []
  , _uniq     = uniqueIdentifierPool
  }
 where
  asrts = fmap (toDNF . cgiToConcept) [veganClass, vegeterianClass]

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
  describe "Assertion" $ do
    it "Vegan is always vegeterian should hold" $
      isProvable veganIsVegeterian testState `shouldBe` True

    it "Vegeterian is always vegan should not hold" $
      isProvable vegeterianIsVegan testState `shouldNotBe` True

