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
    oneof . fmap pure $ [atm, nt] --[conj] --, dis, nt, impl, ifif, atl, fora, atm]
     
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
veganClass = Equivalent vegan (Conjunction person (ForAll eats plant))

vegetarianClass :: CGI
vegetarianClass = Equivalent vegeterian (Conjunction person (ForAll eats (Disjunction plant diary)))

vegeterianIsVegan :: CGI
vegeterianIsVegan = Subsumes vegan vegeterian

veganIsVegeterian :: CGI
veganIsVegeterian = Subsumes vegeterian vegan 

testState :: TableauxState
testState = initialState {
    _frontier = [CAssertion x initialIndividual | x <- asrts] -- [CAssertion (toDNF asrts) initialIndividual]
  , _intrp    = []
  , _inds     = [initialIndividual]
  , _status   = Active
  , _roles    = []
  , _indRoles = []
  , _uniq     = uniqueIdentifierPool
  }
 where
  --asrts = fmap (toDNF . cgiToConcept) [veganClass, vegetarianClass, veganIsVegeterian]
  asrts = fmap (toDNF . cgiToConcept) [veganClass] --, vegetarianClass, vegeterianIsVegan]

----------------------
-- Property testing --
----------------------

spec :: Spec
spec = do
  props
  unitTests

props :: Spec
props = 
  describe "inverse" $ 
    it "when inversed is like id" $
      property $ \x -> (inverse . inverse) (toDNF x) == toDNF (x :: Concept)

unitTests :: Spec
unitTests = 
  describe "Model" $ do
    it "should not exist" $
      modelExists testState `shouldBe` show testState
------------------
-- Unit testing --
------------------

