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


spec :: Spec
spec = 
  describe "inverse" $ 
    context "when inversed" $ 
      it "is like id" $ property $
        \x -> (inverse . inverse) (toDNF x) == (x :: Concept)


vegan, person, vegeterian, plant, diary :: Concept
vegan      = Atomic "vegan"
person     = Atomic "person"
vegeterian = Atomic "vegeterian"
plant      = Atomic "plant"
diary      = Atomic "diary"

eats :: Role
eats = Role "eats"

cgis :: [CGI]
cgis = let
         a = Equivalent vegan (Conjunction person (ForAll eats plant))
         b = Equivalent vegeterian (Conjunction person (ForAll eats (Disjunction plant diary)))
       in [a,b]

