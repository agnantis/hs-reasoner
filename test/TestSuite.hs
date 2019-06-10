{-# OPTIONS_GHC -fno-warn-orphans #-}
module Main (main) where

import           Test.Framework                       (Test, defaultMain,
                                                       testGroup)
import           Test.Framework.Providers.HUnit
import           Test.Framework.Providers.QuickCheck2 (testProperty)

import           Test.HUnit                           hiding (Test)
import           Test.QuickCheck
import           Test.QuickCheck.Gen
import           Test.QuickCheck.Random               (mkQCGen)

import           Control.Monad
import           Control.Monad.State
import           Data.Maybe                           (isJust, isNothing)
import qualified Data.Set                             as Set
--import           System.Random

import           ReasonerADT
import           Tableaux
import           Internal.Utils
import           ReasonerAPI                           as API
--import           Examples
--import           Debug.Trace

----------------------------- Helpers  -------------------------------------
instance Arbitrary Concept where
    arbitrary =
        oneof   [ liftM  AtomicConcept arbitraryString
                , liftM  NotConcept arbitrary
                , liftM2 UConcept arbitrary arbitrary
                , liftM2 IConcept arbitrary arbitrary
                , return TopConcept
                -- , return BottomConcept
                ]

-- Helper newtype to override (Arbitrary MyChar) behaviour
newtype MyChar = MyChar Char
instance Arbitrary MyChar where
    arbitrary = elements (map MyChar ['A'..'Z'])

arbitraryString :: Gen String
arbitraryString = do
    times   <- choose (3,7)
    myChars <- replicateM times (arbitrary::Gen MyChar)
    return $ liftM (\(MyChar x) -> x) myChars

----------------------------- HUnit tests ----------------------------------


randomList :: Int -> [Int]
randomList seed = unGen func (mkQCGen seed) 10
    where   func :: Gen [Int]
            func = do
                size <- choose (20, 35)
                replicateM size arbitrary


test1 :: Assertion
test1 =
    assertBool "Reverse list contains the same elements" $ xs `equalsAsSets` reverse xs
        where xs = randomList 20

test2 :: Assertion
test2 =
    assertBool "Different lists contains some different elements" $ not (xs `equalsAsSets` (5:xs))
      where xs = randomList 20


-- example atomic Conceptes
clsA, clsB, clsC, clsD, clsE, clsF :: Concept
clsA = AtomicConcept "A"
clsB = AtomicConcept "B"
clsC = AtomicConcept "C"
clsD = AtomicConcept "D"
clsE = AtomicConcept "E"
clsF = AtomicConcept "F"

-- example roles
rlR :: Role
rlR = AtomicRole "R"

--example individuals
indA, indB, indC, indD, indE :: Individual
indA = Ind "a"
indB = Ind "b"
indC = Ind "c"
indD = Ind "d"
indE = Ind "e"
--indF = Ind "f"
--indG = Ind "g"

-- concept/role/assertion complement tests
testC1, testC2, testC3, testC4, testC5, testC6, testC7, testC8 :: Assertion
test63, test64, test65, test66, test67, test68, test69, test70 :: Assertion

testC1 = assertBool "" $ isComplement (AtLeast 3 rlR clsA) (AtMost 2 rlR clsA)
testC2 = assertBool "" $ isComplement (AtLeast 3 rlR clsA) (AtMost 1 rlR clsA)
testC3 = assertBool "" $ not $ isComplement (AtLeast 3 rlR clsA) (AtMost 3 rlR clsA)
testC4 = assertBool "" $ not $ isComplement (AtLeast 3 rlR clsA) (AtMost 4 rlR clsA)
testC5 = assertBool "" $ isComplement (AtMost 2 rlR clsA) (AtLeast 3 rlR clsA)
testC6 = assertBool "" $ isComplement (AtMost 1 rlR clsA) (AtLeast 3 rlR clsA)
testC7 = assertBool "" $ not $ isComplement (AtMost 3 rlR clsA) (AtLeast 3 rlR clsA)
testC8 = assertBool "" $ not $ isComplement (AtMost 4 rlR clsA) (AtLeast 3 rlR clsA)

test63 = assertBool "" $ isComplementA  (CAssertion (AtLeast 3 rlR clsA) indA)
                                        (CAssertion (AtMost 2 rlR clsA) indA)
test64 = assertBool "" $ isComplementA  (CAssertion (AtLeast 3 rlR clsA) indA)
                                        (CAssertion (AtMost 1 rlR clsA) indA)
test65 = assertBool "" $ not $ isComplementA    (CAssertion (AtLeast 3 rlR clsA) indA)
                                                (CAssertion (AtMost 3 rlR clsA) indA)
test66 = assertBool "" $ not $ isComplementA    (CAssertion (AtLeast 3 rlR clsA) indA)
                                                (CAssertion (AtMost 4 rlR clsA) indA)
test67 = assertBool "" $ isComplementA  (CAssertion (AtMost 2 rlR clsA) indA)
                                        (CAssertion (AtLeast 3 rlR clsA) indA)
test68 = assertBool "" $ isComplementA  (CAssertion (AtMost 1 rlR clsA) indA)
                                        (CAssertion (AtLeast 3 rlR clsA) indA)
test69 = assertBool "" $ not $ isComplementA    (CAssertion (AtMost 3 rlR clsA) indA)
                                                (CAssertion (AtLeast 3 rlR clsA) indA)
test70 = assertBool "" $ not $ isComplementA    (CAssertion (AtMost 4 rlR clsA) indA)
                                                (CAssertion (AtLeast 3 rlR clsA) indA)

test1a, test1b, test2a, test2b, test3a, test3b, test4a, test4b, test5a :: Assertion
model1, model2, model3, model4, model5, model6 :: Concept

model1t, model2t, model3t, model4t, model5t, model6t :: TBox
model1t = convert2TBox model1
model2t = convert2TBox model2
model3t = convert2TBox model3
model4t = convert2TBox model4
model5t = convert2TBox model5
model6t = convert2TBox model6


-- [A⊓B, ¬C, A⊓D]
model1 = createIntersection [IConcept clsA clsB, NotConcept clsC, IConcept clsA clsD]
test1a = assertBool "" $ hasModel model1t []
test1b = assertBool "" $ isJust $ findModel model1t []

-- [A⊓B, ¬C, ¬A⊔D]
model2 = createIntersection [IConcept clsA clsB, NotConcept clsC, UConcept (NotConcept clsA) clsD]
test2a = assertBool "" $ hasModel model2t []
test2b = assertBool "" $ isJust $ findModel model2t []

-- [A⊓B, ¬C, ¬A⊓D]
model3 = createIntersection [IConcept clsA clsB, NotConcept clsC, IConcept (NotConcept clsA) clsD]
test3a = assertBool "" $ not $ hasModel model3t []
test3b = assertBool "" $ isNothing $ findModel model3t []

-- [A⊓B, ¬C, ¬A⊔(¬B⊓D)]
model4 = createIntersection [IConcept clsA clsB, NotConcept clsC, UConcept (NotConcept clsA) (IConcept (NotConcept clsB) clsD)]
test4a = assertBool "" $ not $ hasModel model4t []
test4b = assertBool "" $ isNothing $ findModel model4t []

-- [A⊓B, ¬C, E⊔D]
model5 = createIntersection [IConcept clsA clsB, NotConcept clsC, UConcept clsE clsD]
test5a = assertBool "" $ hasModel model5t []

-- [A⊓B, ¬C, A⊓D, ∃R.C]
model6 = createIntersection [IConcept clsA clsB, NotConcept clsC, IConcept clsA clsD, Exists rlR clsC]
abox1 :: ABox
abox1 = [RAssertion rlR indC indA, CAssertion clsC indA]

--- test with ABox ---
convert2TBox :: Concept -> TBox
convert2TBox c = [SubConcept TopConcept c]


test10, test11, test12, test13, test14 :: Assertion
test10 = assertBool "" $       hasModel model1t []
test11 = assertBool "" $       hasModel model2t []
test12 = assertBool "" $ not $ hasModel model3t []
test13 = assertBool "" $ not $ hasModel model4t []
test14 = assertBool "" $       hasModel model5t []

-- test exists constructor
test15, test16 :: Assertion
test15 = assertBool "" $ not $ hasModel model6t []
test16 = assertBool "" $ not $ hasModel model6t abox1

-- test for allconstructor
intrp1 :: Set.Set LAssertion -- Interpretation
intrp1 =  Set.fromList  [CAssertion clsA indB       -- A(b)
                        ,CAssertion clsC indB       -- C(b)
                        ,RAssertion rlR indA indB   -- R(a,b)
                        ,RAssertion rlR indA indC   -- R(a,c)
                        ,RAssertion rlR indC indA   -- R(c,a)
                        ,RAssertion rlR indC indB   -- R(c,b)
                        ]

createIntrp :: Set.Set LAssertion -> Interpretation
createIntrp = Set.map (\i -> (Set.empty, i))

createState :: Interpretation -> ModelState
createState intr = newTableaux{i12n=intr}

createState' :: Set.Set LAssertion -> ModelState
createState' intr = newTableaux{i12n=createIntrp intr}

test17, test18, test19, test20, test21, test22, test23 ::Assertion
test17 = assertEqual "" toBeAdded [CAssertion clsC indC]
    where toBeAdded = seconds $ evalState (forAllRuleAdditions clsC rlR indA) (createState' intrp1)

test18 = assertEqual "" toBeAdded [CAssertion clsB indA, CAssertion clsB indB]
    where toBeAdded = seconds $ evalState (forAllRuleAdditions clsB rlR indC) (createState' intrp1)

test19 = assertBool "" $ hasModel [] (Set.toList intrp1)
test20 = assertBool "" $ hasModel (convert2TBox (ForAll rlR clsB)) (Set.toList intrp1)

--findModel TopConcept $ (Set.toList intrp1) ++[CAssertion (NotConcept clsB) indB,CAssertion (ForAll rlR clsB) indA]
test21 = assertBool "" $ not $ hasModel [] abox
    where abox = Set.toList intrp1 ++
                    [CAssertion (ForAll rlR clsB) indA
                    ,CAssertion (NotConcept clsB) indB
                    ]
test22 = assertBool "" $ not $ hasModel [] abox
    where abox = Set.toList intrp1 ++
                    [CAssertion (NotConcept clsB) indB
                    ,CAssertion (ForAll rlR clsB) indA
                    ]

test23 = assertBool "" $ not $ hasModel [] abox
    where abox =    CAssertion (NotConcept clsB) indB
                    :CAssertion (ForAll rlR clsB) indA
                    :Set.toList intrp1

test24, test25, test26 :: Assertion
test24 = assertBool "" $ evalState Tableaux.isConsistent (createState' intrp1)
test25 = assertBool "" $ not $ evalState Tableaux.isConsistent (createState' intrp1')
    where intrp1' = Set.insert (CAssertion (NotConcept clsC) indB) intrp1
test26 = assertBool "" $ not $ evalState Tableaux.isConsistent (createState' intrp1')
    where intrp1' = Set.insert (RAssertion (NotRole rlR) indA indC) intrp1

-- AtLeast tests
test27,test28, test29, test30, test31, test32 :: Assertion
test27 = assertEqual "" 3 (length fillers)
    where   abox = Set.toList intrp1 ++  [CAssertion (AtLeast 3 rlR clsB) indA]
            mdl' = findModel [] abox
            findFillers s' = evalState (findRoleFillers clsB rlR indA) (createState s')
            fillers = maybe [] findFillers mdl'

test28 = assertBool "" $ length fillers >= 3
    where   abox = CAssertion (AtLeast 3 rlR clsB) indA:Set.toList intrp1
            mdl' = findModel [] abox
            findFillers s' = evalState (findRoleFillers clsB rlR indA) (createState s')
            fillers = maybe [] findFillers mdl'

test29 = assertEqual "" 3 (length fillers)
    where   abox = Set.toList intrp1 ++  [CAssertion (AtLeast 3 rlR clsC) indA]
            mdl' = findModel [] abox
            findFillers s' = evalState (findRoleFillers clsC rlR indA) (createState s')
            fillers = maybe [] findFillers mdl'

test30 = assertBool "" $ length fillers >= 3
    where   abox = CAssertion (AtLeast 3 rlR clsC) indA:Set.toList intrp1
            mdl' = findModel [] abox
            findFillers s' = evalState (findRoleFillers clsC rlR indA) (createState s')
            fillers = maybe [] findFillers mdl'

test31 = assertEqual "" 2 (length fillers)
    where   abox = Set.toList intrp1 ++  [CAssertion clsC indC,CAssertion (AtLeast 2 rlR clsC) indA]
            mdl' = findModel [] abox
            findFillers s' = evalState (findRoleFillers clsC rlR indA) (createState s')
            fillers = maybe [] findFillers mdl'

test32 = assertBool "" $ length fillers >= 2
    where   abox = CAssertion clsC indC:CAssertion (AtLeast 2 rlR clsC) indA:Set.toList intrp1
            mdl' = findModel [] abox
            findFillers s' = evalState (findRoleFillers clsC rlR indA) (createState s')
            fillers = maybe [] findFillers mdl'

--roleFillers c r i = evalState (findRoleFillers c r i) (createState . head $ mdl')
-- at most rule tests
test33, test34, test35, test36, test37, test38 ::Assertion
intrp2, intrp3, intrp4, intrp5 :: Set.Set LAssertion
intrp2 =  Set.fromList  [CAssertion clsC indB       -- C(b)
                        ,CAssertion clsC indC       -- C(c)
                        ,CAssertion clsC indD       -- C(d)
                        ,RAssertion rlR indA indB   -- R(a,b)
                        ,RAssertion rlR indA indC   -- R(a,c)
                        ,RAssertion rlR indA indD   -- R(a,d)
                        ]

intrp3 =  Set.fromList  [CAssertion clsC indB               -- C(b)
                        ,CAssertion clsC indC               -- C(c)
                        ,RAssertion rlR indA indB           -- R(a,b)
                        ,RAssertion rlR indA indC           -- R(a,c)
                        ,CAssertion clsA indC               -- A(c)
                        ,CAssertion (NotConcept clsA) indB  -- notA(b)
                        ]

intrp4 = intrp3 `Set.union` Set.fromList
            [CAssertion clsC indD               -- C(d)
            ,RAssertion rlR indA indD           -- R(a,d)
            ]

intrp5 = intrp2 `Set.union` Set.fromList
            [RAssertion rlR indA indE   -- R(a,e)
            ,CAssertion clsC indE       -- C(e)
            ]

test33 = assertEqual "" 2 (length fillers)
    where   abox = Set.toList intrp2 ++ [CAssertion (AtMost 2 rlR clsC) indA]
            mdl' = findModel [] abox
            findFillers s' = evalState (findRoleFillers clsC rlR indA) (createState s')
            fillers = maybe [] findFillers mdl'

test34 = assertEqual "" 2 (length fillers)
    where   abox = CAssertion (AtMost 2 rlR clsC) indA:Set.toList intrp2
            mdl' = findModel [] abox
            findFillers s' = evalState (findRoleFillers clsC rlR indA) (createState s')
            fillers = maybe [] findFillers mdl'

test35 = assertBool "" $ not $ hasModel [] abox
    where   abox = Set.toList intrp3 ++ [CAssertion (AtMost 1 rlR clsC) indA]

test36 = assertBool "" $  hasModel [] abox
    where   abox = Set.toList intrp4 ++ [CAssertion (AtMost 2 rlR clsC) indA]

test37 = assertBool "" $  not $ hasModel [] abox
    where   abox = Set.toList intrp4 ++ [CAssertion (AtMost 1 rlR clsC) indA]

test38 = assertBool "" $  length fillers == 1
    where   abox = Set.toList intrp5 ++ [CAssertion (AtMost 1 rlR clsC) indA]
            mdl' = findModel [] abox
            findFillers s' = evalState (findRoleFillers clsC rlR indA) (createState s')
            fillers = maybe [] findFillers mdl'

----------- test rules list ------------
test42, test43, test44, test45, test46, test47, test48 :: Assertion
test42 = assertEqual "" 0 rulzNo
    where   mdl'    = findModelDbg [] (Set.toList intrp1)
            rulzNo  = either (\_ -> (-1)) (Set.size . rules) mdl'

test43 = assertEqual "" 1 rulzNo
    where   abox = CAssertion (Exists rlR clsD) indA:Set.toList intrp1
            mdl' = findModelDbg [] abox
            rulzNo  = either (\_ -> (-1)) (Set.size . rules) mdl'

test44 = assertEqual "" 4 rulzNo
    where   abox =   CAssertion (Exists rlR clsD) indA
                    :CAssertion (AtMost 3 rlR clsD) indA
                    :CAssertion (AtLeast 2 rlR clsD) indA
                    :CAssertion (ForAll rlR clsD) indA
                    :Set.toList intrp1
            mdl' = findModelDbg [] abox
            rulzNo  = either (\_ -> (-1)) (Set.size . rules) mdl'

test45 = assertBool "" $ not $ hasModel [] abox
    where   abox =   CAssertion (AtLeast 3 rlR clsD) indA
                    :CAssertion (AtMost 2 rlR clsD) indA
                    :Set.toList intrp1

test46 = assertBool "" $ not $ hasModel tbox []
    where   tbox =   convert2TBox $ IConcept (AtLeast 3 rlR clsD) (AtMost 2 rlR clsD)

test47 = assertBool "" $ not $ hasModel [] abox
    where   abox =   CAssertion (AtMost 2 rlR clsD) indA
                    :CAssertion (AtLeast 3 rlR clsD) indA
                    :Set.toList intrp1

test48 = assertBool "" $ not $ hasModel tbox []
    where   tbox =   convert2TBox $ IConcept (AtMost 2 rlR clsD) (AtLeast 3 rlR clsD)

-- test cgi
ttbox, ttbox' :: TBox
ttbox = [SubConcept clsA clsB, SuperConcept clsD clsC, EqualConcept clsE clsF]
ttbox' = [SubConcept clsF clsE, SubConcept clsA clsB, SubConcept clsC clsD, SubConcept clsE clsF]
ttbox'' :: [Concept]
ttbox'' =   [UConcept (NotConcept clsF) clsE, UConcept (NotConcept clsA) clsB
            ,UConcept (NotConcept clsC) clsD, UConcept (NotConcept clsE) clsF]

test49,test50 :: Assertion
test49 = assertBool "" $ equalsAsSets ttbox' (normTBox ttbox)

test50 = assertBool "" $ equalsAsSets ttbox'' (deriveConcepts ttbox)

------ test complements ------
test60, test61, test62 :: Assertion
test60 = assertBool "" $ isComplement c1 c2
    where   c1 = UConcept clsA clsB
            c2 = IConcept (NotConcept clsA) (NotConcept clsB)

test61 = assertBool "" $ isComplement c1 c2
    where   c1 = IConcept clsA clsB
            c2 = UConcept (NotConcept clsA) (NotConcept clsB)

test62 = assertBool "" $ isComplement c1 c2
    where   c1 = UConcept clsA clsB
            c2 = IConcept (NotConcept clsB) (NotConcept clsA)

------ test (in)equality assertions ------
test71, test72, test73, test74, test75, test76 :: Assertion

test71 = assertBool "" $ null $ filteredPairs ineqs prs
    where   ineqs   =   [(indA, indB)]
            prs     =   [(indA, indB)]

test72 = assertBool "" $ null $ filteredPairs ineqs prs
    where   ineqs   =   [(indA, indB)]
            prs     =   [(indB, indA)]

test73 =  assertBool "" intrp
    where   intrp       =   hasModel' [] abox equalInds
            equalInds   =   [(indA, indC), (indC, indD)]
            abox        =   [RAssertion rlR indA indB
                            ,CAssertion clsC indB
                            ,CAssertion clsD indA
                            ,CAssertion clsD indD
                            ]

test74 = assertBool "" $ hasModel tbox abox
    where   tbox    =   convert2TBox $ AtMost 1 rlR clsC
            abox    =   [RAssertion rlR indA indB
                        ,RAssertion rlR indA indD
                        ,CAssertion clsC indB
                        ,CAssertion clsC indD
                        ]

test75 = assertBool "" $ not $ hasModel tbox abox
    where   tbox    =   convert2TBox $ AtMost 1 rlR clsC
            abox    =   [RAssertion rlR indA indB
                        ,RAssertion rlR indA indD
                        ,CAssertion clsC indB
                        ,CAssertion clsC indD
                        ,InEqAssertion indB indD
                        ]

test76 = assertBool "" $  hasModel tbox abox
    where   tbox    =   convert2TBox $ AtMost 2 rlR clsC
            abox    =   [RAssertion rlR indA indB
                        ,RAssertion rlR indA indC
                        ,RAssertion rlR indA indD
                        ,CAssertion clsC indB
                        ,CAssertion clsC indC
                        ,CAssertion clsC indD
                        ,InEqAssertion indB indD
                        ]

test77, test78 :: Assertion
test77 = assertBool "" $ hasModel tbox abox
    where   tbox    =   convert2TBox $ ExistsSelf rlR
            abox    =   []

test78 = assertBool "" $ not $ hasModel tbox abox
    where   tbox    =   convert2TBox $ IConcept (ExistsSelf rlR) (ForAll rlR clsC)
            abox    =   [CAssertion (NotConcept clsC) indA]


--------- test individual substitutions list of a model state --------
test79, test80 :: Assertion
test79 = assertEqual "" 2 subsNo
    where   tbox    =   convert2TBox $ AtMost 1 rlR clsC
            abox    =   [RAssertion rlR indA indB
                        ,RAssertion rlR indA indC
                        ,RAssertion rlR indA indD
                        ,CAssertion clsC indB
                        ,CAssertion clsC indC
                        ,CAssertion clsC indD
                        ]
            subsNo  =   either (\_ -> (-1)) (length . iSubs) $ findModelDbg tbox abox

test80 = assertBool "" $ either (\_ -> False) (not . null . iSubs) mdl'
    where   tbox    =   convert2TBox $ AtMost 1 rlR clsC
            abox    =   [RAssertion rlR indA indB
                        ,RAssertion rlR indA indC
                        ,RAssertion rlR indA indD
                        ,CAssertion clsC indB
                        ,CAssertion clsC indC
                        ,CAssertion clsC indD
                        ]
            mdl'    =  findModelDbg tbox abox

---------- test AtMost AtLeast combinations
test81, test82 :: Assertion

test81 = assertBool "" $ hasModel tbox abox
    where   tbox    =   convert2TBox $ IConcept (AtMost 2 rlR clsC) (AtLeast 2 rlR clsC)
            abox    =   [RAssertion rlR indA indB]

test82 = assertBool "" $ not $ hasModel tbox abox
    where   tbox    =   convert2TBox $ IConcept (Exists rlR clsC) (NotConcept clsC)
            abox    =   []

----------------- Test blocking ----------------
test83, test84, test85, test86, test87 :: Assertion
test83 = assertBool "" $ precedes 1 3 ([1,2,3,4,5] ::[Int])
test84 = assertBool "" $ not $ precedes 3 1 ([1,2,3,4,5]::[Int])
test85 = assertBool "" $ precedes 1 6 ([1,2,3,4,5]::[Int])
test86 = assertBool "" $ not $ precedes 7 3 ([1,2,3,4,5]::[Int])
test87 = assertBool "" $ not $ precedes 7 8 ([1,2,3,4,5]::[Int])

test88, test89, test90, test91, test92, test93, test94, test95, test96, test97 :: Assertion
test88 = assertBool "" isBlocked'
    where   intrp   = Set.fromList  [CAssertion clsC indA
                                    ,CAssertion clsB indA
                                    ,CAssertion clsC indB
                                    ]
            maybeInd    = evalState (blockedBy indB) newTableaux{i12n=createIntrp intrp, indv=[indB,indA]}
            isBlocked'  = maybe False (==indA) maybeInd

test89 = assertBool "" isBlocked'
    where   intrp   = Set.fromList  [CAssertion clsC indA
                                    ,CAssertion clsB indA
                                    ,CAssertion clsC indB
                                    ,CAssertion clsB indB
                                    ]
            maybeInd    = evalState (blockedBy indB) newTableaux{i12n=createIntrp intrp, indv=[indB,indA]}
            isBlocked'  = maybe False (==indA) maybeInd

test90 = assertBool "" $ not isBlocked'
    where   intrp   = Set.fromList  [CAssertion clsC indA
                                    ,CAssertion clsB indA
                                    ,CAssertion clsC indB
                                    ,CAssertion clsB indB
                                    ,CAssertion clsA indB
                                    ]
            maybeInd    = evalState (blockedBy indB) newTableaux{i12n=createIntrp intrp, indv=[indB,indA]}
            isBlocked'  = maybe False (==indA) maybeInd

test91 = assertBool "" $ not isBlocked'
    where   intrp   = Set.fromList  [CAssertion clsC indA
                                    ,CAssertion clsB indA
                                    ,CAssertion clsC indB
                                    ,CAssertion clsB indB
                                    ]
            maybeInd    = evalState (blockedBy indA) newTableaux{i12n=createIntrp intrp, indv=[indB,indA]}
            isBlocked'  = maybe False (==indB) maybeInd


-- TBox = T ⊑ ∃R.A
-- ABox = {A(a)}
test92 = assertEqual "" (1+1) indNo  -- indA, -blocks-> newindX,
    where   abox    = [CAssertion clsA indA] --, CAssertion (Exists rlR clsA) indA]
            mdl'    = findModelDbg (convert2TBox $ Exists rlR clsA) abox
            indNo   = either (\_ -> (-1)) (length . indv) mdl'

-- TBox = T ⊑ ∃R.A
-- ABox = {A(a), (∃R.A)(a)}
test93 = assertEqual "" 3 indNo  -- indA, -blocks-> {x1, x2} (from tbox/abox)
    where   abox    = [CAssertion clsA indA, CAssertion (Exists rlR clsA) indA]
            mdl'    = findModelDbg (convert2TBox $ Exists rlR clsA) abox
            indNo   = either (\_ -> (-1)) (length . indv) mdl'

a0, a1, a2, a3, a4, b1, b2, b3, b4 :: Individual
a0 = Ind "a0"
a1 = Ind "a1"
a2 = Ind "a2"
a3 = Ind "a3"
a4 = Ind "a4"
b1 = Ind "b1"
b2 = Ind "b2"
b3 = Ind "b3"
b4 = Ind "b4"


-- OR-Branching
test94 = assertBool "" $ not $ hasModel tbox abox
    where   tbox = [SubConcept (Exists rlR clsA) clsA]
            abox = [CAssertion (NotConcept clsA) a0
                   ,RAssertion rlR a0 b1,  RAssertion rlR b1 a1
                   ,RAssertion rlR a1 b2,  RAssertion rlR b2 a2
                   ,RAssertion rlR a2 b3,  RAssertion rlR b3 a3
                   ,RAssertion rlR a3 b4,  RAssertion rlR b4 a4
                   ,CAssertion clsA a4
                   ]

clsA1, clsA2, clsA3, clsA4 :: Concept
clsB1, clsC1, clsB2, clsC2, clsB3, clsC3, clsB4, clsC4 :: Concept
clsA1 = AtomicConcept "A1"
clsA2 = AtomicConcept "A2"
clsA3 = AtomicConcept "A3"
clsA4 = AtomicConcept "A4"
clsC1 = AtomicConcept "C1"
clsB1 = AtomicConcept "B1"
clsC2 = AtomicConcept "C2"
clsB2 = AtomicConcept "B2"
clsC3 = AtomicConcept "C3"
clsB3 = AtomicConcept "B3"
clsC4 = AtomicConcept "C4"
clsB4 = AtomicConcept "B5"

_createBox :: Int -> Int -> TBox
_createBox n m =    map mapper1 [1..n-1] ++
                    [SubConcept (createC 'A' n) (createC 'A' 1)] ++
                    map (mapper2 m) [1..n]
    where
            mapper1 i       = SubConcept (createC 'A' i) (AtLeast 2 rlR (createC 'A' (i+1)))
            mapper2 m' i    = SubConcept (createC 'A' i) (helper m')
            helper 1        = UConcept (createC 'B' 1) (createC 'C' 1)
            helper n'       = IConcept (helper $ n'-1) (UConcept (createC 'B' n') (createC 'C' n'))
            createC :: Char -> Int -> Concept
            createC n' id'  = AtomicConcept $ n':show id'

-- AND-Brabching
-- see "Hypertableux reasoning for DL", p. 171
-- TODO: if I change the order of the tbox concepts...it becomes really slow (maybe non-terminated)
test95 = assertBool "" $ hasModel {-(_createBox 4 4) abox --} tbox abox
    where   tbox =  [SubConcept clsA1 (AtLeast 2 rlR clsA2)
                    ,SubConcept clsA2 (AtLeast 2 rlR clsA3) -- < move it here, and boom!!!
                    ,SubConcept clsA3 (AtLeast 2 rlR clsA4)
                    ,SubConcept clsA4 clsA1
                    ,SubConcept clsA1 subs -- < here lies the problem
                    ,SubConcept clsA2 subs
                    ,SubConcept clsA3 subs
                    ,SubConcept clsA4 subs
                    ]
            abox = [CAssertion clsA1 indA]
            subs = createIntersection   [UConcept clsB1 clsC1
                                        ,UConcept clsB2 clsC2
                                        ,UConcept clsB3 clsC3
                                        ,UConcept clsB4 clsC4
                                        ]


--- Test possible loop -> AtLeast -> AtMost
test96 = assertBool "" $ not $ hasModel tbox abox
    where   tbox =  []
            abox =  [CAssertion (AtLeast 3 rlR clsC) indA
                    ,CAssertion (AtMost  1 rlR clsC) indA
                    ]

-- Test cycles. See "Basic Description Logics", p. 92
-- Ao = {R(a,a), (∃R.A)(a), (≤1R.⊤)(a), (∀R.∃R.A)(a)}
test97 = assertBool "" $ hasModel tbox abox
    where   tbox =  []
            abox =  [RAssertion rlR indA indA
                    ,CAssertion (Exists rlR clsA) indA
                    ,CAssertion (AtMost 1 rlR TopConcept) indA
                    ,CAssertion (ForAll rlR (Exists rlR clsA)) indA
                    ]

test98, test99, test100, test101 :: Assertion
test98 = assertEqual "" c2 (toNNF c1)
    where   c1 = NotConcept $ Exists rlR $ IConcept clsA clsB
            c2 = ForAll rlR $ UConcept (NotConcept clsA) (NotConcept clsB)

test99 = assertEqual "" c2 (toNNF c1)
    where   c1 = NotConcept $ ForAll rlR $ IConcept clsA clsB
            c2 = Exists rlR $ UConcept (NotConcept clsA) (NotConcept clsB)

test100 = assertEqual "" c2 (toNNF c1)
    where   c1 = NotConcept $ ForAll rlR $ IConcept clsA (NotConcept clsB)
            c2 = Exists rlR $ UConcept (NotConcept clsA) clsB

test101 = assertEqual "" c2 (toNNF c1)
    where   c1 = NotConcept $ ForAll rlR $ IConcept clsA (NotConcept clsB)
            c2 = Exists rlR $ UConcept (NotConcept clsA) clsB

test102, test103 :: Assertion
test102 = assertBool "" $ not $ API.subsumedBy [] [] c1 c2
    where   c1  = IConcept (Exists rlR clsA) (Exists rlR clsB)
            c2  = Exists rlR (IConcept clsA clsB)

test103 = assertBool "" $ API.subsumedBy [] [] c1' c2
    where   c1  = IConcept (Exists rlR clsA) (Exists rlR clsB)
            c2  = Exists rlR (IConcept clsA clsB)
            c1' = IConcept c1 (AtMost 1 rlR TopConcept)


---------------------- Integrate HUint and QuickCheck ---------------------------
{-
main' :: IO ()
main' = do
    let abox = CAssertion (AtMost 2 rlR clsC) indA:CAssertion (NotConcept indB):Set.toList intrp2
        mdl = findModelDbg [] abox
    mapM_ print mdl
-}



main :: IO ()
main = defaultMain testAll

testAll :: [Test]
testAll =
  [
    testGroup "Basic Concept tests" [
      testProperty "Reversed lists are equal" (prop_equalSets::[Int] -> Bool),
      testProperty "¬¬C == C" prop_negnegConcept,
      testProperty "¬C == ¬C" prop_isComplement,
      testCase "HUnit tests" test1,
      testCase "HUnit tests" test2
    ],
    testGroup "Concept/Role complement tests" [
        testCase "1.\tAtLeast = 3, AtMost  = 2\t\t\t"      testC1,
        testCase "2.\tAtLeast = 3, AtMost  = 1\t\t\t"      testC2,
        testCase "3.\tAtLeast = 3, AtMost  = 3\t\t\t"      testC3,
        testCase "4.\tAtLeast = 3, AtMost  = 4\t\t\t"      testC4,
        testCase "5.\tAtMost  = 2, AtLeast = 3\t\t\t"      testC5,
        testCase "6.\tAtMost  = 1, AtLeast = 3\t\t\t"      testC6,
        testCase "7.\tAtMost  = 3, AtLeast = 3\t\t\t"      testC7,
        testCase "8.\tAtMost  = 4, AtLeast = 3\t\t\t"      testC8
    ],
    testGroup "Basic Model satisfiability tests with Tbox only" [
        testCase "9.\tSimple satisfiable model w/o Union\t\t"       test1a,
        testCase "10.\tReturns a non empty list of models\t\t"      test1b,
        testCase "11.\tSimple satisfiable model with Union\t\t"     test2a,
        testCase "12.\tReturns a non empty list of models\t\t"      test2b,
        testCase "13.\tSimple un-satisfiable model w/o Union\t\t"   test3a,
        testCase "14.\tReturns an empty list of models\t\t\t"       test3b,
        testCase "15.\tSimple un-satisfiable model w Union\t\t"     test4a,
        testCase "16.\tReturns an empty list of models\t\t\t"       test4b,
        testCase "17.\tSatisfiable model with two models\t\t"       test5a
    ],
    testGroup "Basic Model satisfiability tests with Abox" [
        testCase "19.\tSimple satisfiable model w/o Union\t\t"      test10,
        testCase "20.\tSimple satisfiable model with Union\t\t"     test11,
        testCase "21.\tSimple un-satisfiable model w/o Union\t\t"   test12,
        testCase "22.\tSimple un-satisfiable model w Union\t\t"     test13,
        testCase "23.\tSatisfiable model with two models\t\t"       test14
    ],
    testGroup "Model satisfiability tests with Exists constructor" [
        testCase "25.\tSimple Exists constructor\t\t\t"            test15,
        testCase "26.\tSimple Exists constructor with Abox\t\t"    test16
    ],
    testGroup "Model satisfiability tests with ForAll constructor" [
        testCase "27.\tApply for all rule \t\t\t\t"                test17,
        testCase "28.\tApply for all rule \t\t\t\t"                test18,
        testCase "29.\tModel with only ABox\t\t\t\t"               test19,
        testCase "30.\tForAll constr at the end of ABox\t\t"       test20,
        testCase "31.\tForAll constr at the end of ABox\t\t"       test21,
        testCase "32.\tForAll constr at the end of ABox\t\t"       test22,
        testCase "33.\tForAll constr at the begining of ABox\t\t"  test23
    ],
    testGroup "Test consistency helper functions"   [
        testCase "34.\tThe interpetation is consistent\t\t\t"          test24,
        testCase "35.\tThe interpetation is *not* consistent\t\t"      test25,
        testCase "36.\tThe interpetation is *not* consistent\t\t"      test26
    ],
    testGroup "Model statisfiability tests with AtLeast constructor" [
        testCase "37.\tAtLeast constr at the end of Abox\t\t"          test27,
        testCase "38.\tAtLeast constr at the begining of Abox\t\t"     test28,
        testCase "39.\tAtLeast constr at the end of Abox\t\t"          test29,
        testCase "40.\tAtLeast constr at the begining of Abox\t\t"     test30,
        testCase "41.\tAtLeast constr at the end of Abox\t\t"          test31,
        testCase "42.\tAtLeast constr at the begining of Abox\t\t"     test32
    ]
    ,
    testGroup "Model statisfiability tests with AtMost constructor" [
        testCase "43.\tAtMost constr at the end of Abox\t\t"           test33,
        testCase "44.\tAtMost constr at the begining of Abox\t\t"      test34,
        testCase "45.\tAtMost constr with no intrepretation\t\t"       test35,
        testCase "46.\tAtMost constr with intrepretation\t\t"          test36,
        testCase "47.\tAtMost constr with no intrepretation\t\t"       test37,
        testCase "48.\tAtMost constr with 3 substitutions\t\t"         test38
    ],
    testGroup "Tableaux should store rules" [
        testCase "51.\tNo rule in the tbox\t\t\t\t"                    test42,
        testCase "52.\tAtMost rule in the tbox\t\t\t\t"                test43,
        testCase "53.\t4 rules in the tbox\t\t\t\t"                    test44,
        testCase "54.\tAt least and then at most abox\t\t\t"           test45,
        testCase "55.\tAt least and then at most tbox\t\t\t"           test46,
        testCase "56.\tAt most and then at least abox\t\t\t"           test47,
        testCase "57.\tAt most and then at least tbox\t\t\t"           test48
    ],
    testGroup "TBox transformations" [
        testCase "58.\tNormalize TBox\t\t\t\t\t"                      test49,
        testCase "59.\tDerive concept assertions from a TBox\t\t"     test50
    ],
    testGroup "Test complement rules" [
        testCase "60.\tUnion NNF rule\t\t\t\t\t"                      test60,
        testCase "61.\tIntersection NNF rule\t\t\t\t"                 test61,
        testCase "62.\tUnion NNF rule with inversed positions\t\t"    test62
    ],
    testGroup "Assertion complement tests" [
        testCase "63.\tAtLeast = 3, AtMost  = 2\t\t\t"      test63,
        testCase "64.\tAtLeast = 3, AtMost  = 1\t\t\t"      test64,
        testCase "65.\tAtLeast = 3, AtMost  = 3\t\t\t"      test65,
        testCase "66.\tAtLeast = 3, AtMost  = 4\t\t\t"      test66,
        testCase "67.\tAtMost  = 2, AtLeast = 3\t\t\t"      test67,
        testCase "68.\tAtMost  = 1, AtLeast = 3\t\t\t"      test68,
        testCase "69.\tAtMost  = 3, AtLeast = 3\t\t\t"      test69,
        testCase "70.\tAtMost  = 4, AtLeast = 3\t\t\t"      test70
    ],
    testGroup "Test equality assertions" [
        testCase "71.\tFiltered pairs (1)\t\t\t\t"                      test71,
        testCase "72.\tFiltered pairs (2)\t\t\t\t"                      test72,
        testCase "73.\tRemove initial equality assertions\t\t"          test73,
        testCase "74.\tSatisfiable model w/o individual equalities\t"   test74,
        testCase "75.\tUnsatisfiable model w individual equalities\t"   test75,
        testCase "76.\tSatisfiable model w/o individual equalities\t"   test76
    ],
    testGroup "Test ∃S.Self local reflexivity" [
        testCase "77.\tSimplest ∃S.Self satisfiable model\t\t"      test77,
        testCase "78.\tSimplest ∃S.Self unsatisfiable model\t\t"    test78
    ],
    testGroup "Test individual substitutions list of a model state" [
        testCase "79.\tTwo individual substitutions\t\t\t"              test79,
        testCase "80.\tTwo individual substitutions for all models\t"   test80
    ],
    testGroup "Test AtMost/AtLeast peacefull co-existence" [
        testCase "81.\tAtMost = 2, AtLeast = 2, 1 Role Assertion\t"     test81
    ],
    testGroup "Test Bug with new individual additions" [
        testCase "82.\tThe model should be unsatisfiable\t\t"         test82
    ],
    testGroup "Test blocking mechanism" [
        testCase "83.\t1 is before 3 in [1,2,3,4,5]\t\t\t"              test83,
        testCase "84.\t3 is not before 1 in [1,2,3,4,5]\t\t"            test84,
        testCase "85.\t1 is before 6 in [1,2,3,4,5]\t\t\t"              test85,
        testCase "86.\t7 is not before 3 in [1,2,3,4,5]\t\t"            test86,
        testCase "87.\t7 is not before 8 in [1,2,3,4,5]\t\t"            test87,
        testCase "88.\tIndB is blocked by indA\t\t\t\t"                 test88,
        testCase "89.\tIndB is blocked by indA\t\t\t\t"                 test89,
        testCase "90.\tIndB is not blocked by indA\t\t\t"               test90,
        testCase "91.\tIndA is not blocked by indB (it's older)\t"      test91,
        testCase "92.\tExists TBox with block, only 1 new ind\t\t"      test92,
        testCase "93.\tExists TBox/Abox with block, only 1 new ind\t"   test93,
        testCase "94.\tScalability problems with OR-branching\t\t"      test94,
        testCase "95.\tScalability problems with AND-branching\t\t"     test95
    ],
    testGroup "Test rules application" [
        testCase "96.\tAtLeast - AtMost clash\t\t\t\t"              test96,
        testCase "97.\tExists - AtMost - ForAll termination\t\t"    test97

    ],
    testGroup "Test complex NNF" [
        testCase "98.\tNot-Exists combination\t\t\t\t"                  test98,
        testCase "99.\tNot-ForAll combination\t\t\t\t"                  test99,
        testCase "100.\tNot-Exists-Not combination\t\t\t"               test100,
        testCase "101.\tNot-ForAll-Not combination\t\t\t"               test101
    ],
    testGroup "Test hierarchy/classification" [
        testCase "102.\tConcept is not subsumed by other\t\t"           test102,
        testCase "103.\tConcept is subsumed by other\t\t\t"             test103
    ]
  ]


prop_equalSets :: Eq a => [a] -> Bool
prop_equalSets xs = xs `equalsAsSets` reverse xs

prop_negnegConcept :: Concept -> Bool
prop_negnegConcept c = (toNNF . complementC .complementC) c == toNNF c

prop_isComplement :: Concept -> Bool
prop_isComplement c = isComplement (complementC c) c

