{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Logic where

--import Prelude                        hiding (head, tail)

import           Control.Eff
import           Control.Eff.State.Lazy
import           Control.Eff.Writer.Lazy
import           Control.Monad                  (mapM_)
import           Data.Functor.Foldable          (cata, embed)
import           Data.Functor.Foldable.TH       (makeBaseFunctor)
import           Data.List                      (intercalate, intersect)
import qualified Data.Map.Strict                                    as M
import           Data.Maybe                     (isJust, isNothing, mapMaybe)
import           Lens.Micro.Platform

import Debug.Trace

type Label = String
newtype Individual = Individual Label deriving (Show, Eq)

newtype Role = Role Label deriving (Show, Eq, Ord)

data Concept
  = Conjunction Concept Concept -- ^ AND
  | Disjunction Concept Concept -- ^ OR
  | Not Concept                 -- ^ NOT
  | Implies Concept Concept     -- ^ A -> B
  | IfOnlyIf Concept Concept    -- ^ A <-> B
  | AtLeast Role Concept        -- ^ R.C
  | ForAll Role Concept         -- ^ R.C
  | Atomic Label deriving (Show, Eq, Ord)

makeBaseFunctor ''Concept

data CGI
  = Subsumes Concept Concept
  | Equivalent Concept Concept deriving (Show, Eq)

--type TBox = [CGI]

type UniRole = (Role, Concept) -- ^ Represents a ∀R.C (i.e. (R,C)
type IndRole = (Individual, Role) -- ^ Represents a filler of a role

  
data ClashException = ClashException Assertion Assertion deriving (Eq, Show)

data TableauxState = Tableaux
  { _frontier :: [Assertion] -- ^ Assertions to be expanded
  , _intrp    :: [Assertion] -- ^ The current interpretation
  , _inds     :: [Individual] -- ^ individuals in scope
  , _status   :: TableauxStatus -- ^ The state of the specific path
  , _roles    :: [UniRole] -- ^ It holds all visited universal role 
  , _indRoles :: [IndRole] -- ^ It holds all the filler individual
  , _uniq     :: [String] -- ^ A generator of uniq ids
  }

instance Show TableauxState where
  show Tableaux{..} = unlines 
    [ "frontier: " <> show _frontier
    , "Intrp:    " <> show _intrp
    , "Inds:     " <> show _inds
    , "Staus:    " <> show _status
    , "Roles:    " <> show _roles
    , "IndRoles: " <> show _indRoles
    ]

data Assertion
  = CAssertion Concept Individual
  | RAssertion Role Individual Individual
  | RInvAssertion Role Individual Individual deriving (Show, Eq)

type TBox = [Concept]
type ABox = [Assertion]

data TableauxStatus
  = ClashFound ClashException
  | Completed
  | Active deriving (Show, Eq)

type Branch = (Assertion, Assertion)

type KB = [Assertion]
type Interpretation = Maybe KB
-- Some template magic
makeLenses ''TableauxState

-- or:
--
-- import Data.Functor.Foldable
-- data ConceptF a
--   = ConjunctionF a a
--   | DisjunctionF a a
--   | NotF a
--   | ImpliesF a a
--   | IfOnlyIfF a a
--   | AtomicF Label deriving (Show, Eq, Functor, Foldable, Traversable)
-- type instance Base Concept = ConceptF
-- instance Recursive Concept where
--   project (Conjunction a b) = (ConjunctionF a) b
--   project (Disjunction a b) = (DisjunctionF a) b
--   project (Not a)           = NotF a
--   project (Implies a b)     = (ImpliesF a) b
--   project (IfOnlyIf a b)    = (IfOnlyIfF a) b
--   project (Atomic a)        = AtomicF a
--
-- instance Corecursive Concept where
--   embed (ConjunctionF a b) = (Conjunction a) b
--   embed (DisjunctionF a b) = (Disjunction a) b
--   embed (NotF a)           = Not a
--   embed (ImpliesF a b)     = (Implies a) b
--   embed (IfOnlyIfF a b)    = (IfOnlyIf a) b
--   embed (AtomicF a)        = Atomic a


class Eq a => DLogic a where
  -- | Returns its inverse
  --
  -- >>> inverse $ Not (Atomic "A")
  -- Atomic "A"
  inverse :: a -> a

  -- | Checks if two elements are complement to each other
  --
  -- >>> Atomic "A" `isComplement` Not (Atomic "A")
  -- True
  --
  -- >>> Atomic "A" `isComplement` Atomic "A"
  -- False
  --
  isComplement :: a -> a -> Bool
  x `isComplement` y = x == inverse y

class Pretty a where
  pPrint :: a -> String

-- | Simple pretty print function
--
instance (Pretty a, Pretty b) => Pretty (a,b) where
  pPrint (a, b) = "(" ++ pPrint a ++ "," ++ pPrint b ++ ")"

instance Pretty Concept where
  pPrint = cata algebra
   where
    algebra :: ConceptF String -> String
    algebra (ConjunctionF a b) = "(" ++ a ++ " ⊓ " ++ b ++ ")"
    algebra (DisjunctionF a b) = "(" ++ a ++ " ⊔ " ++ b ++ ")"
    algebra (NotF a)           = "(" ++ "¬" ++ a ++ ")"
    algebra (ImpliesF a b)     = "(" ++ a ++ " → " ++ b ++ ")"
    algebra (IfOnlyIfF a b)    = "(" ++ a ++ " ↔ " ++ b ++ ")"
    algebra (AtLeastF r c)     = "(" ++ "∃" ++ pPrint r ++ "." ++ c ++ ")"
    algebra (ForAllF r c)      = "(" ++ "∀" ++ pPrint r ++ "." ++ c ++ ")"
    algebra (AtomicF a)        = a

instance Pretty CGI where
  pPrint (Subsumes a b) = pPrint a ++ " ⊑ " ++ pPrint b
  pPrint (Equivalent a b) = pPrint a ++ " ≡ " ++ pPrint b

instance Pretty Individual where
  pPrint (Individual i) = i

instance Pretty Role where
  pPrint (Role r) = r

instance Pretty Assertion where
  pPrint (CAssertion c a) = pPrint c ++ "(" ++ pPrint a ++ ")"
  pPrint (RAssertion r a b) = pPrint r ++ "(" ++ pPrint a ++ "," ++ pPrint b ++ ")"
  pPrint (RInvAssertion r a b) = "¬" ++ pPrint (RAssertion r a b)

instance Pretty ClashException where
  pPrint (ClashException c1 c2) = "Clash found between '" ++ pPrint c1 ++ "' and '" ++ pPrint c2 ++ "'"

instance Pretty TableauxState where
  pPrint Tableaux{..} = intercalate "; " [show _status, delta, rls, cnt]
   where
    join :: Pretty a => [a] -> String
    join = intercalate ", " . fmap pPrint
    --delta = "∆ = {" ++ join _inds ++ "}"
    delta = "D = {" ++ join _inds ++ "}"
    rls = printMapOfRoles . mapOfRoles $ _intrp
    cnt = printMapOfConcepts . mapOfConcepts $ _intrp

cgiToConcept :: CGI -> Concept
cgiToConcept (Subsumes c1 c2)   = Implies c1 c2
cgiToConcept (Equivalent c1 c2) = IfOnlyIf c1 c2

printMapOfConcepts :: M.Map Concept [Individual] -> String
printMapOfConcepts = intercalate ", " . fmap showPair . M.toList
 where
  showPair (c, is) = pPrint c ++ " = {" ++ intercalate ", " (pPrint <$> is) ++ "}"

mapOfConcepts :: [Assertion] -> M.Map Concept [Individual]
mapOfConcepts = M.fromListWith (++) . mapMaybe fltr
 where
   fltr (CAssertion c a) = Just (c, [a])
   fltr _ = Nothing

printMapOfRoles :: M.Map Role [(Individual, Individual)] -> String
printMapOfRoles = intercalate ", " . fmap showPair . M.toList
 where
  showPair (r, indPairList) = pPrint r ++ " = {" ++ intercalate ", " (pPrint <$> indPairList) ++ "}"

mapOfRoles :: [Assertion] -> M.Map Role [(Individual, Individual)]
mapOfRoles = M.fromListWith (++) . mapMaybe fltr
 where
   -- TODO: Support inverse roles
   fltr (RAssertion r a b) = Just (r, [(a, b)])
   fltr _ = Nothing


isRoleAssertion :: Assertion -> Bool
isRoleAssertion RAssertion{} = True
isRoleAssertion RInvAssertion{} = True
isRoleAssertion _ = False

isConceptAssertion :: Assertion -> Bool
isConceptAssertion CAssertion{} = True
isConceptAssertion _ = False

initialize :: TBox -> ABox
initialize = 
 let ind = Individual "0"
 in fmap (`CAssertion` ind)
-- | Converts a concept to DNF
--
toDNF :: Concept -> Concept
toDNF = cata algebra
 where
  algebra :: ConceptF Concept -> Concept
  algebra (NotF (Not a))           = a
  algebra (NotF (Conjunction a b)) = Disjunction (inverse a) (inverse b)
  algebra (NotF (Disjunction a b)) = Conjunction (inverse a) (inverse b)
  algebra (NotF (AtLeast r c))     = ForAll r (inverse c)
  algebra (NotF (ForAll r c))      = AtLeast r (inverse c)
  -- TODO: This optimization is never triggered, as the IfOnlyIf has been already simplified
  -- I may have to use something like {ana|para}mporphism, to solve this
  -- algebra (NotF (IfOnlyIf a b))    = Disjunction (Conjunction a (inverse b)) (Conjunction (inverse a) b)
  algebra (ImpliesF a b)           = Disjunction (inverse a) b
  algebra (IfOnlyIfF a b)          = Disjunction (Conjunction a b) (Conjunction (inverse a) (inverse b))
  algebra c                        = embed c

-- | Tablaux expansion rules
--
expandAssertion :: ([Writer String, State TableauxState] <:: r) 
                => Assertion
                -> Eff r (Either ClashException (Maybe Branch))
expandAssertion = \case
  CAssertion (Disjunction a b) x -> do -- break assertions and return them as branches
    debugAppLn "Disjunction found"
    pure . Right . Just $ (CAssertion a x, CAssertion b x)

  CAssertion (Conjunction a b) x -> do -- break assertions and add them to frontier
    let newAssertions = [CAssertion a x, CAssertion b x]
    modify $ frontier %~ (newAssertions<>) -- break assertions and add them
    pure . Right $ Nothing
  
  CAssertion (AtLeast r c) x -> do 
    indExists <- fillerExists r c
    if indExists -- check if already a suitable individual exists
    then 
      pure . Right $ Nothing
    else do
      z <- newIndividual
      modify $ inds %~ (z:) -- insert new individual
      let newAssertions = [RAssertion r x z, CAssertion c z]
      modify $ frontier %~ (newAssertions<>)
      pure . Right $ Nothing
  
  CAssertion (ForAll r c) _ -> do
    fils <- fillers r -- find all existing fillers of R(_, i)
    let assertions = fmap (CAssertion c) fils -- add assertions for them
    modify $ roles %~ ((r, c):) -- insert the new universal role
    modify $ frontier %~ (assertions<>) -- add all new assertions
    pure . Right $ Nothing
  
  a@(RAssertion r _ f) -> do
    cpts <- forAllRoles r
    let assertions = fmap (flip CAssertion f) cpts -- add assertions for them
    modify $ indRoles %~ ((f, r):) -- insert the new universal role
    modify $ frontier %~ (assertions<>) -- add all new assertions
    addToInterpretation a -- try adding role assertion
  
  ra@RInvAssertion{} -> addToInterpretation ra
  ci@CAssertion{}    -> addToInterpretation ci

-- | Tries to add an assertion to the current interpretation
-- In case of a clash it updates the state and returns the ClassException
-- otherwise, it adds the assertion to the interpretation and returns Nothing
addToInterpretation :: ([Writer String, State TableauxState] <:: r) 
                    => Assertion
                    -> Eff r (Either ClashException (Maybe Branch))
addToInterpretation ci = do
    st <- get
    case clashesWith ci (view intrp st)  of
      Just z -> do -- clash found; terminate this branch
        let exc = ClashException ci z
        modify $ set status (ClashFound exc)
        debugAppLn . pPrint $ exc
        pure . Left $ exc
      Nothing -> do -- No clash 
        debugAppLn $ "Adding " <> pPrint ci <> " to Interpretation"
        modify $ intrp %~ (ci:) -- add assertion to interpretarion
        pure . Right $ Nothing


instance DLogic Concept where
  -- | Inverse a concept. After the inversion conversion to dnf takes place
  inverse = toDNF . Not

instance DLogic Assertion where
  inverse (CAssertion c i) = CAssertion (inverse c) i
  inverse (RAssertion r a b) = RInvAssertion r a b
  inverse (RInvAssertion r a b) = RAssertion r a b
  
-- | Checks if a concept (first argument) clashes with any of the concepts of the list
--
clashesWith :: Assertion -> [Assertion] -> Maybe Assertion
clashesWith c = safeHead . filter (isComplement c)

-- | Checks if a concept (first argument) clashes with any of the concepts of the list
--
clashExists :: Assertion -> [Assertion] -> Bool
clashExists c = isJust . clashesWith c 

-- | Returns the next uniq number of the state
--
nextUniq :: Member (State TableauxState) r => Eff r String
nextUniq = do
  st <- get
  let (unq:rest) = view uniq st
  put $ set uniq rest st
  pure unq

-- | Returns all the known filler individual of the provided role
--
fillers :: Member (State TableauxState) r => Role -> Eff r [Individual]
fillers rl = do
  st <- get
  let ids = fmap fst
           . filter ((rl ==) . snd)
           . view indRoles
           $ st
  pure ids

conceptIndividuals :: Member (State TableauxState) r => Concept -> Eff r [Individual]
conceptIndividuals c = do
  st <- get
  let ids = mapMaybe (filterCAssertions c)
          . view intrp
          $ st
  pure ids
 where
   filterCAssertions :: Concept -> Assertion -> Maybe Individual
   filterCAssertions cn (CAssertion concept ind) = if cn == concept then Just ind else Nothing
   filterCAssertions _ _                         = Nothing
  

fillerExists :: Member (State TableauxState) r => Role -> Concept -> Eff r Bool
fillerExists rl c = do
  indsA <- fillers rl
  indsB <- conceptIndividuals c
  pure . not . null $ intersect indsA indsB


-- | Returns all known concept that are imposed for a specific role
--
forAllRoles :: Member (State TableauxState ) r => Role -> Eff r [Concept]
forAllRoles rl = do
  st <- get
  let existingRoles = fmap snd
                    . filter ((rl ==) . fst)
                    . view roles
                    $ st
  pure existingRoles

solve :: ([Writer String, State TableauxState] <:: r) => Eff r Interpretation
solve = do
  st@Tableaux{..} <- get
  case _frontier of
    []    -> do
      debugAppLn "Branch completed"
      modify $ set status Completed -- nothing to expand more
      pure . Just $ _intrp          -- update status and return the interpretation
    (c:cs) -> do
      debugAppLn $ "Current: " ++ pPrint c
      modify $ set frontier cs -- remove assertion from frontier
      res <- expandAssertion c
      case res of
        Right(Just(a, b)) -> do -- or block
          let newStates :: [(TableauxState, String)]
              newStates = do -- create branched states and run them
                c' <- [a,b]
                let st' = set frontier (c':cs) st
                pure . run . runMonoidWriter . execState st' $ solve -- solve each branch
          mapM_ (debugAppLn . unlines . fmap ("   " <>) . lines .  snd) newStates
          case getInterpretation . map fst $ newStates of
            (Just state) -> do
              put state -- set the state as the final one
              pure . Just . view intrp $ state -- return its interpretation
            Nothing -> do
              put . head . map fst $ newStates -- all branches clash. Just select one of them
              pure Nothing -- no valid interpretation
        Right Nothing -> do -- no further expansion
          stt <- get
          debugAppLn $ "Remaining assertions: " ++ (show . length . view frontier $ stt)
          solve -- continue
        Left _ -> pure Nothing -- clash found; temrinate execution


-- | Creates a new individual
--
newIndividual :: Member (State TableauxState) r => Eff r Individual
newIndividual = Individual <$> nextUniq

-- | Utility function to handle logging process
-- **Attention**: Adding actual implementation (e.g. using writer or debug) will have as a
-- result all the available branches to be actually expanded in order for the
-- to be collected. For performance reasons the actual logging should be trigger only
-- for debugging purposes
--
debugAppLn :: Member (Writer String) r => String -> Eff r () 
debugAppLn = debugApp . flip (++) "\n" 

debugApp :: Member (Writer String) r => String -> Eff r () 
--debugApp = const . pure $ () -- do nothing
debugApp = tell -- log to writer
--debugApp msg = trace msg (tell msg) -- print to console and log to writer

-- | Provided a list of @TableauxState it tries to find and return the first
-- clash-free completed interpretation
--
getInterpretation :: [TableauxState] -> Maybe TableauxState
getInterpretation = safeHead      -- a single interpretation is enough 
                  . filter ((== Completed) . view status) -- get only the completed tableaux

atomicA, atomicB, atomicC, atomicD :: Concept
example1, example2, example3, example4, example5 :: Concept
atomicA = Atomic "A"
atomicB = Atomic "B"
atomicC = Atomic "C"
atomicD = Atomic "D"
example1 = Not atomicA
example2 = Conjunction atomicA atomicB
example3 = Disjunction atomicA (Conjunction atomicD atomicB)
example4 = Conjunction atomicA example1
rlR :: Role
rlR = Role "R"
example5 = Conjunction
             (Conjunction
               (AtLeast rlR atomicA)
               (AtLeast rlR atomicB))
             (Not (AtLeast rlR (Conjunction atomicA atomicB)))

initialIndividual :: Individual
initialIndividual = Individual "a"

initialState :: TableauxState
initialState = Tableaux {
    _frontier = [CAssertion (toDNF example5) initialIndividual]
  , _intrp    = []
  , _inds     = [initialIndividual]
  , _status   = Active
  , _roles    = []
  , _indRoles = []
  , _uniq     = uniqueIdentifierPool
  }

-- | Generates an almost infinite list of strings. It can be used to introduce new names
-- e.g. for individual, rules or concepts. The format of the labels are 'a0, b0, c0,..., a1, b1, c1,...
--
uniqueIdentifierPool :: [String]
uniqueIdentifierPool = (\i a -> a:show i)
                    <$> [0::Int ..]
                    <*> ['a'..'z'] 

isSatisfiable :: Assertion -> TableauxState -> Bool
isSatisfiable as initState =
  let negatedAss = inverse as
      newState   =  frontier %~ (negatedAss:) $ initState
      (intr, _log :: String) = run . evalState newState . runMonoidWriter $ solve 
  in isNothing intr

main :: IO () -- (Interpretation, String)
main = do
  let theState = initialState
      ((_interp, logs), st) = run . runState theState . runMonoidWriter $ solve 
      theLines = [ "", "***************************", ""
                 , "TBOX: "
                 , unlines
                   . fmap (\(i, v) -> "\t" <> show i <> ". " <> pPrint v)
                   . zip [1::Int ..]
                   . view frontier
                   $ theState
                 , ""
                 , "**Logging**"
                 , "-----------"
                 , ""
                 , logs
                 , "-----------"
                 , "Interpretation: " <> pPrint st
                 ]
  mapM_ putStrLn theLines

---------------
-- Utilities --
---------------

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

safeTail :: [a] -> Maybe [a]
safeTail [] = Nothing
safeTail (_:xs) = Just xs



-- -------------------------
-- -- Auxiliary functions --
-- -------------------------
-- 
-- vegan, person, vegeterian, plant, diary :: Concept
-- vegan      = Atomic "vegan"
-- person     = Atomic "person"
-- vegeterian = Atomic "vegeterian"
-- plant      = Atomic "plant"
-- diary      = Atomic "diary"
-- 
-- eats :: Role
-- eats = Role "eats"
-- 
-- veganClass :: CGI
-- veganClass = Equivalent vegan (Conjunction person (ForAll eats plant))
-- 
-- vegetarianClass :: CGI
-- vegetarianClass = Equivalent vegeterian (Conjunction person (ForAll eats (Disjunction plant diary)))
-- 
-- vegeterianIsVegan :: CGI
-- vegeterianIsVegan = Subsumes vegan vegeterian
-- 
-- veganIsVegeterian :: CGI
-- veganIsVegeterian = Subsumes vegeterian vegan 
-- 
-- testState :: TableauxState
-- testState = initialState {
--     _frontier = [CAssertion x initialIndividual | x <- asrts] -- [CAssertion (toDNF asrts) initialIndividual]
--   , _intrp    = []
--   , _inds     = [initialIndividual]
--   , _status   = Active
--   , _roles    = []
--   , _indRoles = []
--   , _uniq     = uniqueIdentifierPool
--   }
--  where
--   --asrts = fmap (toDNF . cgiToConcept) [veganClass, vegetarianClass, veganIsVegeterian]
--   asrts = fmap (toDNF . cgiToConcept) [veganClass, vegetarianClass] -- <> [toDNF . Not $ Implies vegan vegeterian]
