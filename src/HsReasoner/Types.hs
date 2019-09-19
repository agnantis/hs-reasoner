{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module HsReasoner.Types where

--import Prelude                        hiding (head, tail)

import           Control.Eff
import           Control.Eff.State.Lazy
import           Control.Eff.Writer.Lazy
import           Control.Monad                  (mapM_)
import           Data.Functor.Foldable          (cata, embed)
import           Data.Functor.Foldable.TH       (makeBaseFunctor)
import           Data.List                      (intercalate, intersect, nub)
import qualified Data.Map.Strict                                    as M
import           Data.Maybe                     (fromMaybe, isJust, mapMaybe)
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
  | Exists Role Concept         -- ^ ∃R.C
  | ForAll Role Concept         -- ^ ∀R.C
  | Bottom                      -- ⊥
  | Top                         -- T
  | Atomic Label deriving (Show, Eq, Ord)

makeBaseFunctor ''Concept

data CGI
  = SimpleCGI Concept -- ~ Not Concept `Subsumes` Bottom
  | Subsumes Concept Concept
  | Equivalent Concept Concept deriving (Show, Eq)

type UniRole = (Role, Concept) -- ^ Represents a ∀R.C (i.e. (R,C)
type IndRole = (Individual, Role) -- ^ Represents a filler of a role
type BlockedInds = (Individual, Individual) -- ^ (a,b) where a is the blocked and b is the blocking individuals
type ExistIndividual = (Individual, Concept) -- ^ (a,b) where a is a filler individual that has been introduced by
                                             -- the concept expansion b (only `Exists` in ALC)

data ClashException = ClashException Assertion Assertion deriving (Eq, Show)

data TableauxState = Tableaux
  { _frontier    :: [Assertion]    -- ^ Assertions to be expanded
  , _intrp       :: [Assertion]    -- ^ The current interpretation
  , _inds        :: [Individual]   -- ^ individuals in scope
  , _status      :: TableauxStatus -- ^ The state of the specific path
  , _roles       :: [UniRole]      -- ^ It holds all visited universal role
  , _indRoles    :: [IndRole]      -- ^ It holds all the filler individual
  , _blocked     :: [BlockedInds]  -- ^ It holds all the blocked individuals
  , _uniq        :: [String]       -- ^ A generator of uniq ids
  , _initialTBox :: [Concept]      -- ^ The initial TBox translated to concepts
  , _existInds   :: [ExistIndividual] -- ^ it holds all the individuals created due to a concept expansion (concept included)
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

type TBox = [CGI]
type ABox = [Assertion]
type KB = (TBox, ABox)

data TableauxStatus
  = ClashFound ClashException
  | Completed
  | Active deriving (Show, Eq)

type Branch = (Assertion, Assertion)

type Interpretation = Maybe ABox
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
    algebra (ExistsF r c)     = "(" ++ "∃" ++ pPrint r ++ "." ++ c ++ ")"
    algebra (ForAllF r c)      = "(" ++ "∀" ++ pPrint r ++ "." ++ c ++ ")"
    algebra BottomF            = "⊥"
    algebra TopF               = "⏉"
    algebra (AtomicF a)        = a

instance Pretty CGI where
  pPrint (Subsumes a b) = pPrint a ++ " ⊑ " ++ pPrint b
  pPrint (Equivalent a b) = pPrint a ++ " ≡ " ++ pPrint b
  pPrint (SimpleCGI c) = pPrint c

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
  pPrint Tableaux{..} = intercalate "; " [show _status, delta, rls, cnt, blck]
   where
    join :: (Pretty a, Eq a) => [a] -> String
    join = intercalate ", " . fmap pPrint . nub
    --delta = "∆ = {" ++ join _inds ++ "}"
    delta = "D = {" ++ join _inds ++ "}"
    rls = printMapOfRoles . mapOfRoles $ _intrp
    cnt = printMapOfConcepts . mapOfConcepts $ _intrp
    blck = "B = {" ++ join _blocked ++ "}"

cgiToConcept :: CGI -> Concept
cgiToConcept (c1 `Subsumes` c2)   = c2 `Implies` c1
cgiToConcept (c1 `Equivalent` c2) = c1 `IfOnlyIf` c2
cgiToConcept (SimpleCGI c) = c 

printMapOfConcepts :: M.Map Concept [Individual] -> String
printMapOfConcepts = intercalate ", " . fmap showPair . M.toList
 where
  showPair (c, is) = pPrint c ++ " = {" ++ intercalate ", " (pPrint <$> nub is) ++ "}"

mapOfConcepts :: [Assertion] -> M.Map Concept [Individual]
mapOfConcepts = M.fromListWith (++) . mapMaybe fltr
 where
   fltr (CAssertion c a) = Just (c, [a])
   fltr _ = Nothing

printMapOfRoles :: M.Map Role [(Individual, Individual)] -> String
printMapOfRoles = intercalate ", " . fmap showPair . M.toList
 where
  showPair (r, indPairList) = pPrint r ++ " = {" ++ intercalate ", " (pPrint <$> nub indPairList) ++ "}"

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

-- | Converts a concept to DNF
--
toDNF :: Concept -> Concept
toDNF = cata algebra
 where
  algebra :: ConceptF Concept -> Concept
  algebra (NotF (Not a))           = a
  algebra (NotF (Conjunction a b)) = Disjunction (inverse a) (inverse b)
  algebra (NotF (Disjunction a b)) = Conjunction (inverse a) (inverse b)
  algebra (NotF (Exists r c))     = ForAll r (inverse c)
  algebra (NotF (ForAll r c))      = Exists r (inverse c)
  algebra (NotF Bottom)            = Top
  algebra (NotF Top)               = Bottom
  -- TODO: This optimization is never triggered, as the IfOnlyIf has been already simplified
  -- I may have to use something like {ana|para}mporphism, to solve this
  -- algebra (NotF (IfOnlyIf a b))    = Disjunction (Conjunction a (inverse b)) (Conjunction (inverse a) b)
  algebra (ImpliesF a b)           = Disjunction (inverse a) b
  algebra (IfOnlyIfF a b)          = Disjunction (Conjunction a b) (Conjunction (inverse a) (inverse b))
  algebra c                        = embed c

-- | Tablaux expansion rules
--
-- It read the next available assertion and execute the correspnding rule
-- The function may return:
--   * (Left) ClassException; when the assertion clashes with another assertion in the current imeplementation
--   * (Right) Branch; when the assertion cause the curent state to split to two new (alternative) states
--   * (Right) Nothing; in any other case
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

  CAssertion existsC@(Exists r c) x -> do
    indExists <- fillerExists r c x
    traceShow ("Exists: " ++ show indExists) $ pure ()
    if indExists -- check if already a suitable individual exists
    then
      pure . Right $ Nothing
    else do
      blockingNodes <- findBlockingNodes x r existsC
      traceShow ("Blocking: " ++ show blockingNodes) $ pure ()
      if (not . null) blockingNodes
      then do
        let blocker = head blockingNodes
        modify $ blocked %~ ((x, blocker):) -- add node to the blocking ones
        removeBlockedAssertions x -- remove assertion of blocked individuals
        modify $ intrp %~ fmap (replaceIndividual x blocker) -- update interpretation; replace any reference to to the blocked individual with the blocking one
        pure . Right $ Nothing
      else do
        z <- newIndividual
        modify $ inds %~ (z:) -- insert new individual
        modify $ existInds %~ ((z, existsC):) -- insert new individual and the cause of this creation
        state <- get
        let
          newAssertions = [CAssertion c z, RAssertion r x z]
          tboxAssertions = fmap (flip CAssertion z) $ state ^. initialTBox
        modify $ frontier %~ (<> (newAssertions <> tboxAssertions))
        pure . Right $ Nothing

  CAssertion (ForAll r c) _ -> do
    fils <- fillers r Nothing -- find all existing fillers of R(_, i)
    let assertions = fmap (CAssertion c) fils -- add assertions for them
    modify $ roles %~ ((r, c):) -- insert the new universal role
    modify $ frontier %~ (assertions<>) -- add all new assertions
    pure . Right $ Nothing

  a@(RAssertion r _ f) -> do
    cpts <- forAllRoles r
    let assertions = fmap (flip CAssertion f) cpts -- add assertions for them
    modify $ indRoles %~ ((f, r):) -- insert the new role filler
    modify $ frontier %~ (assertions<>) -- add all new assertions
    addToInterpretation a -- try adding role assertion

  ra@RInvAssertion{} -> addToInterpretation ra
  ci@CAssertion{}    -> addToInterpretation ci

removeBlockedAssertions :: Member (State TableauxState) r
                        => Individual
                        -> Eff r ()
removeBlockedAssertions i = do
  modify $ frontier %~ filter ((== Just i) . extractIndividual)
  pure ()
 where
  extractIndividual :: Assertion -> Maybe Individual
  extractIndividual RAssertion{} = Nothing
  extractIndividual RInvAssertion{} = Nothing
  extractIndividual (CAssertion _ a) = Just a

-- | Tries to add an assertion to the current interpretation
-- In case of a clash it updates the state and returns the ClashException
-- otherwise, it adds the assertion to the interpretation and returns Nothing
--
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

-- | It tries to find all the possible blocking individuals of the input individual
--
findBlockingNodes :: ([Writer String, State TableauxState] <:: r)
                  => Individual
                  -> Role
                  -> Concept
                  -> Eff r [Individual]
findBlockingNodes i r c = do
  state        <- get
  roleParents  <- roleParent r (Just i) -- get parents of i
  sameRuleInds <- fromSameRule c 
  let possibleParents = dropUntil (/=i) . view inds $ state
  pure $ possibleParents `intersect` roleParents `intersect` sameRuleInds
  
-- | Replace an individual in the assertion with another and return the new assertion
--
replaceIndividual :: Individual -> Individual -> Assertion -> Assertion
replaceIndividual x y cpt@(CAssertion c a) = if a /= x then cpt else CAssertion c y 
replaceIndividual x y (RAssertion r a b) =
  let a' = if a == x then y else a
      b' = if b == x then y else b
  in RAssertion r a' b'
replaceIndividual x y (RInvAssertion r a b) = 
  let a' = if a == x then y else a
      b' = if b == x then y else b
  in RInvAssertion r a' b'


instance DLogic Concept where
  -- | Inverse a concept. After the inversion conversion to dnf takes place
  inverse = toDNF . Not

instance DLogic Assertion where
  inverse (CAssertion c i) = CAssertion (inverse c) i
  inverse (RAssertion r a b) = RInvAssertion r a b
  inverse (RInvAssertion r a b) = RAssertion r a b

-- | Checks if a concept (first argument) clashes with any of the concepts of the list
--
-- >>> bottom = CAssertion Bottom initialIndividual
-- >>> top = CAssertion Top initialIndividual
-- >>> clashesWith bottom [top]
-- Just (CAssertion Top (Individual "a"))
--
-- >>> clashesWith top [bottom]
-- Just (CAssertion Bottom (Individual "a"))
--
clashesWith :: Assertion -> [Assertion] -> Maybe Assertion
clashesWith (CAssertion Bottom i) _ = Just $ CAssertion Top i
clashesWith c xs = safeHead . filter (isComplement c) $ xs

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
-- If input individual is not Nothing, it returns only the filler with this specific filler
--
fillers :: Member (State TableauxState) r => Role -> Maybe Individual -> Eff r [Individual]
fillers rl mi = do
  st <- get
  let
    ids = mapMaybe (fltr rl mi)
        . view intrp
        $ st
    fltr :: Role -> Maybe Individual -> Assertion -> Maybe Individual  
    fltr r Nothing  (RAssertion r' _ y) = if r == r' then Just y else Nothing
    fltr r (Just i) (RAssertion r' z y) = if r == r' && i == z then Just y else Nothing
    fltr _ _ _                          = Nothing
  pure ids

-- | Returns all the known individuals that are parents in a specific role
-- If input individual is not Nothing, it returns only the parents if this specific filler
--
roleParent :: Member (State TableauxState) r => Role -> Maybe Individual -> Eff r [Individual]
roleParent r mi = do
  st <- get
  let ids = mapMaybe (fltr r mi)
          . view intrp
          $ st
      fltr :: Role -> Maybe Individual -> Assertion -> Maybe Individual  
      fltr ar Nothing  (RAssertion r' x _) = if ar == r' then Just x else Nothing
      fltr ar (Just i) (RAssertion r' x y) = if ar == r' && i == y then Just x else Nothing
      fltr _ _ _                           = Nothing
  pure ids

-- | Returns all individuals that have been introduce in the model, because of the 
-- provided concept expansion
--
fromSameRule :: Member (State TableauxState) r => Concept -> Eff r [Individual]
fromSameRule cpt = do
  st <- get
  let ids = fmap fst
          . filter ((==) cpt . snd)
          . view existInds
          $ st
  pure ids

-- | Returns all individuals that beong to the provided concept
--
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


-- | Checks if there is a filler individual for the input role where the parent is the provided
-- individual and that also belongs to the input concept
--
fillerExists :: Member (State TableauxState) r => Role -> Concept -> Individual -> Eff r Bool
fillerExists rl c i = do
  indsA <- fillers rl (Just i)
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
        Left _ -> pure Nothing -- clash found; temrinate execution

        Right Nothing -> do -- no further expansion
          stt <- get
          debugAppLn $ "Remaining assertions: " ++ (show . length . view frontier $ stt)
          solve -- continue
        
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
debugApp = const . pure $ () -- do nothing
--debugApp = tell -- log to writer
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
               (Exists rlR atomicA)
               (Exists rlR atomicB))
             (Not (Exists rlR (Conjunction atomicA atomicB)))

initialIndividual :: Individual
initialIndividual = Individual "a"

initialState :: TableauxState
initialState     = Tableaux {
    _frontier    = [CAssertion (toDNF example5) initialIndividual]
  , _intrp       = []
  , _inds        = [initialIndividual]
  , _status      = Active
  , _roles       = []
  , _indRoles    = []
  , _uniq        = uniqueIdentifierPool
  , _blocked     = []
  , _initialTBox = []
  , _existInds   = []
  }

-- | Generates an almost infinite list of strings. It can be used to introduce new names
-- e.g. for individual, rules or concepts. The format of the labels are 'b, c,..., z, a1, b1, c1,...
--
-- >>> take 4 uniqueIdentifierPool
-- ["b","c","d","e"]
-- >>> drop 24 . take 28 $ uniqueIdentifierPool
-- ["z","a1","b1","c1"]
--
uniqueIdentifierPool :: [String]
uniqueIdentifierPool =
  let seq' = flip (:) 
             <$> "" : fmap (show @Int) [1 ..]
             <*> ['a'..'z']
  in tail seq'

isProvableS :: CGI -> TBox -> ABox -> TableauxState
isProvableS cgi tbox abox =
  let
      initState = initialTableaux tbox abox
      negatedAss = inverse $ cgiToConcept cgi
      existingInds = initState ^. inds
      ass = CAssertion negatedAss <$> existingInds -- build assertions from cgi for all existing inds
      newState   =  frontier %~ (ass <>) $ initState
      ((_intr, _log::String), state) = run . runState newState . runMonoidWriter $ solve
  in state

isValidModelS :: TBox -> ABox -> TableauxState
isValidModelS tbox abox =
  let
      initState = initialTableaux tbox abox
      ((_intr, _log::String), state) = run . runState initState . runMonoidWriter $ solve
  in state


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

-- | Given an assertion, extracts the involved individuals
--
extractIndividuals :: Assertion -> [Individual]
extractIndividuals = \case
  CAssertion _ a -> [a]
  RAssertion _ a b -> [a,b]
  RInvAssertion _ a b -> [a,b]

-- | Given a TBox and an ABox, it generates an initial table state
--
initialTableaux :: TBox -> ABox -> TableauxState
initialTableaux cgis ass =
  let
    providedInds = nub $ concatMap extractIndividuals ass -- extract esixting individuals
    allInds = providedInds `orElse` [initialIndividual] -- if none exists, use the default one
    newCpts = fmap (toDNF . cgiToConcept) cgis
    newAss = do -- convert cgis to assertions
       cnpt <- newCpts
       CAssertion cnpt <$> allInds
    allAss = newAss <> ass
  in Tableaux
    { _frontier    = allAss
    , _intrp       = []
    , _inds        = allInds
    , _status      = Active
    , _roles       = []
    , _indRoles    = []
    , _uniq        = uniqueIdentifierPool
    , _blocked     = []
    , _initialTBox = newCpts
    , _existInds   = []
    }

-- | An _alternative_ (<|>) for list when they not used for non-determinism encoding
-- Then function tries to select the non-empty list in case it exists
--
-- >>> [] `orElse` [1,2,3]
-- [1,2,3]
-- >>> [1,2] `orElse` []
-- [1,2]
-- >>> [1,2] `orElse` [4,5,6]
-- [1,2]
--
orElse :: [a] -> [a] -> [a]
orElse [] xs = xs
orElse xs _  = xs

-- | Like `dropWhile` but it also drops the head of the retult
--
dropUntil :: (a -> Bool)-> [a] -> [a]
dropUntil f xs = fromMaybe [] (safeTail $ dropWhile f xs)


----------------
-- Public API --
----------------

-- | Smart constructor of Subsumes CGI
--
subsumes :: Concept -> Concept -> CGI
subsumes a b = a `Subsumes` b

-- | Smart constructor of Subsumes CGI
--
isSubsumedBy :: Concept -> Concept -> CGI
isSubsumedBy a b = b `subsumes` a

-- | Smart constructor of Equivalent CGI
--
isEquivalentTo :: Concept -> Concept -> CGI
isEquivalentTo a b = a `Equivalent` b

-- | Smart constructor of the Simple CGI
simpleCGI :: Concept -> CGI
simpleCGI = SimpleCGI
-- simpleCGI c = Not c `isSubsumedBy` Bottom

-- | Given an TBox and and ABox, the funtion checks if the provided CGI
-- can be proved.
-- It returns `True` if it can be proved, otherwise it returns `False`
--
isProvable :: CGI -> TBox -> ABox -> Bool
isProvable cgi tbox abox =
  let state = isProvableS cgi tbox abox
  in  Completed /= state ^. status

-- | The funtion checks if the model described by the provided TBox and ABox
-- is valid.
-- It returns `True` if there is a valid model, otherwise it returns `False`
--
isValidModel :: TBox -> ABox -> Bool
isValidModel tbox abox =
  let state = isValidModelS tbox abox
  in  Completed == state ^. status

