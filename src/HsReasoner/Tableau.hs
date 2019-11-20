{-# OPTIONS_GHC -fplugin=Polysemy.Plugin #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module HsReasoner.Tableau where

import           Control.Monad                  (mapM_, replicateM)
import           Data.Functor.Foldable          (cata, embed)
import           Data.List                      (intersect, nub)
import           Data.Map                       (Map)
import qualified Data.Map                  as M (empty, findWithDefault, lookup, map)
import           Data.Maybe                     (fromMaybe, isJust, mapMaybe)
import           Data.Tuple                     (swap)
import           Lens.Micro.Platform
import           Polysemy
import           Polysemy.State
import           Polysemy.Writer

import           Debug.Trace

import           HsReasoner.Types
import           HsReasoner.Utils

class Eq a => DLogic a where
  -- | Returns its inverse
  --
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


instance DLogic Concept where
  -- | Inverse a concept. After the inversion conversion to dnf takes place
  -- >>> inverse $ Not (Atomic "A")
  -- Atomic "A"
  inverse = toDNF . Not

instance DLogic Assertion where
  inverse (CAssertion c i) = CAssertion (inverse c) i
  inverse (RAssertion r a b) = RInvAssertion r a b
  inverse (RInvAssertion r a b) = RAssertion r a b

---------------------
-- Expansion rules --
---------------------

-- | Conjunction rule expansion
--
andRule :: Member (Writer String) r
        => Concept
        -> Concept
        -> Individual
        -> Sem r Branch
andRule a b i = do
  debugAppLn "Disjunction found"
  pure (CAssertion a i, CAssertion b i)

-- | Disjunction rule expansion
--
orRule :: Member (State TableauState) r
       => Concept
       -> Concept
       -> Individual
       -> Sem r ()
orRule a b i = do
  let newAssertions = [CAssertion a i, CAssertion b i]
  modify $ frontier %~ (newAssertions<>)
  pure ()

-- | Forall rule expansion
--
allRule :: Member (State TableauState) r
        => Role
        -> Concept
        -> Sem r ()
allRule r c = do
  fils <- fillers r Nothing -- find all existing fillers of R(_, i)
  let assertions = fmap (CAssertion c) fils -- add assertions for them
  modify $ roles %~ ((r, c):) -- insert the new universal role
  modify $ frontier %~ (assertions<>) -- add all new assertions
  pure ()

-- | At least rule expansion. A special version of the at least restriction
-- (where n = 1)
--
existsRule :: Member (State TableauState) r
           => Role
           -> Concept
           -> Individual
           -> Sem r ()
existsRule = atLeastRule 1

-- | LessEqual rule expansion
-- 1. extract all fillers
-- 2. get all the unique fillers
-- 3. if they are less than n
--    F:.do nothing
--    T: a. create n new (or n-unique?)
--       b. marked them as pairwise distinct and add the info to the state
--       c. create the roles with the new inds and add them to the state
atMostRule :: Member (State TableauState) r
           => Int
           -> Role
           -> Concept
           -> Individual
           -> Sem r ()
atMostRule = undefined

-- | GreaterEqual rule expansion. A more general version of existensial quantifier
--
atLeastRule :: Member (State TableauState) r
              => Int
              -> Role
              -> Concept
              -> Individual
              -> Sem r ()
atLeastRule n r c x = do
  let atLeastC = AtLeast n r c
  ex <- roleFillers r c x
  -- traceShow ("Exists: " ++ show indExists) $ pure ()
  if length ex >= n -- check if there are existing individuals
  then
    pure ()
  else do
    blockingNodes <- findBlockingNodes x r atLeastC
    -- traceShow ("Blocking: " ++ show blockingNodes) $ pure ()
    if (not . null) blockingNodes
    then do
      let blocker = head blockingNodes
      modify $ blocked %~ ((x, blocker):) -- add node to the blocking ones
      removeBlockedAssertions x -- remove assertion of blocked individuals
      modify $ intrp %~ fmap (replaceIndividual x blocker) -- update interpretation; replace any reference to to the blocked individual with the blocking one
      pure ()
    else do
      zs <- replicateM n newIndividual
      modify $ inds %~ (zs <>) -- insert new individual
      let newIndRules = (, atLeastC) <$> zs
      modify $ existInds %~ (newIndRules <>) -- insert new individual and the cause of this creation
      let
        newAssertions = concat $ (\i -> [CAssertion c i, RAssertion r x i]) <$> zs
      modify $ frontier %~ (<> newAssertions)
      pure ()


-- | Role assertion rule expansion
--
roleRule :: Member (State TableauState) r
         => Role
         -> Individual
         -> Sem r ()
roleRule r f = do
  cpts <- forAllRoles r
  let assertions = fmap (flip CAssertion f) cpts -- add assertions for them
  modify $ indRoles %~ ((f, r):) -- insert the new role filler
  modify $ frontier %~ (assertions<>) -- add all new assertions
  pure ()

-- | The function reads the next available assertion and executes the corresponding expansion rule
-- The function may return:
--   * (Left) ClassException; when the assertion clashes with another assertion in the current implementation
--   * (Right) Branch; when the assertion cause the curent state to split to two new (alternative) states
--   * (Right) Nothing; in any other case
--
expandAssertion :: (Members [Writer String, State TableauState] r)
                => Assertion
                -> Sem r (Either ClashException (Maybe Branch))
expandAssertion = \case
  CAssertion (Disjunction a b) x -> Right . Just <$> andRule a b x
  CAssertion (Conjunction a b) x -> Right Nothing <$ orRule a b x
  CAssertion (ForAll r c) _      -> Right Nothing <$ allRule r c
  CAssertion (Exists r c) x      -> Right Nothing <$ existsRule r c x
  CAssertion (AtMost n r c) x    -> Right Nothing <$ atMostRule n r c x
  CAssertion (AtLeast n r c) x   -> Right Nothing <$ atLeastRule n r c x
  a@(RAssertion r _ f)           -> roleRule r f >> addToInterpretation a -- try adding role assertion
  ra@RInvAssertion{}             -> addToInterpretation ra -- TODO: extra actions may be required
  ci@CAssertion{}                -> addToInterpretation ci


removeBlockedAssertions :: Member (State TableauState) r
                        => Individual
                        -> Sem r ()
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
addToInterpretation :: Members [Writer String, State TableauState] r
                    => Assertion
                    -> Sem r (Either ClashException (Maybe Branch))
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
findBlockingNodes :: Member (State TableauState) r
                  => Individual
                  -> Role
                  -> Concept
                  -> Sem r [Individual]
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
nextUniq :: Member (State TableauState) r => Sem r String
nextUniq = do
  st <- get
  let (unq:rest) = view uniq st
  put $ set uniq rest st
  pure unq

-- | Returns all the known filler individual of the provided role
-- If input individual is not Nothing, it returns only the filler with this specific filler
--
fillers :: Member (State TableauState) r => Role -> Maybe Individual -> Sem r [Individual]
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
roleParent :: Member (State TableauState) r => Role -> Maybe Individual -> Sem r [Individual]
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
fromSameRule :: Member (State TableauState) r => Concept -> Sem r [Individual]
fromSameRule cpt = do
  st <- get
  let ids = fmap fst
          . filter ((==) cpt . snd)
          . view existInds
          $ st
  pure ids

-- | Returns all individuals that beong to the provided concept
--
-- TODO: the code does not handle the cases where a concept C subsumes concept C'
-- and we ask for individuals that belong to C. The code should return individuals
-- of C' as well, but currently it does not do that
conceptIndividuals :: Member (State TableauState) r => Concept -> Sem r [Individual]
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
fillerExists :: Member (State TableauState) r => Role -> Concept -> Individual -> Sem r Bool
fillerExists rl c i =  not.null <$> roleFillers rl c i

-- | Returns all the filler individuals for the input role where the parent is the provided
-- individual and that also belongs to the input concept
--
roleFillers :: Member (State TableauState) r => Role -> Concept -> Individual -> Sem r [Individual]
roleFillers rl c i = do
  indsA <- fillers rl (Just i)
  indsB <- conceptIndividuals c
  pure $ intersect indsA indsB


-- | Returns all known concept that are imposed for a specific role
--
forAllRoles :: Member (State TableauState ) r => Role -> Sem r [Concept]
forAllRoles rl = do
  st <- get
  let existingRoles = fmap snd
                    . filter ((rl ==) . fst)
                    . view roles
                    $ st
  pure existingRoles

solve :: Members [Writer String, State TableauState] r => Sem r Interpretation
solve = do
  st@Tableau{..} <- get
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
          let newStates :: [(TableauState, String)]
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
newIndividual :: Member (State TableauState) r => Sem r Individual
newIndividual = Individual <$> nextUniq

-- | Utility function to handle logging process
-- **Attention**: Adding actual implementation (e.g. using writer or debug) will have as a
-- result all the available branches to be actually expanded in order for the
-- to be collected. For performance reasons the actual logging should be trigger only
-- for debugging purposes
--
debugAppLn :: Member (Writer String) r => String -> Sem r ()
debugAppLn = debugApp . flip (++) "\n"

debugApp :: Member (Writer String) r => String -> Sem r ()
debugApp = const . pure $ () -- do nothing
--debugApp = tell -- log to writer
--debugApp msg = trace msg (pure ()) -- print to console
--debugApp msg = trace msg (tell msg) -- print to console and log to writer

-- | Provided a list of @TableauState it tries to find and return the first
-- clash-free completed interpretation
--
getInterpretation :: [TableauState] -> Maybe TableauState
getInterpretation = safeHead      -- a single interpretation is enough
                  . filter ((== Completed) . view status) -- get only the completed tableau

cgiToConcept :: CGI -> Concept
cgiToConcept (c1 `Subsumes` c2)   = c2 `Implies` c1
cgiToConcept (c1 `Equivalent` c2) = c1 `IfOnlyIf` c2
cgiToConcept (c1 `Disjoint` c2) = Disjunction c1 c2 `Implies` Bottom
cgiToConcept (SimpleCGI c) = c 


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


-- | Expand the whole tbox
--
expandTBox :: TBox -> TBox
expandTBox tbox = M.map (expandConcept tbox) tbox

-- | Expand a concept
--
expandConcept :: TBox -> Concept -> Concept
expandConcept tbox = toDNF . cata algebra
 where
  algebra :: ConceptF Concept -> Concept
  algebra (NotF a)           = Not (expand a)
  algebra (ConjunctionF a b) = Conjunction (expand a) (expand b)
  algebra (DisjunctionF a b) = Disjunction (expand a) (expand b)
  algebra (ExistsF r c)      = Exists r (expand c)
  algebra (ForAllF r c)      = ForAll r (expand c)
  algebra (ImpliesF a b)     = Implies (expand a) (expand b)
  algebra (IfOnlyIfF a b)    = IfOnlyIf (expand a) (expand b)
  algebra c                  = embed c
  expand :: Concept -> Concept
  expand c =
    case M.lookup c tbox of
      Nothing -> c
      Just c' -> expandConcept tbox c'

-- | Extract concept dependencies
--
extractDependencies :: Concept -> [Concept]
extractDependencies = cata algebra
 where
  algebra :: ConceptF [Concept] -> [Concept]
  algebra (AtomicF t)        = [Atomic t]
  algebra (NotF a)           = a
  algebra (ConjunctionF a b) = a <> b
  algebra (DisjunctionF a b) = a <> b
  algebra (ExistsF _ c)      = c
  algebra (ForAllF _ c)      = c
  algebra (ImpliesF a b)     = a <> b 
  algebra (IfOnlyIfF a b)    = a <> b
  algebra (AtMostF _ _ a)    = a
  algebra (AtLeastF _ _ a)   = a
  algebra BottomF            = []
  algebra TopF               = []


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

initialState :: TableauState
initialState     = Tableau {
    _frontier    = [CAssertion (toDNF example5) initialIndividual]
  , _intrp       = []
  , _inds        = [initialIndividual]
  , _status      = Active
  , _roles       = []
  , _indRoles    = []
  , _uniq        = uniqueIdentifierPool
  , _blocked     = []
  , _initialTBox = M.empty
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

isProvableS :: CGI -> TBox -> TableauState
isProvableS cgi = isSatisfiableS (inverse . cgiToConcept $ cgi)

isSatisfiableS :: Concept -> TBox -> TableauState
isSatisfiableS c tbox =
  let
      expandedTBox = expandTBox tbox
      expandedC = toDNF . expandConcept expandedTBox $ c
      initState = initialTableau expandedTBox []
      ass = CAssertion expandedC initialIndividual
      newState =  frontier .~ [ass] $ initState
      ((_intr, _log::String), state) = run . runStateP newState . runMonoidWriter $ solve
  in state


-- | expand the concept of a CGI using the definitions provided in the 'TBox' argument
-- In order for the concepts of the cgi to fully expanded, the provided tbox should be fully
-- expanded as well
--
expandCGI :: CGI -> TBox -> CGI
expandCGI cgi tbox = mapOverCGI (\c -> M.findWithDefault c c tbox) cgi


main :: IO () -- (Interpretation, String)
main = do
  let theState = initialState
      ((_interp, logs), st) = run . runStateP theState . runMonoidWriter $ solve
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

graphFromTBox :: TBox -> Map Concept [Concept]
graphFromTBox = M.map extractDependencies

-- | Given an assertion, extracts the involved individuals
--
extractIndividuals :: Assertion -> [Individual]
extractIndividuals = \case
  CAssertion _ a -> [a]
  RAssertion _ a b -> [a,b]
  RInvAssertion _ a b -> [a,b]

-- | Given a TBox and an ABox, it generates an initial table state
--
initialTableau :: TBox -> ABox -> TableauState
initialTableau tbox abox =
  let
    providedInds = nub $ concatMap extractIndividuals abox -- extract esixting individuals
    allInds = providedInds `orElse` [initialIndividual] -- if none exists, use the default one
  in Tableau
    { _frontier    = abox
    , _intrp       = []
    , _inds        = allInds
    , _status      = Active
    , _roles       = []
    , _indRoles    = []
    , _uniq        = uniqueIdentifierPool
    , _blocked     = []
    , _initialTBox = tbox
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

-- Helper functions for the transition from extensible-effects to polysemy
execState :: s -> Sem (State s ': r) a -> Sem r s
execState s = fmap fst . runState s

runMonoidWriter :: Monoid o => Sem (Writer o : r) a -> Sem r (a, o)
runMonoidWriter = fmap swap . runWriter

runStateP ::  s -> Sem (State s ': r) a -> Sem r (a, s)
runStateP x = fmap swap . runState x

----------------
-- Public API --
----------------

-- | Smart constructor of Subsumes CGI
--
subsumes :: Concept -> Concept -> CGI
subsumes = Subsumes

-- | Smart constructor of Subsumes CGI
--
isSubsumedBy :: Concept -> Concept -> CGI
isSubsumedBy = flip subsumes

-- | Smart constructor of Equivalent CGI
--
isEquivalentTo :: Concept -> Concept -> CGI
isEquivalentTo = Equivalent

-- | Smart constructor of Disjoint CGI
--
isDisjointWith :: Concept -> Concept -> CGI
isDisjointWith = Disjoint

-- | Smart constructor of the Simple CGI
--
simpleCGI :: Concept -> CGI
simpleCGI = SimpleCGI
-- simpleCGI c = Not c `isSubsumedBy` Bottom

------------------
-- Concept Task --
------------------

-- | Given an TBox and and ABox, the funtion checks if the provided CGI
-- can be proved.
-- It returns `True` if it can be proved, otherwise it returns `False`
--
isProvable :: CGI -> TBox -> Bool
isProvable cgi tbox =
  let state = isProvableS cgi tbox
  in  Completed /= state ^. status

-- | The funtion checks if the model described by the provided TBox and ABox
-- is valid.
-- It returns `True` if there is a valid model, otherwise it returns `False`
--
isSatisfiable :: Concept -> TBox -> Bool
isSatisfiable c tbox =
  let state = isSatisfiableS c tbox
  in  Completed == state ^. status

