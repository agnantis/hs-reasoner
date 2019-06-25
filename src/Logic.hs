{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module Logic where

--import Prelude                        hiding (head, tail)

import Control.Eff
import Control.Eff.State.Lazy
import Control.Eff.Writer.Lazy
import Control.Monad                  (mapM_)
import Data.Functor.Foldable          (cata, embed)
import Data.Functor.Foldable.TH       (makeBaseFunctor)
import Data.Maybe                     (isJust)
import Lens.Micro.Platform

import Debug.Trace

type Label = String
newtype Individual = Individual Label deriving (Show, Eq)

newtype Role = Role Label deriving (Show, Eq)

data Concept
  = Conjunction Concept Concept -- ^ AND
  | Disjunction Concept Concept -- ^ OR
  | Not Concept                 -- ^ NOT
  | Implies Concept Concept     -- ^ A -> B
  | IfOnlyIf Concept Concept    -- ^ A <-> B
  | AtLeast Role Concept        -- ^ R.C
  | ForAll Role Concept         -- ^ R.C
  | Atomic Label deriving (Show, Eq)

makeBaseFunctor ''Concept

data CGI
  = Subsumes Concept Concept
  | Equivalent Concept Concept deriving (Show, Eq)

--type TBox = [CGI]


  
data ClashException = ClashException Assertion Assertion deriving (Eq)
instance Show ClashException where
  show (ClashException c1 c2) = "Clash found between '" ++ show c1 ++ "' and '" ++ show c2 ++ "'"

data TableauxState = Tableaux
  { _frontier :: [Assertion] -- ^ Concepts to be expanded
  --, _kb       :: [Concept] -- ^ In practice, it holds all the true and false atomic concepts
  , _intrp    :: [Assertion] -- ^ The current interpretation
  , _inds     :: [Individual] -- ^ individuals in scope
  , _status   :: TableauxStatus -- ^ The state of the specific path
  , _roles    :: [Assertion] -- ^ It should hold all the roles 
  , _uniq     :: [Int] -- ^ A generator of uniq ids
  } deriving (Show)

data Assertion
  = CAssertion Concept Individual
  | RAssertion Role Individual Individual deriving (Show, Eq)

type TBox = [Concept]
type ABox = [Assertion]

data TableauxStatus
  = ClashFound ClashException
  | Completed
  | Active deriving (Show, Eq)

data Expansion
  = Branch [Assertion]
  | Seq [Assertion] deriving (Show)

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

-- Various traversal

class DLogic a where
  inverse :: a -> a

class Pretty a where
  pPrint :: a -> String

-- | Simple pretty print function
--
instance Pretty Concept where
  pPrint = cata algebra
   where
    algebra :: ConceptF String -> String
    algebra (ConjunctionF a b) = "(" ++ a ++ " ⊓ " ++ b ++ ")"
    algebra (DisjunctionF a b) = "(" ++ a ++ " ⊔ " ++ b ++ ")"
    algebra (NotF a)           = "(" ++ "¬" ++ a ++ ")"
    algebra (ImpliesF a b)     = "(" ++ a ++ " → " ++ b ++ ")"
    algebra (IfOnlyIfF a b)    = "(" ++ a ++ " ↔ " ++ b ++ ")"
    algebra (AtLeastF r c)     = "(" ++ "∃" ++ show r ++ "." ++ c ++ ")"
    algebra (ForAllF r c)      = "(" ++ "∀" ++ show r ++ "." ++ c ++ ")"
    algebra (AtomicF a)        = a

instance Pretty CGI where
  pPrint (Subsumes a b) = pPrint a ++ " ⊑ " ++ pPrint b
  pPrint (Equivalent a b) = pPrint a ++ " ≡ " ++ pPrint b

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
expandConcept :: Member (State TableauxState) r => Assertion -> Eff r (Maybe Expansion)
expandConcept = \case
  CAssertion (Conjunction a b) x -> pure . Just $ Seq [CAssertion a x, CAssertion b x]
  CAssertion (Disjunction a b) x -> pure . Just $ Branch [CAssertion a x, CAssertion b x]
  CAssertion (AtLeast r c) x -> do 
    z <- newIndividual
    pure . Just $ Seq [RAssertion r x z, CAssertion c z]
  CAssertion (ForAll r c) x -> do
    fils <- fillers r x -- find all existing fillers of R(_, i)
    let assertions = fmap (CAssertion c) fils -- add assertions for them
    pure . Just . Seq $ assertions
  _ -> pure Nothing

instance DLogic Concept where
  -- | Inverse a concept. After the inversion conversion to dnf takes place
  inverse = toDNF . Not

instance DLogic Assertion where
  inverse (CAssertion c i) = CAssertion (inverse c) i
  -- TODO: what about RAssertions
  

-- | Checks if two are compement
--
-- >>> c1 = Atomic "A"
-- >>> c2 = Not (Atomic "A")
-- >>> c1 `isComplement` c2
-- True
--
-- >>> c1 `isComplement` c1
-- False
--
isComplement :: Assertion -> Assertion -> Bool
isComplement c1 c2 = c1 == inverse c2

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
nextUniq :: Member (State TableauxState) r => Eff r Int
nextUniq = do
  st <- get
  let (unq:rest) = view uniq st
  put $ set uniq rest st
  pure unq

-- | Returns all the known filler individual iof the provided role
--
fillers :: Member (State TableauxState) r => Role -> Individual -> Eff r [Individual]
fillers rl ind = do
  st <- get
  let ids = fmap (\(RAssertion _ _ b) -> b)
           . filter (\(RAssertion r a _) -> r == rl && a == ind)
           $ view roles st
  pure ids

solve :: ([Writer String, State TableauxState] <:: r) => Eff r Interpretation
solve = do
  st@Tableaux{..} <- get
  case _frontier of
    []    -> do
      debugApp "Branch completed\n"
      modify $ set status Completed -- nothing to expand more
      pure . Just $ _intrp          -- update status and return the interpretation
    (c:cs) -> do
      res <- expandConcept c
      case res of
        Just(Seq cs') -> do -- and block
          debugApp "Conjunction found\n"
          modify $ set frontier (cs' <> cs)
          solve
        Just(Branch cs') -> do -- or block
          debugApp "Disjunction found\n"
          let newStates :: [(TableauxState, String)]
              newStates = do -- create branched states and run them
                c' <- cs'
                let st' = set frontier (c':cs) st
                pure . run . runMonoidWriter . execState st' $ solve -- solve each branch
          mapM_ (debugApp . unlines . fmap ("   " <>) . lines .  snd) newStates
          pure . getInterpretation . map fst $ newStates
        Nothing -> -- no further expansion
          case clashesWith c _intrp of
            Just z -> do -- clash found; terminate this branch
              modify $ set status (ClashFound $ ClashException c z)
              debugApp . show $ ClashException c z
              pure Nothing
            Nothing -> do -- No clash 
              debugApp $ "Adding " <> show c <> " to KB\n"
              modify $ set frontier cs . over intrp (c:) -- remove concept from frontier
                                                      -- add concept to kb
              solve                 -- and continue


-- | Creates a new individual
--
newIndividual :: Member (State TableauxState) r => Eff r Individual
newIndividual = Individual . show <$> nextUniq

-- | Utility function to handle logging process
-- **Attention**: Adding actual implementation (e.g. using writer or debug) will have as a
-- result all the available branches to be actually expanded in order for the
-- to be collected. For performance reasons the actual logging should be trigger only
-- for debugging purposes
--
debugApp :: Member (Writer String) r => String -> Eff r () 
debugApp = const . pure $ () -- do nothing
--debugApp = tell msg -- log to writer
--debugApp msg = trace msg (tell msg) -- print to console and log to writer

-- | Provided a list of @TableauxState it tries to find and return the first
-- clash-free completed interpretation
--
getInterpretation :: [TableauxState] -> Interpretation
getInterpretation = safeHead      -- a single interpretation is enough 
                  . map (view intrp) -- extract their interpretation
                  . filter ((/= Active) . view status) -- get only the completed tableaux

atomicA, atomicB, atomicC, atomicD :: Concept
example1, example2, example3, example4 :: Concept
atomicA = Atomic "A"
atomicB = Atomic "B"
atomicC = Atomic "C"
atomicD = Atomic "D"
example1 = Not atomicA
example2 = Conjunction atomicA atomicB
example3 = Disjunction atomicA (Conjunction atomicD atomicB)
example4 = Conjunction atomicA example1


initialState :: TableauxState
initialState = Tableaux {
    _frontier = [CAssertion example3 (Individual "007")]
  , _intrp    = []
  , _inds     = []
  , _status   = Active
  , _roles    = []
  , _uniq     = [1..]
  }

main :: IO () -- (Interpretation, String)
main = do
  let (intrp, logs) = run . evalState initialState . runMonoidWriter $ solve 
      theLines = [ ("Concept: " <> ) . show . head . view frontier $ initialState
                 , "**Logging**"
                 , "-----------"
                 , ""
                 , logs
                 , "-----------"
                 , "Interpretation: " <> show intrp
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

