{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
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
--import Control.Monad.State
import Data.Functor.Foldable          (cata, embed)
import Data.Functor.Foldable.TH       (makeBaseFunctor)
import Data.Maybe                     (isJust)
import Lens.Micro.Platform

import Debug.Trace

type Label = String

data Concept
  = Conjunction Concept Concept -- ^ AND
  | Disjunction Concept Concept -- ^ OR
  | Not Concept                 -- ^ NOT
  | Implies Concept Concept     -- ^ A -> B
  | IfOnlyIf Concept Concept    -- ^ A <-> B
  | Atomic Label deriving (Show, Eq) -- ^ A

makeBaseFunctor ''Concept

data ClashException = ClashException Concept Concept deriving (Eq)
instance Show ClashException where
  show (ClashException c1 c2) = "Clash found between '" ++ show c1 ++ "' and '" ++ show c2 ++ "'"

data TableauxState = Tableaux
  { _frontier :: [Concept] -- ^ Concepts to be expanded
  , _kb       :: [Concept] -- ^ In practice, it holds all the true and false atomic concepts
  , _status   :: TableauxStatus -- ^ The state of the specific path
  } deriving (Show)

data TableauxStatus
  = ClashFound ClashException
  | Completed
  | Active deriving (Show, Eq)

data Expansion
  = Branch [Concept]
  | Seq [Concept] deriving (Show)

-- Some temaplte magic
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

-- | Simple pretty print function
--
pPrint :: Concept -> String
pPrint = cata algebra
 where
  algebra :: ConceptF String -> String
  algebra (ConjunctionF a b) = "(" ++ a ++ " ⊓ " ++ b ++ ")"
  algebra (DisjunctionF a b) = "(" ++ a ++ " ⊔ " ++ b ++ ")"
  algebra (NotF a)           = "(" ++ "¬" ++ a ++ ")"
  algebra (ImpliesF a b)     = "(" ++ a ++ " → " ++ b ++ ")"
  algebra (IfOnlyIfF a b)    = "(" ++ a ++ " ↔ " ++ b ++ ")"
  algebra (AtomicF a)        = a


-- | Converts a concept to DNF
--
toDNF :: Concept -> Concept
toDNF = cata algebra
 where
  algebra :: ConceptF Concept -> Concept
  algebra (NotF (Not a))           = a
  algebra (NotF (Conjunction a b)) = Disjunction (toDNF $ Not a) (toDNF $ Not b)
  algebra (NotF (Disjunction a b)) = Conjunction (toDNF $ Not a) (toDNF $ Not b)
  algebra (ImpliesF a b)           = Disjunction (toDNF $ Not a) b
  algebra (IfOnlyIfF a b)          = Conjunction (Disjunction (inverse a) b) (Disjunction a (inverse b))
  algebra c                        = embed c

-- | Tablaux expansion rules
--
expandConcept :: Concept -> Maybe Expansion
expandConcept (Conjunction a b) = Just $ Seq [a,b]
expandConcept (Disjunction a b) = Just $ Branch [a,b]
expandConcept _ = Nothing

-- | Inverse a concept. After the inversion conversion to dnf takes place
--
inverse :: Concept -> Concept
inverse = toDNF . Not

-- | Checks if two are compement
--
isComplement :: Concept -> Concept -> Bool
isComplement c1 c2 = c1 == inverse c2

-- | Checks if a concept (first argument) clashes with any of the concepts of the list
--
clashesWith :: Concept -> [Concept] -> Maybe Concept
clashesWith c = safeHead . filter (isComplement c)

-- | Checks if a concept (first argument) clashes with any of the concepts of the list
--
clashExists :: Concept -> [Concept] -> Bool
clashExists c = isJust . clashesWith c 

addConcept :: Concept -> [Concept] -> Either ClashException [Concept]
addConcept c cs = case clashesWith c cs of
                    Nothing -> Right $ c:cs
                    Just y -> Left $ ClashException c y

-- step :: TableauxState -> Either ClashException (Maybe [TableauxState])
-- step Tableaux {..}
--   | null frontier = Right Nothing
--   | otherwise     = case expandConcept (head frontier) of
--                       Nothing -> (\kb' -> Just [Tableaux (tail frontier) kb']) <$> addConcept (head frontier) kb
--                       Just (Seq xs) ->  undefined
--                       Just (Branch xs) -> undefined
-- 
solve :: Member (State TableauxState) r => Eff r (Maybe [Concept])
-- solve :: State TableauxState (Maybe [Concept])
solve = do
  st@Tableaux{..} <- get
  case _frontier of
    []    -> do
      put $ set status Completed st
      pure . Just $ _kb
    (c:cs) ->
      case expandConcept c of
        Just(Seq cs') -> do -- ^ and block
          put $ set frontier (cs' <> cs) st
          solve
        Just(Branch cs') -> do -- ^ or block
          let
            newStates :: [TableauxState]
            newStates = do -- ^ create branched states and run them
              c' <- cs'
              let st' = set frontier (c':cs) st
              pure . run $ execState st' solve -- ^ solve each branch
          pure $ getInterpretation newStates
        Nothing -> -- ^ no further expansion
          case clashesWith c _kb of
            Just z -> do -- ^ clash found; terminate this branch
              put $ set status (ClashFound $ ClashException c z) st
              pure Nothing
            Nothing -> do -- ^ No clash 
              let st' = set frontier cs st -- ^ remove concept from frontier
              put $ over kb (c:) st' -- ^ add concept to kb
              solve                 -- ^ and continue

atomicA, atomicB, atomicC, atomicD :: Concept
example1, example2, example3, example4 :: Concept
atomicA = Atomic "A"
atomicB = Atomic "B"
atomicC = Atomic "C"
atomicD = Atomic "D"
example1 = Not atomicA
example2 = Conjunction atomicA atomicB
example3 = Disjunction atomicA atomicB
example4 = Conjunction atomicA example1


initialState :: TableauxState
initialState = Tableaux {
    _frontier = [example4]
  , _kb = []
  , _status = Active
  }


main :: Maybe [Concept]
main = run $ evalState initialState solve 

--transferFrontierConceptToKB :: State TableauxState ()
--transferFrontierConceptToKB = do
--  st@Tableaux{..} <- get
--  case _frontier of
--    [] -> pure ()
--    (c:cs) -> do
--      let st' = set frontier cs st
--      put $ over kb (c:) st'


--  if null _frontier 
--  then pure . Just $ kb  -- set status Completed st
--  else undefined

getInterpretation :: [TableauxState] -> Maybe [Concept]
getInterpretation = safeHead -- a single interpretation is enough 
                  . map (view kb) -- extract their kb
                  . filter ((== Completed) . view status) -- get only the completed tableaux

-- getLogLevel :: (Member (Reader Config) r, Member (Reader Connection) r) => String -> Eff r String

-- algorithm
-- initialState = {[Concepts], []}
--  - get head (1)
--  - expand it
--    - if no expansion
--      - check for clashes
--      - if no clash
--        - add it to kb
--        - go back to (1)
--      - if clash
--        - stop execution with status "clash"
--    - if 'and' expansion
--        - add new concepts to frontier
--        - go back to (1)
--    - (otherwise) if 'or' expansion
--        - create 2 new states
--        - add one concept to their frontier
--        - map execution
                                                    

-- step Tableaux{..} = case frontier of
--   []     -> undefined
--   (x:[]) -> undefined
--   (x:xs) -> undefined

---------------
-- Utilities --
---------------

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

safeTail :: [a] -> Maybe [a]
safeTail [] = Nothing
safeTail (_:xs) = Just xs

