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

import           Data.Functor.Foldable          (cata)
import           Data.Functor.Foldable.TH       (makeBaseFunctor)
import           Data.List                      (intercalate,  nub)
import qualified Data.Map.Strict                                    as M
import           Data.Maybe                     (mapMaybe)
import           Lens.Micro.Platform

-- import Debug.Trace

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

