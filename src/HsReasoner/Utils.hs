module HsReasoner.Utils where

import           Data.List        (intersect, nub, sort, sortBy)
import           Data.Map         (Map)
import qualified Data.Map    as M
import           Data.Maybe       (fromMaybe)
import           Data.Ord         (comparing, Down(..))
import qualified Data.Set    as S

-- import           Debug.Trace

-- | Given a list of pairwise different elements, the function return the maximum (in length) list
-- with distinct elements
-- 
-- >>> :{
-- let difList =
--             [ (1,2)
--             , (1,4)
--             , (2,4)
--             , (3,4)
--             ]
-- in maxDistinctSet difList
-- :}
-- [1,2,4]
--
maxDistinctSet :: (Show a, Ord a) => [(a, a)] -> [a]
maxDistinctSet = fromMaybe [] . safeHead            -- get the largest, if exists
               . sortBy (comparing (Down . length)) -- sort larger sets first
               . distinctSets                       -- all sets

singleton :: a -> [a]
singleton = pure

safeHead :: [a] -> Maybe a
safeHead []    = Nothing
safeHead (x:_) = Just x

distinctSets :: (Show a, Ord a) => [(a, a)] -> [[a]]
distinctSets pl = allSets <> singletons
 where
  sortedPairs = (\(x, y) -> if x > y then (y,x) else (x,y)) <$> pl
  theMap = M.fromListWith (<>) . fmap (fmap singleton) $ sortedPairs
  els    = nub . sort $ M.keys theMap <> concat (M.elems theMap)
  singletons = pure <$> els
  allSets = filter ((>1) . length) (maxDistincts theMap els)

  maxDistincts :: (Show a, Ord a) => Map a [a] -> [a] -> [[a]]
  maxDistincts m = go (M.filter (not.null) m)
   where
    go _  [] = []
    go mp (x:xs)
      | M.null mp = [[x]]
      | otherwise = case1 <> case2
     where
      candidates = M.findWithDefault [] x mp
      mapTail = M.delete x mp
      newMap = M.restrictKeys mapTail (S.fromList candidates)
      newMap' = fmap (intersect candidates) newMap
      case1 = (x:) <$> maxDistincts newMap' (filter (`elem` candidates) xs)
      case2 = maxDistincts mapTail xs


