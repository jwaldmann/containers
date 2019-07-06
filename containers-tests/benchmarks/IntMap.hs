{-# LANGUAGE BangPatterns #-}
module Main where

import Control.DeepSeq (rnf)
import Control.Exception (evaluate)
import Gauge (bench, bgroup, defaultMain, whnf, Benchmark)
import Data.List (foldl')
import qualified Data.IntMap as M
import qualified Data.IntMap.Strict as MS
import Data.Maybe (fromMaybe)
import Prelude hiding (lookup)

main = do
  defaultMain
    [ bulk $
      [ ("contiguous/overlapping", [1..2^12], [1..2^12])
      , ("contiguous/disjoint"   , [1,3..2^13], [2,4..2^13])
      , ("sparse/overlapping"    , map (^2) [1..2^12], map (^2) [1..2^12])
      , ("sparse/disjoint"   , map (^2) [1,3..2^13], map (^2) [2,4..2^13])
      , ("random", take (2^12) $ random_from 1 , take (2^12) $ random_from 2 )
      ] >> []
    , pointwise
      [ ("contiguous", [1..2^12])
      , ("sparse", map (^2) [1..2^12] )
      , ("random", take (2^12) $ random_from 1 )
      ]
    ]

random_from s =
  iterate (\x -> mod (1664525 *x + 1013904223) (2^32)) s

bulk ::  [(String, [Int], [Int])] -> Benchmark
bulk nkks = bgroup "bulk" $
  let naive_union a b = M.foldlWithKey' (\ m k v -> M.insert k v m) a b
      naive_intersection a b = M.filterWithKey (\ k _ -> M.member k a) b
      naive_difference a b = M.filterWithKey (\ k _ -> not (M.member k b)) a
      benches name fun = bgroup name $ do
        (n, keys1, keys2) <- nkks
	let m1 = M.fromList $ zip keys1 $ repeat (1 :: Int)
	    m2 = M.fromList $ zip keys2 $ repeat (1 :: Int)
        sum m1 `seq` sum m2 `seq` return ( bench n ( fun m1 m2 ))
  in  [ benches "union" $ \ m1 m2 -> whnf ( M.size . uncurry M.union) (m1,m2)
      , benches "naive_union" $ \ m1 m2 -> whnf ( M.size . uncurry naive_union) (m1,m2)
      , benches "intersection" $ \ m1 m2 -> whnf ( M.size . uncurry M.intersection ) (m1,m2)
      , benches "naive_intersection" $ \ m1 m2 -> whnf ( M.size . uncurry naive_intersection ) (m1,m2)
      , benches "difference" $ \ m1 m2 -> whnf ( M.size . uncurry M.difference ) (m1,m2)
      , benches "naive_difference" $ \ m1 m2 -> whnf ( M.size . uncurry naive_difference ) (m1,m2)
      ]

pointwise :: [(String, [Int])] -> Benchmark
pointwise nks = 
  let benches name fun = bgroup name $ do
        (n, keys) <- nks
        let values = repeat 1 -- does not matter anyway?
            elems = zip keys values
            m = M.fromList elems :: M.IntMap Int
        seq (sum m) $ return $ bench n $ fun keys elems m
  in  bgroup "pointwise" 
        [ benches "lookup" $ \ keys elems m -> whnf (lookup keys) m
        , benches "insert" $ \ keys elems m -> whnf (ins elems) M.empty
        , benches "insertWith empty" $ \ keys elems m -> whnf (insWith elems) M.empty
        , benches "insertWith update" $ \ keys elems m -> whnf (insWith elems) m
        , benches "insertWith' empty" $ \ keys elems m -> whnf (insWith' elems) M.empty
        , benches "insertWith' update" $ \ keys elems m -> whnf (insWith' elems) m
        , benches "insertWithKey empty" $ \ keys elems m -> whnf (insWithKey elems) M.empty
        , benches "insertWithKey update" $ \ keys elems m -> whnf (insWithKey elems) m
        , benches "insertWithKey' empty" $ \ keys elems m -> whnf (insWithKey' elems) M.empty
        , benches "insertWithKey' update" $ \ keys elems m -> whnf (insWithKey' elems) m
        , benches "insertLookupWithKey empty" $ \ keys elems m -> whnf (insLookupWithKey elems) M.empty
        , benches "insertLookupWithKey update" $ \ keys elems m -> whnf (insLookupWithKey elems) m
        , benches "map" $ \ keys elems m -> whnf (M.map (+ 1)) m
        , benches "mapWithKey" $ \ keys elems m -> whnf (M.mapWithKey (+)) m
        , benches "foldlWithKey" $ \ keys elems m -> whnf (ins elems) m
        , benches "foldlWithKey'" $ \ keys elems m -> let sum k v1 v2 = k + v1 + v2 in whnf (M.foldlWithKey' sum 0) m
        , benches "foldrWithKey" $ \ keys elems m -> let consPair k v xs = (k, v) : xs in whnf (M.foldrWithKey consPair []) m
        , benches "delete" $ \ keys elems m -> whnf (del keys) m
        , benches "update" $ \ keys elems m -> whnf (upd keys) m
        , benches "updateLookupWithKey" $ \ keys elems m -> whnf (upd' keys) m
        , benches "alter"  $ \ keys elems m -> whnf (alt keys) m
        , benches "mapMaybe" $ \ keys elems m -> whnf (M.mapMaybe maybeDel) m
        , benches "mapMaybeWithKey" $ \ keys elems m -> whnf (M.mapMaybeWithKey (const maybeDel)) m
        , benches "fromList" $ \ keys elems m -> whnf M.fromList elems
        , benches "fromList_via_foldl_insert" $ \ keys elems m -> whnf (foldl' (\m (k,v) -> M.insert k v m) M.empty) elems
        , benches "fromAscList" $ \ keys elems m -> whnf M.fromAscList elems
        , benches "fromDistinctAscList" $ \ keys elems m -> whnf M.fromDistinctAscList elems
        , benches "minView" $ \ keys elems m -> whnf (maybe 0 (\((k,v), m) -> k+v+M.size m) . M.minViewWithKey)
                    (M.fromList $ zip [1..10] [1..10])
        ]

add3 :: Int -> Int -> Int -> Int
add3 x y z = x + y + z
{-# INLINE add3 #-}

lookup :: [Int] -> M.IntMap Int -> Int
lookup xs m = foldl' (\n k -> fromMaybe n (M.lookup k m)) 0 xs

ins :: [(Int, Int)] -> M.IntMap Int -> M.IntMap Int
ins xs m = foldl' (\m (k, v) -> M.insert k v m) m xs

insWith :: [(Int, Int)] -> M.IntMap Int -> M.IntMap Int
insWith xs m = foldl' (\m (k, v) -> M.insertWith (+) k v m) m xs

insWithKey :: [(Int, Int)] -> M.IntMap Int -> M.IntMap Int
insWithKey xs m = foldl' (\m (k, v) -> M.insertWithKey add3 k v m) m xs

insWith' :: [(Int, Int)] -> M.IntMap Int -> M.IntMap Int
insWith' xs m = foldl' (\m (k, v) -> MS.insertWith (+) k v m) m xs

insWithKey' :: [(Int, Int)] -> M.IntMap Int -> M.IntMap Int
insWithKey' xs m = foldl' (\m (k, v) -> MS.insertWithKey add3 k v m) m xs

data PairS a b = PS !a !b

insLookupWithKey :: [(Int, Int)] -> M.IntMap Int -> (Int, M.IntMap Int)
insLookupWithKey xs m = let !(PS a b) = foldl' f (PS 0 m) xs in (a, b)
  where
    f (PS n m) (k, v) = let !(n', m') = M.insertLookupWithKey add3 k v m
                        in PS (fromMaybe 0 n' + n) m'

del :: [Int] -> M.IntMap Int -> M.IntMap Int
del xs m = foldl' (\m k -> M.delete k m) m xs

upd :: [Int] -> M.IntMap Int -> M.IntMap Int
upd xs m = foldl' (\m k -> M.update Just k m) m xs

upd' :: [Int] -> M.IntMap Int -> M.IntMap Int
upd' xs m = foldl' (\m k -> snd $ M.updateLookupWithKey (\_ a -> Just a) k m) m xs

alt :: [Int] -> M.IntMap Int -> M.IntMap Int
alt xs m = foldl' (\m k -> M.alter id k m) m xs

maybeDel :: Int -> Maybe Int
maybeDel n | n `mod` 3 == 0 = Nothing
           | otherwise      = Just n
