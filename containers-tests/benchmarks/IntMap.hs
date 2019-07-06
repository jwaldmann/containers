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
  defaultMain $ do
    e <- [ 10, 15 .. 25 ]
    return $ bgroup ("2^" <> show e)
      [ bulk
        [ ("contiguous/overlapping", [1..2^e], [1..2^e])
      	, ("contiguous/disjoint"   , [1,3..2^(e+1)], [2,4..2^(e+1)])
      	, ("sparse/overlapping"    , map (^2) [1..2^e], map (^2) [1..2^e])
      	, ("sparse/disjoint"   , map (^2) [1,3..2^(e+1)], map (^2) [2,4..2^(e+1)])
      	, ("random", take (2^e) $ random_from 1 , take (2^e) $ random_from 2 )
      	]
      , pointwise
      	[ ("contiguous", [1..2^e])
      	, ("interleaved", [0..2^e-1] >>= \ x -> [x, x + 2^e ])
      	, ("sparse", map (^2) [1..2^e] )
      	, ("random", take (2^e) $ random_from 1 )
      	]
      ]

-- | lazy list of pseudo-random numbers from linear congruential generator,
-- coefficients taken from "the BSD rand generator", as cited in
-- https://www.gnu.org/software/gsl/doc/html/rng.html#c.gsl_rng_rand
random_from :: Int -> [Int]
random_from s =
  iterate (\x -> mod (1103515245 * x + 12345) (2^31)) s

bulk ::  [(String, [Int], [Int])] -> Benchmark
bulk nkks = bgroup "bulk" $ do
  let naive_union a b = M.foldlWithKey' (\ m k v -> M.insert k v m) a b
      naive_intersection a b = M.filterWithKey (\ k _ -> M.member k a) b
      naive_difference a b = M.filterWithKey (\ k _ -> not (M.member k b)) a
  (n, keys1, keys2) <- nkks
  let m1 = M.fromList $ zip keys1 $ repeat (1 :: Int)
      m2 = M.fromList $ zip keys2 $ repeat (1 :: Int)
  return $ bgroup n 
      [ bench "union" $ whnf ( M.size . uncurry M.union) (m1,m2)
      , bench "naive_union" $ whnf ( M.size . uncurry naive_union) (m1,m2)
      , bench "intersection" $ whnf ( M.size . uncurry M.intersection ) (m1,m2)
      , bench "naive_intersection" $ whnf ( M.size . uncurry naive_intersection ) (m1,m2)
      , bench "difference" $ whnf ( M.size . uncurry M.difference ) (m1,m2)
      , bench "naive_difference" $ whnf ( M.size . uncurry naive_difference ) (m1,m2)
      ]

pointwise :: [(String, [Int])] -> Benchmark
pointwise nks = bgroup "pointwise" $ do
  (n, keys) <- nks
  let values = repeat 1 -- does not matter anyway?
      elems = zip keys values
      m = M.fromList elems :: M.IntMap Int
  return $ bgroup n
        [ bench "lookup" $  whnf (lookup keys) m
        , bench "insert" $  whnf (ins elems) M.empty
        , bench "insertWith empty" $  whnf (insWith elems) M.empty
        , bench "insertWith update" $  whnf (insWith elems) m
        , bench "insertWith' empty" $  whnf (insWith' elems) M.empty
        , bench "insertWith' update" $  whnf (insWith' elems) m
        , bench "insertWithKey empty" $  whnf (insWithKey elems) M.empty
        , bench "insertWithKey update" $  whnf (insWithKey elems) m
        , bench "insertWithKey' empty" $  whnf (insWithKey' elems) M.empty
        , bench "insertWithKey' update" $  whnf (insWithKey' elems) m
        , bench "insertLookupWithKey empty" $  whnf (insLookupWithKey elems) M.empty
        , bench "insertLookupWithKey update" $  whnf (insLookupWithKey elems) m
        , bench "map" $  whnf (M.map (+ 1)) m
        , bench "mapWithKey" $  whnf (M.mapWithKey (+)) m
        , bench "foldlWithKey" $  whnf (ins elems) m
        , bench "foldlWithKey'" $  let sum k v1 v2 = k + v1 + v2 in whnf (M.foldlWithKey' sum 0) m
        , bench "foldrWithKey" $  let consPair k v xs = (k, v) : xs in whnf (M.foldrWithKey consPair []) m
        , bench "delete" $  whnf (del keys) m
        , bench "update" $  whnf (upd keys) m
        , bench "updateLookupWithKey" $  whnf (upd' keys) m
        , bench "alter"  $  whnf (alt keys) m
        , bench "mapMaybe" $  whnf (M.mapMaybe maybeDel) m
        , bench "mapMaybeWithKey" $  whnf (M.mapMaybeWithKey (const maybeDel)) m
        , bench "fromList" $  whnf M.fromList elems
        , bench "fromList_via_foldl_insert" $  whnf (foldl' (\m (k,v) -> M.insert k v m) M.empty) elems
        , bench "fromAscList" $  whnf M.fromAscList elems
        , bench "fromDistinctAscList" $  whnf M.fromDistinctAscList elems
        , bench "minView" $  whnf (maybe 0 (\((k,v), m) -> k+v+M.size m) . M.minViewWithKey)
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
