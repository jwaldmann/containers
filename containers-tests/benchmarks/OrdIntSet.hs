{-# language
  GeneralizedNewtypeDeriving, TypeFamilies, BangPatterns
#-}

module Main where

import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.Foldable as F
import Gauge (bgroup, bench, defaultMain, whnf)

main = do
  let sigma = 3
  defaultMain
    [ bgroup "det" $ do
        n <- takeWhile (< 10^3) $ iterate (*2) 1
        return $ bgroup ("n=" <> show n) $ do
          Sigma c <- [1 .. 2*sigma] ; let m = c * n
          return $ bench ("m=" <> show c <> "*n") 
            $ whnf (det0 sigma)
            $ random_nfa sigma (State n) m 42
    ]


-- evaluate this expression while typing:
-- ghcid -W -Ttest benchmarks/OrdIntSet.hs 
test = do
  let a = random_nfa 2 5 10 41
  print_nfa a
  print_dfa $ det0 2 a

print_nfa a = mapM_ putStrLn $ do
  (p,qs) <- IM.toList a
  return $ unwords [ show p, ":", show qs ]
  
print_dfa a = mapM_ putStrLn $ do
  (p,qs) <- M.toList a
  return $ unwords [ show p, ":", show qs ]
  

newtype State = State Int deriving (Num, Enum)
newtype Sigma = Sigma Int deriving (Num, Enum)

-- | just the transistion system,
-- we ignore initial and final states
type NFA = IntMap (IntMap IntSet)
type DFA = M.Map IntSet (IntMap IntSet)

det :: Sigma -> IntSet -> NFA -> DFA
det sigma initial aut =
  let get :: State -> Sigma -> IntSet
      get (State p) (Sigma s) = IM.findWithDefault IS.empty s
              $ IM.findWithDefault IM.empty p aut
      go :: DFA -> S.Set IntSet -> S.Set IntSet -> DFA
      go !accu !done !todo = case S.minView todo of
        Nothing -> accu
        Just (t, odo) ->
          if S.member t done
          then go accu done odo
          else let ts :: IntMap IntSet
                   ts = IM.fromList $ do
                     s <- [0 .. sigma-1]
                     let next :: IntSet
                         next =
                           -- IS.foldMap (\p -> get (State p) s) t
                           foldMap (\p -> get (State p) s) $ IS.toList t
                     return (fromEnum s, next)
               in  go (M.insertWith (error "WAT") t ts accu)
                      (S.insert t done)
                      (IM.foldl' (flip S.insert) odo ts)
  in  go M.empty S.empty $ S.singleton initial  
  

det0 sigma = det sigma $ IS.singleton 0

type Transition = (State, Sigma, State)

nfa :: [Transition ] -> NFA 
nfa ts = IM.fromListWith ( IM.unionWith IS.union )
  $ map (\(State p,Sigma s,State q) ->
           (p, IM.singleton s (IS.singleton q))) ts

random_nfa
  :: Sigma -- ^ size of alphabet
  -> State -- ^ number of states
  -> Int -- ^ number of edges
  -> Seed
  -> NFA
random_nfa (Sigma a) (State n) m s = nfa
  $ map (\ (x,y,z) ->
           (State $ mod x n, Sigma $ mod y a, State $ mod z n))
  $ take m $ triples $ random_ints s

triples :: [a] -> [(a,a,a)]
triples (x:y:z:later) = (x,y,z) : triples later


newtype Seed = Seed Int deriving Num

-- | lazy list of pseudo-random numbers from linear congruential generator,
-- coefficients taken from "the BSD rand generator", as cited in
-- https://www.gnu.org/software/gsl/doc/html/rng.html#c.gsl_rng_rand
random_ints :: Seed -> [Int]
random_ints (Seed s) =
  iterate (\x -> mod (1103515245 * x + 12345) (2^31)) s
