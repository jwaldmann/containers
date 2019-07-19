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
import Data.List (foldl')
import Data.Monoid (Sum(..))
import Control.Monad (guard)
import Gauge (bgroup, bench, defaultMain, whnf)

main = do
  defaultMain
    [ bgroup "det/hard" $ do
        n <- [1 .. 20]
        return $ bench ("n=" <> show n)
            $ whnf (size . det0 2) $ hard_nfa n
    ]


-- evaluate this expression while typing:
-- ghcid -W -Ttest benchmarks/OrdIntSet.hs 
test = do
  let a = hard_nfa 4
  print_nfa a
  print_dfa $ det0 2 a

print_nfa :: NFA -> IO ()
print_nfa a = mapM_ putStrLn $ do
  (c,t) <- IM.toList a
  (p,qs) <- IM.toList t
  return $ unwords [ show p, "(", show c, ")", show qs ]

print_dfa :: DFA -> IO ()
print_dfa a = mapM_ putStrLn $ do
  (c,t) <- IM.toList a
  (p,q) <- M.toList t
  return $ unwords [ show p, "(", show c, ")", show q ]
  

newtype State = State Int deriving (Num, Enum)
newtype Sigma = Sigma Int deriving (Num, Enum, Eq)

-- | just the transistion system,
-- we ignore initial and final states
type NFA = IntMap (IntMap IntSet)
-- ^ Sigma -> State -> Set State

type DFA = IntMap (M.Map IntSet IntSet)
-- ^ Sigma -> Set State -> Set State

size :: DFA -> Int
size = getSum . foldMap (Sum . length)

det :: Sigma -> IntSet -> NFA -> DFA
det sigma initial aut =
  let get :: State -> Sigma -> IntSet
      get (State p) (Sigma s) = IM.findWithDefault IS.empty p
              $ IM.findWithDefault IM.empty s aut
      go :: DFA -> S.Set IntSet -> S.Set IntSet -> DFA
      go !accu !done !todo = case S.minView todo of
        Nothing -> accu
        Just (t, odo) ->
          if S.member t done
          then go accu done odo
          else let ts = do
                     s <- [0 .. sigma-1]
                     let next :: IntSet
                         next =
                           -- IS.foldMap (\p -> get (State p) s) t
                           foldMap (\p -> get (State p) s) $ IS.toList t
                     return (t, s, next)
               in  go (union_dfa (dfa ts) accu)
                      (S.insert t done)
                      (foldl' (\ o (_,_,q) -> S.insert q o) odo ts)
  in go IM.empty S.empty $ S.singleton initial  
  

det0 :: Sigma -> NFA -> DFA
det0 sigma = det sigma $ IS.singleton 0

type Transition = (State, Sigma, State)

nfa :: [Transition ] -> NFA 
nfa ts = IM.fromListWith ( IM.unionWith IS.union )
  $ map (\(State p,Sigma s,State q) ->
           (s, IM.singleton p (IS.singleton q))) ts

dfa :: [(IntSet, Sigma, IntSet)] -> DFA
dfa ts = IM.fromListWith ( M.unionWith ( error "WAT") )
  $ map (\( p, Sigma s, q) ->
           (s, M.singleton p q)) ts

union_dfa a b = IM.unionWith (M.unionWith (error "WAT")) a b

-- | for the language Sigma^* 1 Sigma^{n-2}  where Sigma={0,1}.
-- this NFA has  n  states. DFA has 2^(n-1) states
-- since it needs to remember the last n characters.
hard_nfa :: Int -> NFA
hard_nfa n = nfa
  $ [ (0, 0, 0), (0,1,0), (0, 1, 1) ]
  <> do k <- [1 .. State n - 2] ; c <- [0,1] ; return (k,c,k+1)

