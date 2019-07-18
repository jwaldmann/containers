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
  defaultMain
    [ bgroup "det/hard" $ do
        n <- [1 .. 20]
        return $ bench ("n=" <> show n)
            $ whnf (M.size . det0 2) $ hard_nfa n
    ]


-- evaluate this expression while typing:
-- ghcid -W -Ttest benchmarks/OrdIntSet.hs 
test = do
  let a = hard_nfa 10
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

-- | for the language Sigma^* 1 Sigma^{n-2}  where Sigma={0,1}.
-- this NFA has  n  states. DFA has 2^(n-1) states
-- since it needs to remember the last n characters.
hard_nfa n = nfa
  $ [ (0, 0, 0), (0,1,0), (0, 1, 1) ]
  <> do k <- [1 .. State n - 2] ; c <- [0,1] ; return (k,c,k+1)

