{-# language
  GeneralizedNewtypeDeriving, TypeFamilies, BangPatterns, StandaloneDeriving
#-}

module Main where

import Data.IntSet (IntSet)
import Data.IntSet.Internal
import qualified Data.IntSet as IS
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.Foldable as F
import qualified Data.List
import Data.List (mapAccumL)
import Data.Maybe (catMaybes)
import Data.Bits (shift, complement, (.&.), (.|.), xor, bit, countLeadingZeros)
import Utils.Containers.Internal.BitUtil
import Data.Monoid (Sum(..))
import Control.Monad (guard, forM_, when)
import Test.LeanCheck
import Test.LeanCheck.Utils.Types (unNat)
import Gauge (bgroup, bench, defaultMain, whnf)

main = do
  defaultMain
    [ bgroup "det/hard" $ do
        n <- [1 .. 20]
        return $ bgroup  ("n=" <> show n) $ do
          delta <- take 5 $ iterate (*3) 1
          return $ bench ("delta=" <> show delta)
            $ whnf (IM.size . det0 2) $ hard_nfa delta n
    ]

test2 = do
  print $ shorter 64 0
  let t1@(Tip p1 b1) = fromList [100]
      t2@(Bin p2 m2 l2 r2) = fromList [100,200]
  print (p1,b1)      
  print (p2,m2,l2,r2)
  print (compare t1 t2, relate t1 t2)
  print (compare t1 l2, relate t1 l2)

  when False $ do
    putStrLn "combine"       ; checkFor (10^6) prop_combine
    putStrLn "combine_left"  ; checkFor (10^6) prop_combine_left
    putStrLn "combine_right" ; checkFor (10^6) prop_combine_right

  forM_ [1, 10, 100] $ \ s -> do
    putStrLn $ "compare==cis (scaled by " <> show s <> ")"
    checkFor (10^3) $ \ a0 b0 ->
      let a = IS.map (*s) a0
          b = IS.map (*s) b0
      in compare a b == cis a b

instance Listable IntSet where
  tiers = mapT IS.fromList tiers

-- | detailed outcome of lexicographic comparison of lists.
-- w.r.t. Ordering, there are two extra cases,
-- since (++) is not monotonic w.r.t. lex. order on lists
-- (which is used by definition):
-- consider comparison of  (Bin [0,3,4] [ 6] ) to  (Bin [0,3] [7] )
-- where [0,3,4] > [0,3]  but [0,3,4,6] < [0,3,7].

data Relation
  = Less  -- ^ holds for [0,3,4] [0,3,5,1]
  | Prefix -- ^ holds for [0,3,4] [0,3,4,5]
  | Equals -- ^  holds for [0,3,4] [0,3,4]
  | FlipPrefix -- ^ holds for [0,3,4] [0,3]
  | Greater -- ^ holds for [0,3,4] [0,2,5]
  deriving (Show, Eq)

-- | compare IntSet
cis :: IntSet -> IntSet -> Ordering
cis a b = case relate a b of
  Less -> LT
  Prefix -> LT
  Equals -> EQ
  FlipPrefix -> GT
  Greater -> GT

-- The following gets complicated since integers are
-- effectively handled (in the tree) by their binary representation:
-- if a bit is zero, the left branch is taken.
-- This also holds for the sign bit (the MSB),
-- so negative numbers are in the right subtree:
-- after    Bin p m l r = fromList [-1,0]
-- we have  l = fromList [0], r = fromList [-1]

-- | does the set contain both numbers >= 0 and numbers < 0 ?
mixed :: IntSet -> Bool
mixed (Bin p m l r) = m == (2 ^( wordSize -1 ))

{- nota bene:

this example shows that the prefix can drop (from 64 to 0)
while inserting a strictly larger number:

fromList [100]     = Tip 64 (2^32)
fromList [100,200] = Bin 0 128 (fromList [100]) (fromList [200])



-}

relate :: IntSet -> IntSet -> Relation
relate Nil Nil = Equals
relate Nil t2 = Prefix
relate t1 Nil = FlipPrefix
relate (Tip p1 bm1) (Tip p2 bm2) = case compare p1 p2 of
  LT -> Less
  EQ -> relateBM bm1 bm2
  GT -> Greater
relate t1@(Bin p1 m1 l1 r1) t2@(Bin p2 m2 l2 r2)
  | mixed t1 && mixed t2 = combine (relate r1 r2) (relate l1 l2)
  | mixed t1 = combine_left (relate r1 t2)
  | mixed t2 = combine_right (relate t1 r2)
  | p1 == p2 = combine (relate l1 l2) (relate r1 r2)
  | shorter m1 m2 = combine_left (relate l1 t2)
  | shorter m2 m1 = combine_right (relate t1 l2)
  | otherwise = case compare p1 p2 of LT -> Less ; GT -> Greater
relate t1@(Bin p1 m1 l1 r1) t2@(Tip p2 bm2)
  | mixed t1 = combine_left (relate r1 t2)
  -- FIXME
  | otherwise = case compare p1 p2 of
      LT -> Less
      EQ -> combine_left (relate l1 t2)
      GT -> Greater
relate t1@(Tip p1 bm1) t2@(Bin p2 m2 l2 r2)
  | mixed t2 = combine_right (relate t1 r2)
  -- FIXME (counterexample is note above)
  | otherwise =  case compare p1 p2 of
      LT -> Less
      EQ -> combine_right (relate t1 l2)
      GT -> Greater

rel :: [Int] -> [Int] -> Relation
rel [] [] = Equals ; rel [] ys = Prefix ; rel xs [] = FlipPrefix
rel (x:xs) (y:ys) = case compare x y of LT -> Less ; EQ -> rel xs ys ; GT -> Greater

-- | for testing:
-- in Split xs ys, xs are increasing up to -1, ys are increasing from 1
data Split = Split [Int] [Int] deriving Show

prop_combine (Split l1 r1) (Split l2 r2) =
  rel (l1 <> r1) (l2 <> r2) == combine (rel l1 l2) (rel r1 r2)

combine :: Relation -> Relation -> Relation
combine r eq = case r of
      Less -> Less
      Prefix -> Greater
      Equals -> eq
      FlipPrefix -> Less
      Greater -> Greater

prop_combine_left (Split l1 r1) (Split l2 _) = let r2 = [] in
  rel (l1 <> r1) (l2 <> r2) == combine_left (rel l1 l2)

combine_left :: Relation -> Relation
combine_left r = case r of
      Less -> Less
      Prefix -> Greater
      Equals -> FlipPrefix
      FlipPrefix -> FlipPrefix
      Greater -> Greater

prop_combine_right (Split l1 _) (Split l2 r2) = let r1 = [] in
  rel (l1 <> r1) (l2 <> r2) == combine_right (rel l1 l2)

combine_right :: Relation -> Relation
combine_right r = case r of
      Less -> Less
      Prefix -> Prefix
      Equals -> Prefix
      FlipPrefix -> Less
      Greater -> Greater


instance Listable Split where
  tiers = mapT ( \ (bs,cs) ->
                   Split (scanr (\ b a -> a - fromEnum b) (-1) (bs::[Bool]))
                         (scanl (\ a c -> a + fromEnum c) ( 1) (cs::[Bool]))
               ) tiers



bmtol m = toList $ Tip 0 m

relateBM :: BitMap -> BitMap -> Relation
relateBM w1 w2 | w1 == w2 = Equals
relateBM w1 w2 =    --  e.g.,  3=11 1=01
  let delta = xor w1 w2  -- 2=10
      lowest_diff_mask = delta .&. complement (delta-1) -- 10
      prefix = (complement lowest_diff_mask + 1)
            .&. (complement lowest_diff_mask)   -- 1..100
  in  if 0 == lowest_diff_mask .&. w1
      then if 0 == w1 .&. prefix
           then Prefix else Greater
      else if 0 == w2 .&. prefix
           then FlipPrefix else Less

shorter :: Mask -> Mask -> Bool
shorter m1 m2
  = (natFromInt m1) > (natFromInt m2)
{-# INLINE shorter #-}

-- A "Nat" is a natural machine word (an unsigned Int)
type Nat = Word

natFromInt :: Int -> Nat
natFromInt i = fromIntegral i
{-# INLINE natFromInt #-}

intFromNat :: Nat -> Int
intFromNat w = fromIntegral w
{-# INLINE intFromNat #-}


-- evaluate this expression while typing:
-- ghcid -W -Ttest benchmarks/OrdIntSet.hs 
test = do
  let a = hard_nfa 1 4
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
instance Show State where show (State s) = show s
newtype Sigma = Sigma Int deriving (Num, Enum, Eq)

-- | just the transistion system,
-- we ignore initial and final states
type NFA = IntMap (IntMap IntSet)
-- ^ Sigma -> State -> Set State

type DFA = IntMap (M.Map MyIntSet MyIntSet)
-- ^ Sigma -> Set State -> Set State

size :: DFA -> Int
size = getSum . foldMap (Sum . length)

{-  performance:

# standard instance Ord IntSet

det/hard/n=16                            time                 521.2 ms  
det/hard/n=17                            time                 1.192 s   
det/hard/n=18                            time                 2.613 s   
det/hard/n=19                            time                 6.302 s   
det/hard/n=20                            time                 13.79 s   

# using function `cis` defined here

det/hard/n=16                            time                 167.6 ms  
det/hard/n=17                            time                 359.1 ms  
det/hard/n=18                            time                 819.8 ms  
det/hard/n=19                            time                 1.844 s   
det/hard/n=20                            time                 4.091 s   

-}

newtype MyIntSet = My { ym :: IntSet } deriving (Semigroup, Monoid, Show, Eq)

-- deriving instance Ord MyIntSet
instance Ord MyIntSet where compare (My a) (My b) = cis a b

det :: Sigma -> IntSet -> NFA -> DFA
det sigma initial aut =
  let get :: State -> Sigma -> MyIntSet
      get (State p) (Sigma s) = My $ IM.findWithDefault IS.empty p
              $ IM.findWithDefault IM.empty s aut
      go :: DFA -> S.Set MyIntSet -> S.Set MyIntSet -> DFA
      go !accu !done !todo = case S.minView todo of
        Nothing -> accu
        Just (t, odo) ->
          if S.member t done
          then go accu done odo
          else let ts = do
                     s <- [0 .. sigma-1]
                     let next :: MyIntSet
                         next =
                           -- IS.foldMap (\p -> get (State p) s) t
                           foldMap (\p -> get (State p) s) $ IS.toList $ ym t
                     return (t, s, next)
               in  go (union_dfa (dfa ts) accu)
                      (S.insert t done)
                      (Data.List.foldl' (\ o (_,_,q) -> S.insert q o) odo ts)
  in go IM.empty S.empty $ S.singleton $ My initial  
  

det0 :: Sigma -> NFA -> DFA
det0 sigma = det sigma $ IS.singleton 0

type Transition = (State, Sigma, State)

nfa :: [Transition ] -> NFA 
nfa ts = IM.fromListWith ( IM.unionWith IS.union )
  $ Prelude.map (\(State p,Sigma s,State q) ->
           (s, IM.singleton p (IS.singleton q))) ts

dfa :: [(MyIntSet, Sigma, MyIntSet)] -> DFA
dfa ts = IM.fromListWith ( M.unionWith ( error "WAT") )
  $ Prelude.map (\( p, Sigma s, q) ->
           (s, M.singleton p q)) ts

union_dfa a b = IM.unionWith (M.unionWith (error "WAT")) a b

-- | for the language Sigma^* 1 Sigma^{n-2}  where Sigma={0,1}.
-- this NFA has  n  states. DFA has 2^(n-1) states
-- since it needs to remember the last n characters.
-- Extra parameter delta: the automaton will use states [0, delta .. ]
-- for IntSet, larger deltas should be harder,
-- since for delta=1, all the states do fit in one Tip
hard_nfa :: State -> Int -> NFA
hard_nfa delta n = nfa
  $ [ (0, 0, 0), (0,1,0), (0, 1, delta) ]
  <> do k <- [1 .. State n - 2] ; c <- [0,1] ; return (delta * k,c,delta *(k+1))

