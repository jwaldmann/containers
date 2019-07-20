{-# language
  GeneralizedNewtypeDeriving, TypeFamilies, BangPatterns
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
import Data.Bits (shift, complement, (.&.), (.|.), xor, bit, countLeadingZeros)
import Utils.Containers.Internal.BitUtil
import Data.Monoid (Sum(..))
import Control.Monad (guard, forM_)
import Test.LeanCheck
import Test.LeanCheck.Utils.Types (unNat)
import Gauge (bgroup, bench, defaultMain, whnf)

main = do
  defaultMain
    [ bgroup "det/hard" $ do
        n <- [1 .. 20]
        return $ bench ("n=" <> show n)
            $ whnf (IM.size . det0 2) $ hard_nfa n
    ]

test2 = do
  print $ toList (Tip (-1024) 11)

  let t1 = fromList [0]
      t2@(Bin p m l r) = fromList [-1,0]
  print (p,m,l,r)
  print $ relate t1 t2
  print $ relate t1 l

  putStrLn "compare==cis (Tip, Tip)"
  checkFor (10^5) $ \ a b -> a == 0 || b == 0 ||
    let p = 2^12; q = negate $ 2^12
    in compare (Tip p a) (Tip q b) == cis (Tip p a) (Tip q b)

  forM_ [0, 2^10, negate $ 2^10 ] $ \ p -> do
    putStrLn $ "compare==cis (Tip (" <> show p <> ") *)"
    checkFor (10^5) $ \ a b ->
      compare (Tip p a) (Tip p b) == cis (Tip p a) (Tip p b)

  putStrLn "compare==cis"
  checkFor (10^6) $ \ a b -> compare a b == cis a b

instance Listable IntSet where
  tiers = mapT (IS.fromList {- . Prelude.map unNat -}  ) tiers

-- | detailed outcome of lexicographic comparison of lists.
-- w.r.t. Ordering, there are two extra cases.
data Relation
  = Less  -- ^ holds for [0,3,4] [0,3,5,1]
  | Prefix -- ^ holds for [0,3,4] [0,3,4,5]
  | Equals -- ^  holds for [0,3,4] [0,3,4]
  | FlipPrefix -- ^ holds for [0,3,4] [0,3]
  | Greater -- ^ holds for [0,3,4] [0,2,5]
  deriving Show

-- | compare IntSet
cis :: IntSet -> IntSet -> Ordering
cis a b = case relate a b of
  Less -> LT
  Prefix -> LT
  Equals -> EQ
  FlipPrefix -> GT
  Greater -> GT

relate :: IntSet -> IntSet -> Relation
relate Nil Nil = Equals
relate Nil t2 = Prefix
relate t1 Nil = FlipPrefix
relate (Tip p1 bm1) (Tip p2 bm2) = case compare p1 p2 of
  LT -> Less
  EQ -> relateBM bm1 bm2
  GT -> Greater
relate t1@(Bin p1 m1 l1 r1) t2@(Bin p2 m2 l2 r2)
  | p1 == p2 = combine (relate l1 l2) (relate r1 r2)
  | shorter m1 m2 = combine (relate l1 t2) FlipPrefix
  | shorter m2 m1 = combine (relate t1 l2) Prefix
  | otherwise = case compare p1 p2 of
      LT -> Less
      GT -> Greater
relate t1@(Bin p1 m1 l1 r1) t2@(Tip p2 bm2)
  = combine (relate l1 t2) FlipPrefix
relate t1@(Tip p1 bm1) t2@(Bin p2 m2 l2 r2) = case compare p1 p2 of
  LT -> Less
  EQ -> combine (relate t1 l2) Prefix
  GT -> Greater

combine :: Relation -> Relation -> Relation
combine r eq = case r of
      Less -> Less
      Prefix -> Greater
      Equals -> eq
      FlipPrefix -> Less
      Greater -> Greater

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
                      (Data.List.foldl' (\ o (_,_,q) -> S.insert q o) odo ts)
  in go IM.empty S.empty $ S.singleton initial  
  

det0 :: Sigma -> NFA -> DFA
det0 sigma = det sigma $ IS.singleton 0

type Transition = (State, Sigma, State)

nfa :: [Transition ] -> NFA 
nfa ts = IM.fromListWith ( IM.unionWith IS.union )
  $ Prelude.map (\(State p,Sigma s,State q) ->
           (s, IM.singleton p (IS.singleton q))) ts

dfa :: [(IntSet, Sigma, IntSet)] -> DFA
dfa ts = IM.fromListWith ( M.unionWith ( error "WAT") )
  $ Prelude.map (\( p, Sigma s, q) ->
           (s, M.singleton p q)) ts

union_dfa a b = IM.unionWith (M.unionWith (error "WAT")) a b

-- | for the language Sigma^* 1 Sigma^{n-2}  where Sigma={0,1}.
-- this NFA has  n  states. DFA has 2^(n-1) states
-- since it needs to remember the last n characters.
hard_nfa :: Int -> NFA
hard_nfa n = nfa
  $ [ (0, 0, 0), (0,1,0), (0, 1, 1) ]
  <> do k <- [1 .. State n - 2] ; c <- [0,1] ; return (k,c,k+1)

