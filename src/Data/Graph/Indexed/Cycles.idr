module Data.Graph.Indexed.Cycles

import Data.Array.Indexed
import Data.AssocList.Indexed
import Data.Graph.Indexed.Types
import Data.Graph.Indexed.Util
import Data.SortedMap
import Data.SortedSet
import Data.List
import Data.String
import Data.Vect
import Data.Bits

%default total


--------------------------------------------------------------------------------
--          Ring detection
--------------------------------------------------------------------------------

covering
paths : (g : IGraph k e n) -> (n1 : Fin k) -> (n2 : Fin k) -> List (List (Fin k))
paths g n1 n2 = getPaths [] n1

  where getPaths : (List (Fin k)) -> (n : Fin k) -> List (List (Fin k))
        getPaths xs n =
          if n == n2 then [[n2]] else
          case map fst $ pairs $ neighbours g n of
            neigh =>
              let unvis := filter (not . wasVisited) neigh
                  newVis := [n] ++ xs
                  subpaths := concatMap (getPaths newVis) unvis
                in map (n ::) subpaths

        where wasVisited : Fin k -> Bool
              wasVisited x = elem x xs

covering
rings : (g : IGraph k e n) -> (n : Fin k) -> List (List (Fin k))
rings g n = case map (\y => paths g y n) (map fst $ pairs $ neighbours g n) of
              xss => case concatMap (filter (\xs => length xs > 2)) xss of
                fs => map (n ::) fs

record Visited (k : Nat) where
  constructor V
  value : Integer

isVisited : Fin k -> Visited k -> Bool
isVisited v vis = testBit vis.value $ finToNat v

visit : Fin k -> Visited k -> Visited k
visit v vis = V . setBit vis.value $ finToNat v

record Path (k : Nat) where
  constructor P
  value : Integer

add : Fin k -> Path k -> Path k
add v path = P . setBit path.value $ finToNat v

inPath : Fin k -> Path k -> Bool
inPath v path = testBit path.value $ finToNat v

implementation Semigroup (Path k) where
  (<+>) p1 p2 = P (xor p1.value p2.value)

implementation Monoid (Path k) where
  neutral = P 0

record State k where
  constructor MkState
  visited  : Visited k
  prefixes : Vect k (Path k)
  rings    : List Integer

covering
getRings : (v : Fin k) -> (curr, prev : Path k) -> (g : IGraph k e n) -> (st : State k) -> State k

covering
getRings' : List (Fin k) -> (v : Fin k) -> (next, curr, prev : Path k) -> (g : IGraph k e n) -> State k -> State k

getRings v curr prev g (MkState visited prefixes rings) =
  let updpref := replaceAt v curr prefixes
      next    := add v curr
      updvis  := visit v visited
      newst   := MkState updvis updpref rings
    in case keys $ neighbours g v of
      neigh => getRings' neigh v next curr prev g newst

getRings' []        v next curr prev g st = st
getRings' (x :: xs) v next curr prev g st =
  if isVisited x st.visited
    then if inPath x prev
           then let nring  := value $ index x st.prefixes <+> next
                    newst  := {rings $= (nring ::)} st
                  in getRings' xs v next curr prev g newst
           else getRings' xs v next curr prev g st
    else let newst := getRings x next curr g st
          in getRings' xs v next curr prev g newst

export covering
search1 : {k : _} -> (g : IGraph k e n) -> List Integer
search1 {k = Z}   g = []
search1 {k = S n} g = rings $ getRings 0 (P 0) (P 0) g (MkState (V 0) (replicate _ (P 0)) Nil)

