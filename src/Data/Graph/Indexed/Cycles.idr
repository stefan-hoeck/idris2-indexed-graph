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

record State k where
  constructor MkState
  visited  : Integer
  prefixes : Vect k Integer
  rings    : List Integer

covering
getRings : (v, prev : Fin k) -> (g : IGraph k e n) -> (st : State k) -> State k

covering
getRings' : List (Fin k) -> (v, prev : Fin k) -> (g : IGraph k e n) -> State k -> State k
getRings' [] v prev g st@(MkState visited prefixes rings)         = st
getRings' (x :: xs) v prev g st@(MkState visited prefixes rings)  =
  if not . testBit st.visited $ finToNat x
    then let newst    := getRings x v g st
             returnst := getRings' xs v prev g newst
           in returnst
    else if not $ testBit (index prev st.prefixes) (finToNat x)
           then case getRings' xs v prev g st of
             returnst => returnst
           else let nring := xor (index v st.prefixes) (index x st.prefixes)
                    nrings := nring :: st.rings
                    newst := MkState visited prefixes nrings
                  in getRings' xs v prev g newst

getRings v prev g (MkState visited prefixes rings) =
  let updpref := replaceAt v visited prefixes
      updvis  := setBit visited $ finToNat v
      newst   := MkState updvis updpref rings
    in case keys $ neighbours g v of
      neigh => getRings' neigh v prev g newst

covering
search1 : {k : _} -> (g : IGraph k e n) -> List Integer
search1 {k = Z} g = []
search1 {k = S n} g = rings $ getRings 0 0 g (MkState 0 (replicate _ 0) Nil)


