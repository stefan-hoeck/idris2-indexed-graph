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

record State where
  constructor MkState
  visited  : Integer
  prefixes : Vect k Integer
  rings    : List Integer

covering
search1 : (g : IGraph k e n) -> State
search1 g = ?foo ---getRings 0 0 (MkState 0 (Vect k 0) Nil)

  where getRings : (v, prev : Fin k) -> (st : State) -> State
        getRings v prev st =
          if st.visited == oneBits then st
          else case updatePrefixes st of
            st2 => case updateVisited st2 of
              st3 => case keys $ neighbours g v of
                neigh => case map (checkNeigh st3) neigh of
                             xs => ?fofo



        where updatePrefixes : State -> State
              updatePrefixes x = ?koo ---{prefixes $= replaceAt v st.visited} x

              updateVisited : State -> State
              updateVisited x = ?fooo

              checkNeigh : State -> (n : Fin k) -> State
              checkNeigh st3 n = case testBit st3.visited $ finToNat n of
                x => if not x then getRings n v st3
                  else ?fjeiw
                    ---case testBit (index v (?st3prefixes)) $ finToNat prev of
                    ---  y => ?maifh

