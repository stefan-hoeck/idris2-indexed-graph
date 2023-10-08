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


