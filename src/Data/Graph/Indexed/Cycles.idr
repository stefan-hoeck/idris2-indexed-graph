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

record PreRing (k : Nat) where
  constructor PR
  value : Integer

add : Fin k -> PreRing k -> PreRing k
add v prering = PR . setBit prering.value $ finToNat v

inPreRing : Fin k -> PreRing k -> Bool
inPreRing v prering = testBit prering.value $ finToNat v

merge : PreRing k -> PreRing k -> Ring k
merge pr1 pr2 = R (xor pr1.value pr2.value)

record State k where
  constructor MkState
  prefixes : Vect k (Maybe $ PreRing k)
  rings    : List (Ring k)

-- covering
-- getRings : (v : Fin k) -> (curr, prev : PreRing k) -> (g : IGraph k e n) -> (st : State k) -> State k
--
-- covering
-- getRings' : List (Fin k) -> (v : Fin k) -> (next, curr, prev : PreRing k) -> (g : IGraph k e n) -> State k -> State k
--
-- getRings v curr prev g (MkState visited prefixes rings) =
--   let updpref := replaceAt v curr prefixes
--       next    := add v curr
--       updvis  := visit v visited
--       newst   := MkState updvis updpref rings
--       neigh   := keys $ neighbours g v
--     in getRings' neigh v next curr prev g newst
--
-- getRings' []        v next curr prev g st = st
-- getRings' (x :: xs) v next curr prev g st =
--   if isVisited x st.visited
--     then
--       if inPreRing x prev
--          then
--            let nring  := merge next $ index x st.prefixes
--                newst  := {rings $= (nring ::)} st
--             in getRings' xs v next curr prev g newst
--          else getRings' xs v next curr prev g st
--     else
--       let newst := getRings x next curr g st
--        in getRings' xs v next curr prev g newst
--
-- export covering
-- search1 : {k : _} -> (g : IGraph k e n) -> List (Ring k)
-- search1 {k = Z}   g = []
-- search1 {k = S n} g =
--   rings $ getRings 0 (PR 0) (PR 0) g (MkState (V 0) (replicate _ (PR 0)) Nil)
--
-- covering
-- getAll : List (Fin k) -> (g : IGraph k e n) -> (st : State k) -> State k
-- getAll []        g st = st
-- getAll (x :: xs) g st =
--   if isVisited x st.visited
--      then getAll xs g st
--      else getAll xs g $ getRings x (PR 0) (PR 0) g st
--
-- export covering
-- searchAll : {k : _} -> (g : IGraph k e n) -> List (Ring k)
-- searchAll g =
--   let xs := allFinsFast k
--    in rings $ getAll xs g (MkState (V 0) (replicate _ (PR 0)) Nil)
