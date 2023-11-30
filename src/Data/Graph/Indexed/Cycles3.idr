module Data.Graph.Indexed.Cycles3

import Data.Array
import Data.Array.Mutable
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
  1 prefixes : MArray k (Maybe $ PreRing k)
  rings    : List (Ring k)

covering
getRings : (v : Fin k) -> (curr, prev : PreRing k) -> (g : IGraph k e n) -> (1 st : State k) -> State k

covering
getRings' : List (Fin k) -> (v : Fin k) -> (next, curr, prev : PreRing k) -> (g : IGraph k e n) -> (1 st: State k) -> State k

---getRings v curr prev g (MkState prefixes rings) =
---  let updpref := insert v curr prefixes
---      next    := add v curr
---      newst   := MkState updpref rings
---      neigh   := keys $ neighbours g v
---   in getRings' neigh v next curr prev g newst
---
---getRings' []        v next curr prev g st = st
---getRings' (x :: xs) v next curr prev g st =
---  case lookup x st.prefixes of
---    Nothing =>
---      let newst := getRings x next curr g st
---       in getRings' xs v next curr prev g newst
---    Just pr =>
---      if inPreRing x prev
---        then
---          let nring  := merge next pr
---              newst  := {rings $= (nring ::)} st
---           in getRings' xs v next curr prev g newst
---        else
---          getRings' xs v next curr prev g st
---
covering
getAll : List (Fin k) -> (g : IGraph k e n) -> (1 st : State k) -> Ur (List $ Ring k)
getAll []        g (MkState p r) = discarding p (MkBang r)
getAll (x :: xs) g (MkState prefixes rings) =
  let r # p2 := get x prefixes
   in ?foo
  ---case get x st.prefixes of
       ---xs => ?foo
    ---Nothing => getAll xs g $ getRings x (PR 0) (PR 0) g st
    ---Just _  => getAll xs g st

---export covering
---searchAllSM : {k : _} -> (g : IGraph k e n) -> List (Ring k)
---searchAllSM g =
---  let xs := allFinsFast k
---   in rings $ getAll xs g (MkState empty Nil)
