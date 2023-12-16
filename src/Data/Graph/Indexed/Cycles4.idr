module Data.Graph.Indexed.Cycles4

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
  rings    : List (Bool, Ring k)

--- incomplete version of finding fused rings that doesnt check
--- if new fused ring is fused to other rings

addFused : Ring k -> List (Bool, Ring k) -> List (Bool, Ring k)
addFused y []        = [(False, y)]
addFused y (x :: xs) =
  case (value y .&. (value (snd x))) > 1 of
    False => x :: addFused y xs
    True  =>
      let fusedRing := R $ value y .|. (value (snd x))
       in (True, fusedRing) :: xs

addRing : Ring k -> (1 st : State k) -> State k
addRing x (MkState prefixes rings) =
  case addFused x rings of
    nrings => MkState prefixes nrings

---------------------------------------------------------------

--- cumbersome version that checks if new fused rings are fused
--- with other rings

findFused : Ring k -> List (Bool, Ring k) -> Maybe (Ring k)
findFused y []        = Nothing
findFused y (x :: xs) =
  case (value y .&. (value (snd x))) > 1 of
    False => findFused y xs
    True  => Just (snd x)

removeFused : Ring k -> List(Bool, Ring k) -> List (Bool, Ring k)
removeFused y []        = []
removeFused y (z :: xs) =
  if value (snd z) == value y then xs else z :: removeFused y xs

covering
updateRings' : Ring k -> List (Bool, Ring k) -> List (Bool, Ring k)
updateRings' fusedRing ys =
  case findFused fusedRing ys of
    Nothing => (True, fusedRing) :: ys
    Just x  =>
      let yys := removeFused x ys
          fusedRing2 := R $ value fusedRing .|. value x
       in updateRings' fusedRing2 yys

covering
updateRings : Ring k -> List (Bool, Ring k) -> List (Bool, Ring k)
updateRings x xs =
  case findFused x xs of
    Nothing => (False, x) :: xs
    Just y  =>
      let ys        := removeFused y xs
          fusedRing := R $ value y .|. value x
       in updateRings' fusedRing ys

covering
addRing' : Ring k -> (1 st : State k) -> State k
addRing' x (MkState prefixes rings) =
  let nrings := updateRings x rings
   in MkState prefixes nrings


covering
findRings :
     (v : Fin k)
  -> (curr, prev : PreRing k)
  -> (g : IGraph k e n)
  -> (1 st : State k)
  -> State k

covering
findRings' :
     List (Fin k)
  -> (v : Fin k)
  -> (next, curr, prev : PreRing k)
  -> (g : IGraph k e n)
  -> (1 st: State k)
  -> State k

findRings v curr prev g (MkState prefixes rings) =
  let updpref := set v (Just curr) prefixes
      next    := add v curr
      newst   := MkState updpref rings
      neigh   := keys $ neighbours g v
   in findRings' neigh v next curr prev g newst

findRings' []        v next curr prev g st = st
findRings' (x :: xs) v next curr prev g (MkState pref rings) =
  case get x pref of
    Nothing # pref2 =>
      let newst := findRings x next curr g $ MkState pref2 rings
       in findRings' xs v next curr prev g newst
    Just pr # pref2 =>
      if inPreRing x prev
        then
          let nring  := merge next pr
              newst  := addRing nring $ MkState pref2 rings
           in findRings' xs v next curr prev g newst
        else
          findRings' xs v next curr prev g $ MkState pref2 rings

covering
findAll : List (Fin k) -> IGraph k e n -> (1 st : State k) -> Ur (List (Bool, Ring k))
findAll []        g (MkState p r) = discarding p (MkBang r)
findAll (x :: xs) g (MkState pref rings) =
  case get x pref of
    Nothing # pref2 =>
      findAll xs g $ findRings x (PR 0) (PR 0) g (MkState pref2 rings)
    Just _  # pref2 =>
      findAll xs g (MkState pref2 rings)

export covering
searchAllMA : {k : _} -> (g : IGraph k e n) -> List (Bool, Ring k)
searchAllMA g =
  unrestricted $ alloc k Nothing (\x => findAll (allFinsFast k) g (MkState x []))
