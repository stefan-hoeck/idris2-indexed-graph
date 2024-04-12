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
import Data.Graph.Indexed.Ring

%default total

export
popCountInteger : Integer -> Nat
popCountInteger = go 0
  where
    go : Nat -> Integer -> Nat
    go n x =
      case x <= 0 of
        True  => n
        False =>
          let n2 := n + cast (popCount {a = Bits32} (cast x))
           in go n2 (assert_smaller x (shiftR x 32))

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

addFused : Bool -> Ring k -> List (Bool, Ring k) -> List (Bool, Ring k)
addFused f y []     = [(f, y)]
addFused f y (x :: xs) =
  if popCountInteger (value y .&. value (snd x)) > 1
    then addFused True (R $ value y .|. (value (snd x))) xs
    else x :: addFused False y xs

addRing : Ring k -> (1 st : State k) -> State k
addRing x (MkState prefixes rings) =
  let nrings := addFused False x rings
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
      neigh   := neighbours g v
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

getBitsEdges : {k : _} -> (g : IGraph k e n) -> SortedMap (Fin k, Fin k) Integer
getBitsEdges g =
  let es := map (\e => (e.node1, e.node2)) $ edges g
   in setBits es 0 empty

  where setBits : List (Fin k, Fin k)
                  -> Integer
                  -> SortedMap (Fin k, Fin k) Integer
                  -> SortedMap (Fin k, Fin k) Integer
        setBits []        bitp sm = sm
        setBits (y :: xs) bitp sm =
          let newbitp := shiftL bitp 1
              smnew   := insert y newbitp sm
           in setBits xs newbitp smnew

-- Resuslt LT -> same significant bit, else distinct significant bit
testSigBit : Integer -> Integer -> Ordering
testSigBit i j = compare (xor i j) (i .&. j)

cycleLength : Integer -> Nat

isRelevant : (ring : Integer)
          -> (processedRs : SnocList (Integer))
          -> (unprocessedRs : List (Integer))
          -> (List Integer, Bool)

isInMCB : (ring : Integer)
          -> (processedRs : SnocList (Integer))
          -> (unprocessedRs : List (Integer))
          -> (List Integer, Bool)

isInMCB ring [<] [] = ([ring], True)

isInMCB ring (sx :< x) [] =
  (toList $ sx :< x :< ring, True) -- add Ring at bottom

isInMCB ring [<] (x :: xs) =
  case testSigBit ring x of
    -- same significant bit
    LT => let remainder := xor ring x
           in if remainder == 0
                then (x :: xs, False) -- not relevant since linearly dependent from set
                else isInMCB remainder [<x] xs --continue
    -- distinct significant bit
    _  => case compare ring x of
      GT => (ring :: x :: xs, True) -- ring is signifint because ring > x (Right?)
      _  => isInMCB ring [<x] xs --continue

isInMCB ring sy (x :: xs) =
  case testSigBit ring x of
    -- same significant bit
    LT => let remainder := xor ring x
           in if remainder == 0
                then (sy <>> x :: xs, False) -- not relevant since linearly dependent from set
                else isInMCB remainder (sy :< x) xs -- continue
    -- distinct significant bit
    _  => case compare ring x of
      GT => (sy :< ring <>> x :: xs, True) -- ring is signifint because ring > x (Right?)
      _  => isInMCB ring (sy :< x) xs -- continue

getCrAndMCB' : (size : Nat)
               -> (unprocessedRs : List Integer)
               -> (smaller : List Integer)
               -> (relC : List Integer)
               -> (mcb : List Integer)
               -> (List Integer, List Integer)
getCrAndMCB' size [] smaller relC mcb = (relC, mcb)
getCrAndMCB' size (x :: xs) smaller relC mcb =
  if (cycleLength x) > size
    -- smaller is now == mcb
    then case isRelevant x [<] mcb of
      (y, False) => getCrAndMCB' size xs mcb relC y -- neither in Cr nor MCB, continuefoo_3
      (y, True)  =>
        let newRelC := x :: relC
         in getCrAndMCB' (cycleLength x) xs mcb newRelC y

    else case isRelevant x [<] smaller of
      (y, False) => getCrAndMCB' size xs smaller relC mcb -- neither in Cr nor MCB, continue
      (y, True)  =>
        let newRelC := x :: relC
         in case isInMCB x [<] mcb of
           (z, False) => getCrAndMCB' (cycleLength x) xs smaller newRelC mcb
           (z, True)  => getCrAndMCB' (cycleLength x) xs smaller newRelC z

--- Assuming the List of rings is ordered by ringSize in increasing order
getCrAndMCB : List Integer -> (List Integer, List Integer)
getCrAndMCB xs = getCrAndMCB' 0 xs [] [] []



