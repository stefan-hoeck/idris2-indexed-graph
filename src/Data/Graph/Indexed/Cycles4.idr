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
import Data.Graph.Indexed.Relevant

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

convertC : Cycle k -> ECycle k
convertC [] = []
convertC [y] = []
convertC (x :: y :: xs) = (x,y) :: convertC (y :: xs)

getBitsRing : ECycle k -> SortedMap (Fin k, Fin k) Integer -> Integer -> Maybe Integer
getBitsRing [] x i = Just i
getBitsRing (y :: xs) x i = case lookup y x of
  Nothing => Nothing
  Just z  => getBitsRing xs x (i .|. z)

-- Resuslt LT -> same significant bit, else distinct significant bit
testSigBit : Integer -> Integer -> Ordering
testSigBit i j = compare (xor i j) (i .&. j)

-- get the length of a cycle in edges by counting the set bits
cycleLength : Integer -> Nat

-- test if ring is linearly independet from the given set
-- returns the modified set if the ring is linearly independet
-- and a boolan to indicate wheter the ring is linearly independent
isInSet : (ring : Integer)
          -> (processedRs : SnocList (Integer))
          -> (unprocessedRs : List (Integer))
          -> (List Integer, Bool)
isInSet ring sy  []        = (toList $ sy :< ring, True)
isInSet ring sy  (x :: xs) =
  case testSigBit ring x of
    -- same significant bit
    LT => let remainder := xor ring x
           in if remainder == 0
                then (sy <>> x :: xs, False)
                else isInSet remainder (sy :< x) xs
    -- distinct significant bit
    _  => case compare ring x of
      GT => (sy :< ring <>> x :: xs, True)
      _  => isInSet ring (sy :< x) xs

getCrAndMCB' : (v : Nat)
               -> (size : Nat)
               -> (xs : List Integer)
               -> (sm : List Integer)
               -> (eq : List Integer)
               -> (relC : List Integer)
               -> (mcb : List Integer)
               -> (List Integer, List Integer)
getCrAndMCB' v size [] sm eq relC mcb = (relC, mcb)
getCrAndMCB' v size (x :: xs) sm eq relC mcb =
  if (cycleLength x) > size
    -- now: sm == eq
    then if length mcb == v then (relC, mcb) else case isInSet x [<] eq of
      (_,     False) => getCrAndMCB' v size xs eq eq relC mcb -- neither in Cr nor MCB, continue
      (neweq, True)  => getCrAndMCB' v (cycleLength x) xs eq neweq (x :: relC) (x :: mcb) -- in Cr and MCB

    else case isInSet x [<] sm of
      (_, False) => getCrAndMCB' v size xs sm eq relC mcb -- neither in Cr nor MCB, continue
      (_, True)  => -- is relevant, add to Cr (relC)
         case isInSet x [<] eq of
           (_,     False) => getCrAndMCB' v (cycleLength x) xs sm eq (x :: relC) mcb -- in Cr but not MCB
           (neweq, True)  => getCrAndMCB' v (cycleLength x) xs sm neweq (x :: relC) (x :: mcb) -- in Cr and MCB

--- Arguments: cyclomatic number (Nat) and rings (List Integer)
--- Assuming the List of rings is ordered by ringSize in increasing order
getCrAndMCB : Nat -> List Integer -> (List Integer, List Integer)
getCrAndMCB v xs = getCrAndMCB' v 0 xs [] [] [] []

computeCyclomaticN : {k : _} -> IGraph k e n -> Integer
computeCyclomaticN g = cast (size g) - cast k + 1

computeCrAndMCB : {k : _} -> IGraph k e n -> Maybe (List Integer, List Integer)
computeCrAndMCB g =
  let ebits := getBitsEdges g
      ci' := map convertC $ computeCI' g
      lengths := map length ci'
   in case traverse (\x => getBitsRing x ebits 0) ci' of
     Nothing => Nothing
     Just xs =>
       let cs := zip lengths xs
           v := computeCyclomaticN g
        in ?foo --Just $ getCrAndMCB v $ map snd cs

