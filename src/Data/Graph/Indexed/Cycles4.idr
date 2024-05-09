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

--------------------------------------------------------------------------------
--          Basic Ring Search
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
--          Relevant Cycles and MCB
--------------------------------------------------------------------------------

public export
record Cycle (k: Nat) where
  constructor C
  size   : Nat
  ncycle : NCycle k
  ecycle : ECycle k
  bitp   : Integer

public export
record CycleSets (k : Nat) where
  constructor CS
  cr : List (Cycle k)
  mcb : List (Cycle k)

computeCyclomaticN : {k : _} -> IGraph k e n -> Nat
computeCyclomaticN g = size g `minus` k + 1

-- Compute a sortedMap corresponding to a mapping from all edges of a graph to their
-- respective bit pattern.
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

-- Convert cycle representation List (Fin k) corresponding to cyclic nodes to the cycle
-- representation List (Fin k, Fin k) corresponding to the cyclic edges.
convertC : NCycle k -> ECycle k
convertC [] = []
convertC [y] = []
convertC (x :: y :: xs) = (x,y) :: convertC (y :: xs)

-- Computes the bit pattern corresponding to the edges included in the given cycle.
-- The cycle is represented as node pairs corresponding to the cyclic edges.
-- The sortedMap is a maping from each edge of the graph (node pairs) to the bit
-- pattern corresponding to this edge.
getBitsRing : SortedMap (Fin k, Fin k) Integer -> Integer -> ECycle k -> Integer
getBitsRing sm i [] = i
getBitsRing sm i (x :: xs) = case lookup x sm of
  Nothing => getBitsRing sm i xs -- impossible case
  Just z  => getBitsRing sm (i .|. z) xs

-- Tests if two integers have the same significant bit.
-- LT -> same significant bit, else distinct significant bit.
testSigBit : Integer -> Integer -> Ordering
testSigBit i j = compare (xor i j) (i .&. j)

-- Tests if a ring, represented as a bit pattern of edges, is linearly independet
-- from the given set of rings. Returns the modified set if the ring is linearly
-- independet and a boolan to indicate wheter the ring is linearly independent.
isInSet : (ring : Integer)
          -> (processedRs : SnocList (Integer))
          -> (unprocessedRs : List (Integer))
          -> (List Integer, Bool)
isInSet ring sy  []        = (toList $ sy :< ring, True)
isInSet ring sy  (x :: xs) =
  case testSigBit ring x of
    LT => -- same significant bit
      let remainder := xor ring x
           in if remainder == 0
                then (sy <>> x :: xs, False)
                else isInSet remainder (sy :< x) xs
    _  => -- distinct significant bit
      case compare ring x of
        GT => (sy :< ring <>> x :: xs, True)
        _  => isInSet ring (sy :< x) xs

-- Recursive function to compute the set of relevant rings and minimum cycle basis.
getCrAndMCB' : (v, size: Nat)
               -> (sm, eq : List Integer)
               -> (xs, cr, mcb : List (Cycle k))
               -> CycleSets k
getCrAndMCB' v size sm eq []        cr mcb = CS cr mcb
getCrAndMCB' v size sm eq (c :: cs) cr mcb =
  if c.size > size -- now: sm == eq
    then if (cast (length mcb)) == v then CS cr mcb else case isInSet c.bitp [<] eq of
      (_,     False) => -- neither in Cr nor MCB, continue
        getCrAndMCB' v size eq eq cs cr mcb
      (neweq, True)  => -- in Cr and MCB
        getCrAndMCB' v c.size eq neweq cs (c :: cr) (c :: mcb)
    else case isInSet c.bitp [<] sm of
      (_, False) => -- neither in Cr nor MCB, continue
        getCrAndMCB' v size sm eq cs cr mcb
      (_, True)  =>
        case isInSet c.bitp [<] eq of
          (_,     False) => -- in Cr but not MCB
            getCrAndMCB' v c.size sm eq cs (c :: cr) mcb
          (neweq, True)  => -- in Cr and MCB
            getCrAndMCB' v c.size sm neweq cs (c :: cr) (c :: mcb)

-- Initalizes the recursive function getCrAndMCB' to get the relevant cycles and MCB
-- from the cyclomatic number and the set of potentially relevant cycles (CI', given
-- as a list of pairs with cycle size and the cycle represented as a bit pattern of edges).
-- The potentially relevant cycles are ordered by size.
getCrAndMCB : Nat -> List (Cycle k) -> CycleSets k
getCrAndMCB v xs = getCrAndMCB' v 0 [] [] xs [] []

-- computes the relevant cycles and minimum cycle basis for a graph
public export
computeCrAndMCB : {k : _} -> IGraph k e n -> CycleSets k
computeCrAndMCB g =
  let ebits := getBitsEdges g
      ci'   := sortBy (compare `on` length) $ computeCI' g
      cs    := map (getCycle ebits) ci'
      v     := computeCyclomaticN g
   in getCrAndMCB v cs

   where getCycle : SortedMap (Fin k, Fin k) Integer -> NCycle k ->  Cycle k
         getCycle ebits nc =
           let ec := convertC nc
               size := length nc
               bitp := getBitsRing ebits 0 ec
            in C size nc ec bitp

