module Data.Graph.Indexed.Ring.Relevant

import Data.Bits
import Data.Graph.Indexed.Ring.Relevant.Candidates
import Data.List
import Data.SortedMap

import public Data.Graph.Indexed.Ring.Relevant.Types

%default total

--------------------------------------------------------------------------------
--          Relevant Cycles and MCB
--------------------------------------------------------------------------------

export
computeCyclomaticN : {k : _} -> IGraph k e n -> Nat
computeCyclomaticN g = S (size g) `minus` k

0 EdgMap : Nat -> Type
EdgMap k = SortedMap (Edg k) Integer

-- Compute a sortedMap corresponding to a mapping from all edges of a graph to their
-- respective bit pattern.
getBitsEdges : {k : _} -> (g : IGraph k e n) -> EdgMap k
getBitsEdges g = setBits (map ignore $ edges g) 1 empty
  where
    setBits : List (Edg k) -> Integer -> EdgMap k -> EdgMap k
    setBits []        bitp sm = sm
    setBits (y :: xs) bitp sm = setBits xs (shiftL bitp 1) (insert y bitp sm)

-- Computes the bit pattern corresponding to the edges included in the given cycle.
-- The cycle is represented as node pairs corresponding to the cyclic edges.
-- The sortedMap is a maping from each edge of the graph (node pairs) to the bit
-- pattern corresponding to this edge.
getBitsRing : EdgMap k -> Integer -> List (Fin k) -> Integer
getBitsRing sm i (x::xs@(y::_)) = case mkEdge x y () >>= lookup' sm of
  Nothing => getBitsRing sm i xs -- impossible case
  Just z  => getBitsRing sm (i .|. z) xs
getBitsRing sm i _ = i

-- Tests if two integers have the same significant bit.
-- LT -> same significant bit, else distinct significant bit.
testSigBit : Integer -> Integer -> Ordering
testSigBit i j = compare (xor i j) (i .&. j)

-- Tests if a ring, represented as a bit pattern of edges, is linearly independet
-- from the given set of rings. Returns the modified set if the ring is linearly
-- independet and a boolan to indicate wheter the ring is linearly independent.
isInSet :
     (ring : Integer)
  -> (processedRs : SnocList (Integer))
  -> (unprocessedRs : List (Integer))
  -> (List Integer, Bool)
isInSet ring sy  []        = (sy <>> [ring], True)
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

record BCycle (k : Nat) where
  constructor BC
  ncycle : NCycle k
  bitp   : Integer

0 BCycles : Nat -> Type
BCycles = List . BCycle

-- Recursive function to compute the set of relevant rings and minimum cycle basis.
getCrAndMCB' :
     (v, size: Nat)
  -> (sm, eq : List Integer)
  -> (xs, cr, mcb : BCycles k)
  -> (BCycles k, BCycles k)
getCrAndMCB' v size sm eq []        cr mcb = (cr,mcb)
getCrAndMCB' v size sm eq (c :: cs) cr mcb =
  case c.ncycle.length > size of
    True => case length mcb == v of
      True  => (cr,mcb)
      False => case isInSet c.bitp [<] eq of
        (_,     False) => -- neither in Cr nor MCB, continue
          getCrAndMCB' v size eq eq cs cr mcb
        (neweq, True)  => -- in Cr and MCB
          getCrAndMCB' v c.ncycle.length eq neweq cs (c :: cr) (c :: mcb)
    False => case isInSet c.bitp [<] sm of
      (_, False) => -- neither in Cr nor MCB, continue
        getCrAndMCB' v size sm eq cs cr mcb
      (_, True)  =>
        case isInSet c.bitp [<] eq of
          (_,     False) => -- in Cr but not MCB
            getCrAndMCB' v c.ncycle.length sm eq cs (c :: cr) mcb
          (neweq, True)  => -- in Cr and MCB
            getCrAndMCB' v c.ncycle.length sm neweq cs (c :: cr) (c :: mcb)

-- Initalizes the recursive function getCrAndMCB' to get the relevant cycles and MCB
-- from the cyclomatic number and the set of potentially relevant cycles (CI', given
-- as a list of pairs with cycle size and the cycle represented as a bit pattern of edges).
-- The potentially relevant cycles are ordered by size.
getCrAndMCB : Nat -> BCycles k -> (BCycles k, BCycles k)
getCrAndMCB v xs = getCrAndMCB' v 0 [] [] xs [] []

convert : ISubgraph o k e n -> (BCycles o, BCycles o) -> CycleSets k
convert g (m,b) = CS (map conv m) (map conv b)
  where
    conv : BCycle o -> Cycle k
    conv (BC c _) = cast {from = NCycle k} $ {path $= map (origin g)} c

fromCandidates : Candidates k e -> CycleSets k
fromCandidates Empty = CS [] []
fromCandidates (Isolate x nc) = let c := cast {to = Cycle k} nc in CS [c] [c]
fromCandidates (System o g xss) =
  let ebits := getBitsEdges g
      ci'   := sortBy (compare `on` length) xss
      cs    := map (getCycle ebits) ci'
      v     := computeCyclomaticN g
   in convert g $ getCrAndMCB v cs

   where getCycle : EdgMap o -> NCycle o ->  BCycle o
         getCycle ebits nc = BC nc $ getBitsRing ebits 0 nc.path

||| computes the relevant cycles and minimum cycle basis
||| for a biconnected component in a graph.
export %inline
componentCycles : Subgraph k e n -> CycleSets k
componentCycles = fromCandidates . componentCandidates

||| computes the relevant cycles and minimum cycle basis for a graph
export
computeCrAndMCB : {k : _} -> IGraph k e n -> CycleSets k
computeCrAndMCB g =
  let css := map fromCandidates (candidates g)
   in CS (css >>= cr) (css >>= mcb)
