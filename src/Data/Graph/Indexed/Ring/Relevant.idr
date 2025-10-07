module Data.Graph.Indexed.Ring.Relevant

import Data.Bits
import Data.Graph.Indexed
import Data.Graph.Indexed.Query.Util
import Data.Graph.Indexed.Ring.Relevant.Internal.Candidates
import Data.Graph.Indexed.Subgraph
import Data.List
import Data.SortedMap

%default total

--------------------------------------------------------------------------------
--          Relevant Cycles and MCB
--------------------------------------------------------------------------------

public export
0 Edg : Nat -> Type
Edg k = Edge k ()

public export
0 ECycle : Nat -> Type
ECycle k = List (Edg k)

public export
record Cycle (k: Nat) where
  constructor C
  ncycle : NCycle k
  ecycle : ECycle k
  bitp   : Integer

public export
record CycleSets (k : Nat) where
  constructor CS
  cr  : List (Cycle k)
  mcb : List (Cycle k)

export
computeCyclomaticN : {k : _} -> IGraph k e n -> Nat
computeCyclomaticN g = (size g `minus` k) + 1

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

-- Convert cycle representation List (Fin k) corresponding to cyclic nodes to the cycle
-- representation List (Fin k, Fin k) corresponding to the cyclic edges.
convertC : List (Fin k) -> ECycle k
convertC [] = []
convertC [y] = []
convertC (x :: y :: xs) =
  case mkEdge x y () of
    Just e  => e :: convertC (y :: xs)
    Nothing => convertC (y::xs)

-- Computes the bit pattern corresponding to the edges included in the given cycle.
-- The cycle is represented as node pairs corresponding to the cyclic edges.
-- The sortedMap is a maping from each edge of the graph (node pairs) to the bit
-- pattern corresponding to this edge.
getBitsRing : EdgMap k -> Integer -> ECycle k -> Integer
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

-- Recursive function to compute the set of relevant rings and minimum cycle basis.
getCrAndMCB' : (v, size: Nat)
               -> (sm, eq : List Integer)
               -> (xs, cr, mcb : List (Cycle k))
               -> CycleSets k
getCrAndMCB' v size sm eq []        cr mcb = CS cr mcb
getCrAndMCB' v size sm eq (c :: cs) cr mcb =
  if c.ncycle.length > size -- now: sm == eq
    then if (cast (length mcb)) == v then CS cr mcb else case isInSet c.bitp [<] eq of
      (_,     False) => -- neither in Cr nor MCB, continue
        getCrAndMCB' v size eq eq cs cr mcb
      (neweq, True)  => -- in Cr and MCB
        getCrAndMCB' v c.ncycle.length eq neweq cs (c :: cr) (c :: mcb)
    else case isInSet c.bitp [<] sm of
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
getCrAndMCB : Nat -> List (Cycle k) -> CycleSets k
getCrAndMCB v xs = getCrAndMCB' v 0 [] [] xs [] []

convert : ISubgraph o k e n -> CycleSets o -> CycleSets k
convert g (CS m b) = CS (map convertC m) (map convertC b)
  where
    convertE : Edg o -> Maybe (Edg k)
    convertE (E x y ()) = mkEdge (origin g x) (origin g y) ()

    convertC : Cycle o -> Cycle k
    convertC (C nc ec bitp) =
      C ({path $= map (origin g)} nc) (mapMaybe convertE ec) bitp

fromCandidates : Candidates k e -> CycleSets k
fromCandidates Empty = CS [] []
fromCandidates (Isolate x xs) =
  let c := C xs (convertC xs.path) 0
   in CS [c] [c]
fromCandidates (System o g xss) =
  let ebits := getBitsEdges g
      ci'   := sortBy (compare `on` length) xss
      cs    := map (getCycle ebits) ci'
      v     := computeCyclomaticN g
   in convert g $ getCrAndMCB v cs

   where getCycle : EdgMap o -> NCycle o ->  Cycle o
         getCycle ebits nc =
           let ec := convertC nc.path
            in C nc ec $ getBitsRing ebits 0 ec

-- computes the relevant cycles and minimum cycle basis for a graph
export
computeCrAndMCB : {k : _} -> IGraph k e n -> CycleSets k
computeCrAndMCB g =
  let css := map fromCandidates (computeCI' g)
   in CS (css >>= cr) (css >>= mcb)
