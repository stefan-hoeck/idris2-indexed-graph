module Data.Graph.Indexed.Relevant

import public Data.Graph.Indexed.ShortestPath
import Data.SnocList
import Derive.Prelude

%default total
%language ElabReflection

public export
record NCycle (k : Nat) where
  constructor NC
  path   : List (Fin k)
  length : Nat
  combos : Nat

%runElab deriveIndexed "NCycle" [Show]

export
origin : ISubgraph o k e n -> NCycle o -> NCycle k
origin g = {path $= map (Subgraph.origin g)}

isolate : {o : _} -> ISubgraph (S o) k e n -> NCycle k
isolate g = NC (map (origin g) $ nodes g ++ [FZ]) (o + 2) 1

notLast : Fin k -> SnocList (Fin k) -> Bool
notLast x (_ :< y :< _) = x /= y
notLast x _             = True

parameters {o    : Nat}
           (g    : ISubgraph o k e Nat)
           (root : Fin o)
           (rdeg : Nat)

  revOnto : SnocList (Fin o) -> SnocList (Fin o) -> List (Fin o)
  revOnto sx [<] = sx <>> []
  revOnto sx (sy:<y) = revOnto (sx :< y) sy

  connector : SnocList (Fin o) -> SnocList (Fin o) -> Fin o -> Bool
  connector sx sy x = smaller g root rdeg x && notLast x sx && notLast x sy

  -- Takes a list of reverse paths starting all from the same node and
  -- sorted by length (this is by construction: the `shortestPaths` algorithm
  -- will produce shorter paths earlier than longer paths). It will pair every
  -- path with all successors of equal length (resulting in odd cycles) and
  -- one node longer (resulting in even cycles) and connect the pair if it
  -- builds a proper, disjoint cycle.
  cycleSystem : List (NCycle o)
  cycleSystem =
    let ps := shortestPaths g root rdeg
     in go [<] ps
    where
      %inline odd : (p1,p2 : Path o) -> NCycle o
      odd p1 p2 =
        NC
          (revOnto p1.path p2.path)
          (p1.length + p2.length + 1)
          (p1.combos * p2.combos)

      %inline even : (p1,p2 : Path o) -> Fin o -> Maybe (NCycle o)
      even p1 p2 x =
        if connector p1.path p2.path x
           then
             Just $ NC
               (revOnto (p1.path :< x) p2.path)
               (p1.length + p2.length + 2)
               (p1.combos * p2.combos)
            else Nothing

      addCs : SnocList (NCycle o) -> Path o -> List (Path o) -> SnocList (NCycle o)
      addCs sc p [] = sc
      addCs sc p@(P len1 p1 _ f1 l1 _) (q@(P len2 p2 _ f2 l2 _)::qs) =
        let True  := len1 == len2     | False => sc
            False := f1 == f2         | True  => addCs sc p qs
            False := adjacent g l1 l2 | True  => addCs (sc :< odd p q) p qs
            ns    := keys $ intersect (neighboursAsAL g l1) (neighboursAsAL g l2)
         in addCs (sc <>< mapMaybe (even p q) ns) p qs

      -- for the current path, we take from the remaining paths those
      -- that are at most one node longer and try to pair them to
      -- form a cycle.
      go : SnocList (NCycle o) -> List (Path o) -> List (NCycle o)
      go sxs []        = sxs <>> []
      go sxs (p :: ps) = go (addCs sxs p ps) ps

public export
data Candidates : (k : Nat) -> (e : Type) -> Type where
  Empty   : Candidates k e
  Isolate : Subgraph k e Nat -> NCycle k -> Candidates k e
  System  :
       (o : Nat)
    -> ISubgraph o k e Nat
    -> List (NCycle o)
    -> Candidates k e

findSP : (g : Subgraph k e Nat) -> Nat
findSP (G 0 g) = 0
findSP sg@(G (S k) g) =
  case filter ((2 <) . deg g) (nodes g) of
    [] => 0
    ns => length $ ns >>= \n => shortestPaths g n (deg g n)

findCandidates : Subgraph k e Nat -> Candidates k e
findCandidates (G 0 g) = Empty
findCandidates sg@(G (S k) g) =
  case filter ((2 <) . deg g) (nodes g) of
    [] => Isolate sg $ isolate g
    ns => System (S k) g (ns >>= \n => cycleSystem g n (deg g n))

toDegs : Subgraph k e n -> Subgraph k e Nat
toDegs (G o g) = G o $ mapAdj (\(A (x,_) ns) => A (x, length ns) ns) g

-- cuts a graph into strongly connected components and computes
-- the potential relevant cycles for each component in isolation.
export
computeCI' : {k : _} -> IGraph k e n -> List (Candidates k e)
computeCI' g = map (findCandidates . toDegs) $ biconnectedComponents g

export
computeSPs : {k : _} -> IGraph k e n -> Nat
computeSPs g = sum . map (findSP . toDegs) $ biconnectedComponents g
