module Data.Graph.Indexed.Ring.Relevant.Types

import public Data.Graph.Indexed
import public Data.Graph.Indexed.Subgraph
import public Data.Graph.Indexed.Query.Util
import Data.Nat
import Data.SortedSet as SS
import Derive.Prelude

%default total
%language ElabReflection

||| A shortest path of length `length` from a starting node to node `last`.
||| `combos` is the number of shortest paths of the same length leading
||| from `first` to `last`.
||| Node `first` is the first node after the root node, and is used to
||| check if two paths are disjoint.
public export
record Path (k : Nat) where
  constructor P
  ||| Number of nodes in the path (including the root node).
  length : Nat

  ||| The accumulated path viewed from the right
  path   : SnocList (Fin k)

  ||| True, if all nodes in the path are smaller than the root
  |||
  ||| This flag is used for efficiency, as it allows us to avoid
  ||| computing the same cycle more than once.
  keep   : Bool

  ||| The first non-root node in the path
  first  : Fin k

  ||| The last node in the path
  last   : Fin k

  ||| Number of paths of the same length from `root` to
  ||| `last`. This is later used to compute the size of
  ||| a family of relevant cycles
  combos : Nat

%runElab deriveIndexed "Path" [Show,Eq]

||| A family of cycles in a graph of order `k`.
public export
record NCycle (k : Nat) where
  constructor NC
  ||| A single representative of the cycle family.
  path   : List (Fin k)

  ||| Length of the cycle.
  length : Nat

  ||| Number of members in the family.
  combos : Nat

%runElab deriveIndexed "NCycle" [Show,Eq]

public export
0 Edg : Nat -> Type
Edg k = Edge k ()

public export
0 ECycle : Nat -> Type
ECycle k = List (Edg k)

public export
record Cycle (k: Nat) where
  constructor C
  ncycle  : NCycle k
  ecycle  : ECycle k
  nodeset : SortedSet (Fin k)
  edgeset : SortedSet (Edg k)

%runElab deriveIndexed "Cycle" [Show,Eq]

export
ecycle : List (Fin k) -> ECycle k
ecycle (x::y::xs) =
  case mkEdge x y () of
    Just e  => e :: ecycle (y::xs)
    Nothing => ecycle (y::xs)
ecycle _ = []

export
Cast (NCycle k) (Cycle k) where
  cast n =
   let es := ecycle n.path
    in C n es (SS.fromList n.path) (SS.fromList es)

||| Returns the list of nodes two cycles have in common.
export
sharedNodes : (cx,cy : Cycle k) -> List (Fin k)
sharedNodes cx cy =
  case cx.ncycle.length <= cy.ncycle.length of
    True  => filter (`contains` cy.nodeset) (drop 1 cx.ncycle.path)
    False => filter (`contains` cx.nodeset) (drop 1 cy.ncycle.path)

||| Returns the number of nodes shared by two cycles.
export
numSharedNodes : (cx,cy : Cycle k) -> Nat
numSharedNodes cx cy =
  case cx.ncycle.length <= cy.ncycle.length of
    True  => count (`contains` cy.nodeset) (drop 1 cx.ncycle.path)
    False => count (`contains` cx.nodeset) (drop 1 cy.ncycle.path)

||| Returns the list of edges two cycles have in common.
export
sharedEdges : (cx,cy : Cycle k) -> List (Edg k)
sharedEdges cx cy =
  case cx.ncycle.length <= cy.ncycle.length of
    True  => filter (`contains` cy.edgeset) cx.ecycle
    False => filter (`contains` cx.edgeset) cy.ecycle

||| Returns the number of nodes shared by two cycles.
export
numSharedEdges : (cx,cy : Cycle k) -> Nat
numSharedEdges cx cy =
  case cx.ncycle.length <= cy.ncycle.length of
    True  => count (`contains` cy.edgeset) cx.ecycle
    False => count (`contains` cx.edgeset) cy.ecycle

||| True, if the two cycles share a single edge and no additional node.
export
isFusedTo : (cx,cy : Cycle k) -> Bool
isFusedTo cx cy = numSharedNodes cx cy == 2 && numSharedEdges cx cy == 1

||| True, if the two cycles share a single node.
export
isSpiro : (cx,cy : Cycle k) -> Bool
isSpiro cx cy = numSharedNodes cx cy == 1

public export
record CycleSets (k : Nat) where
  constructor CS
  cr  : List (Cycle k)
  mcb : List (Cycle k)

%runElab deriveIndexed "CycleSets" [Show,Eq]

public export
data Candidates : (k : Nat) -> (e : Type) -> Type where
  Empty   : Candidates k e
  Isolate : Subgraph k e Nat -> NCycle k -> Candidates k e
  System  :
       (o : Nat)
    -> ISubgraph o k e Nat
    -> List (NCycle o)
    -> Candidates k e
