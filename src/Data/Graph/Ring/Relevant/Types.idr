module Data.Graph.Ring.Relevant.Types

import public Data.Graph
import public Data.Graph.Subgraph
import public Data.Graph.Query.Util
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
record Path (g : Graph e n) where
  constructor P
  ||| Number of nodes in the path (including the root node).
  length : Nat

  ||| The accumulated path viewed from the right
  path   : Sedon g

  ||| True, if all nodes in the path are smaller than the root
  |||
  ||| This flag is used for efficiency, as it allows us to avoid
  ||| computing the same cycle more than once.
  keep   : Bool

  ||| The first non-root node in the path
  first  : Node g

  ||| The last node in the path
  last   : Node g

  ||| Number of paths of the same length from `root` to
  ||| `last`. This is later used to compute the size of
  ||| a family of relevant cycles
  combos : Nat

%runElab deriveIndexed "Path" [Show,Eq]

||| A family of cycles in a graph of order `k`.
public export
record NCycle (g : Graph e n) where
  constructor NC
  ||| A single representative of the cycle family.
  path   : Nodes g

  ||| Length of the cycle.
  size   : Nat

  ||| Number of members in the family.
  combos : Nat

  ||| A cycle consists of at least three nodes
  {auto 0 prf : LTE 3 size}

%runElab deriveIndexed "NCycle" [Show,Eq]

public export
0 ECycle : Graph e n -> Type
ECycle g = List (Edg g)

public export
record Cycle (g : Graph e n) where
  constructor C
  ncycle  : NCycle g
  ecycle  : ECycle g
  nodeset : SortedSet (Node g)
  edgeset : SortedSet (Edg g)

export
(.nodes) : Cycle g -> List (Node g)
(.nodes) c = drop 1 c.ncycle.path

%runElab deriveIndexed "Cycle" [Show,Eq]

export
ecycle : Nodes g -> ECycle g
ecycle (x::y::xs) =
  case mkEdg x y of
    Just e  => e :: ecycle (y::xs)
    Nothing => ecycle (y::xs)
ecycle _ = []

export
Cast (NCycle g) (Cycle g) where
  cast n =
   let es := ecycle n.path
    in C n es (SS.fromList n.path) (SS.fromList es)

||| Returns the list of nodes two cycles have in common.
export
sharedNodes : (cx,cy : Cycle g) -> List (Node g)
sharedNodes cx cy =
  case cx.ncycle.size <= cy.ncycle.size of
    True  => filter (`contains` cy.nodeset) cx.nodes
    False => filter (`contains` cx.nodeset) cy.nodes

||| Returns the number of nodes shared by two cycles.
export
numSharedNodes : (cx,cy : Cycle g) -> Nat
numSharedNodes cx cy =
  case cx.ncycle.size <= cy.ncycle.size of
    True  => count (`contains` cy.nodeset) cx.nodes
    False => count (`contains` cx.nodeset) cy.nodes

||| Returns the list of edges two cycles have in common.
export
sharedEdges : (cx,cy : Cycle g) -> List (Edg g)
sharedEdges cx cy =
  case cx.ncycle.size <= cy.ncycle.size of
    True  => filter (`contains` cy.edgeset) cx.ecycle
    False => filter (`contains` cx.edgeset) cy.ecycle

||| Returns the number of nodes shared by two cycles.
export
numSharedEdges : (cx,cy : Cycle g) -> Nat
numSharedEdges cx cy =
  case cx.ncycle.size <= cy.ncycle.size of
    True  => count (`contains` cy.edgeset) cx.ecycle
    False => count (`contains` cx.edgeset) cy.ecycle

||| True, if the two cycles share a single edge and no additional node.
export
isFusedTo : (cx,cy : Cycle g) -> Bool
isFusedTo cx cy = numSharedNodes cx cy == 2 && numSharedEdges cx cy == 1

||| True, if the two cycles share a single node.
export
isSpiro : (cx,cy : Cycle g) -> Bool
isSpiro cx cy = numSharedNodes cx cy == 1

public export
record CycleSets (g : Graph e n) where
  constructor CS
  cr  : List (Cycle g)
  mcb : List (Cycle g)

%runElab deriveIndexed "CycleSets" [Show,Eq]

public export
data Candidates : (g : Graph e n) -> Type where
  Empty   : Candidates g
  Isolate : Subgraph g -> NCycle g -> Candidates g
  System  : (sg : Subgraph g) -> List (NCycle sg) -> Candidates g
