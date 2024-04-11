module BFS

import Data.Graph.Indexed.Query.BFS
import Data.List
import Data.String
import Data.SnocList
import Test.Data.Graph.Indexed.Generators
import Text.Smiles.Simple

%default total

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

unlabeledGraphs : Gen (Graph Bits8 Bits8)
unlabeledGraphs = sparseGraph (linear 0 30) (linear 0 100) anyBits8 anyBits8

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

-- test if a sequence of nodes is a walk
isWalk : IGraph k e n -> List (Fin k) -> Bool
isWalk g (x::y::t) = adjacent g x y && isWalk g (y::t)
isWalk _ _         = True

-- every node appears at most once in a shortest path
uniqueNodes : List (Fin k) -> Bool
uniqueNodes = go . sort
  where
    go : List (Fin k) -> Bool
    go (x::y::t) = x /= y && go (y::t)
    go _         = True

last : a -> List a -> a
last v []      = v
last _ (x::xs) = last x xs

-- tests that a path is indeed a shortest path by running a
-- breadth first search from its starting node and testing the
-- paths end node and length against the BFS result
smallestLength : {k : _} -> IGraph k e n -> List (Fin k) -> Bool
smallestLength g []      = False
smallestLength g (x::xs) =
  let y := last x xs
   in S (length xs) == maybe 0 length (bfs g x y)

-- test the given predicate for all shortest paths for all pairs
-- of connected nodes in a graph
testPaths : {k : _} -> (List (Fin k) -> Bool) -> IGraph k e n -> Bool
testPaths p g = all (all (p . (<>> [])) . shortestPaths g) (nodes g)

--------------------------------------------------------------------------------
-- Example Graphs
--------------------------------------------------------------------------------

-- an encoding of phenole starting with the oxygen
phenole : Maybe (Graph Bond Elem)
phenole = readSmiles "OC=1CC=CC=C1"

-- dimethylamino pyridine
dmap : Maybe (Graph Bond Elem)
dmap = readSmiles "C1(N(C)C)C=CN=CC=1"

-- octacontane
octac : Maybe (Graph Bond Elem)
octac = readSmiles $ replicate 80 'C'

testSPs : Maybe (Graph e n) -> Nat -> List (List Nat) -> Bool
testSPs Nothing        n _   = False
testSPs (Just $ G o g) n nss =
  let Just x := natToFin n o | Nothing => False
   in map (map finToNat . (<>> [])) (shortestPaths g x) == nss

-- shortest path from start to target node
testSP : Maybe (Graph e n) -> (start,target : Nat) -> List Nat -> Bool
testSP Nothing        _ _ _  = False
testSP (Just $ G o g) s t ns =
  let Just x := natToFin s o | Nothing => False
      Just y := natToFin t o | Nothing => False
   in map ((<>> []) . map finToNat) (bfs g x y) == Just ns

prop_phenole : Property
prop_phenole =
  property1 $ assert $
    testSPs phenole 1 [[1,0],[1,2],[1,6],[1,2,3],[1,6,5],[1,2,3,4]]

prop_phenole_short : Property
prop_phenole_short =
  property1 $ assert $
    testSP phenole 1 3 [1,2,3]

prop_dmap : Property
prop_dmap =
  property1 $ assert $
    testSPs dmap 0 [[0,1],[0,4],[0,8],[0,1,2],[0,1,3],[0,4,5],[0,8,7],[0,4,5,6]]

prop_dmap_short : Property
prop_dmap_short =
  property1 $ assert $
    testSP dmap 0 5 [0,4,5]

prop_dmap_short2 : Property
prop_dmap_short2 =
  property1 $ assert $
    testSP dmap 5 0 [5,4,0]

prop_octacontan_short : Property
prop_octacontan_short =
  property1 $ assert $
    testSP octac 0 79 [0..79]

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

-- all shortest paths between nodes are walks (neighbouring nodes in the path
-- are connected via an edge in the graph)
prop_walk : Property
prop_walk =
  property $ do
    G o g <- forAll unlabeledGraphs
    assert $ testPaths (isWalk g) g

-- all shortest paths between nodes contain every node at most once
prop_unique : Property
prop_unique =
  property $ do
    G o g <- forAll unlabeledGraphs
    assert $ testPaths uniqueNodes g

-- all shortest paths have at least two nodes
prop_properPath : Property
prop_properPath =
  property $ do
    G o g <- forAll unlabeledGraphs
    assert $ testPaths ((> 1) . length) g

-- the lengths of unweighted shortest paths are in accordance with
-- the result of a basic breadth-first search
prop_shortestPath : Property
prop_shortestPath =
  property $ do
    G o g <- forAll unlabeledGraphs
    assert $ testPaths (smallestLength g) g

export
props : Group
props =
  MkGroup "BFS"
    [ ("prop_walk", prop_walk)
    , ("prop_unique", prop_unique)
    , ("prop_properPath", prop_properPath)
    , ("prop_shortestPath", prop_shortestPath)
    , ("prop_phenole", prop_phenole)
    , ("prop_phenole_short", prop_phenole_short)
    , ("prop_dmap", prop_dmap)
    , ("prop_dmap_short", prop_dmap_short)
    , ("prop_dmap_short2", prop_dmap_short2)
    , ("prop_octacontan_short", prop_octacontan_short)
    ]
