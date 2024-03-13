module Subgraphs

import Text.Smiles.Simple
import Data.Graph.Indexed.Util
import Data.Graph.Indexed.Query.DFS
import Data.Graph.Indexed.Subgraph
import Data.List
import Data.Vect
import Test.Data.Graph.Indexed.Generators

%default total

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

unlabeledGraphs : Gen (Graph Bits8 Bits8)
unlabeledGraphs = sparseGraph (linear 0 30) (linear 0 100) anyBits8 anyBits8

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

-- test that the given edge (from the subgraph) corresponds to
-- an edge in the original graph
testEdge : Eq e => IGraph k e n -> ISubgraph m k e n -> Edge m e -> Bool
testEdge g h (E n1 n2 el) =
  elab g (fst $ lab h n1) (fst $ lab h n2) == Just el

-- test that the given node (from the subgraph) corresponds to
-- a node in the original graph
testNode : Eq n => IGraph k e n -> ISubgraph m k e n -> Fin m -> Bool
testNode g h x = lab g (fst $ lab h x) == snd (lab h x)

isBiconnected : {k : _} -> IGraph k e n -> Bool
isBiconnected g =
  all (\(E n1 n2 _) => isConnected (delEdge n1 n2 g)) (edges g)

--------------------------------------------------------------------------------
-- Example Graphs
--------------------------------------------------------------------------------

-- an encoding of phenole starting with the oxygen
phenole : Maybe (Graph Bond Elem)
phenole = readSmiles "OC=1CC=CC=C1"

-- an encoding of indole starting with the nitrogen
indole : Maybe (Graph Bond Elem)
indole = readSmiles "N1C=C2C=CC=CC=C12"

-- an encoding of skatole starting with the methyl group
skatole : Maybe (Graph Bond Elem)
skatole = readSmiles "CN1C=C2C=CC=CC=C12"

-- dimethylamino pyridine
dmap : Maybe (Graph Bond Elem)
dmap = readSmiles "C1(N(C)C)C=CN=CC=1"

-- bisphenole BP (four essential six-rings)
bbp : Maybe (Graph Bond Elem)
bbp = readSmiles "C(C=1CC=CC=C1)(C=1CC(O)=CC=C1)(C=1CC=CC=C1)C=1CC(O)=CC=C1"
--                0 1        6   7     10    13  14       19 20    23    27

toNodes : Graph e (Fin m, n) -> List Nat
toNodes (G k g) = sort $ map (finToNat . fst . lab g) (nodes g)

test2Comps : Maybe (Graph e n) -> List (List Nat) -> Bool
test2Comps Nothing _ = False
test2Comps (Just $ G o g) ns =
  let cs := toNodes <$> biconnectedComponents g
   in sort cs == ns

prop_phenole : Property
prop_phenole = property1 $ assert (test2Comps phenole [[1,2,3,4,5,6]])

prop_indole : Property
prop_indole = property1 $ assert (test2Comps indole [[0,1,2,3,4,5,6,7,8]])

prop_skatole : Property
prop_skatole = property1 $ assert (test2Comps skatole [[1,2,3,4,5,6,7,8,9]])

prop_dmap : Property
prop_dmap = property1 $ assert (test2Comps dmap [[0,4,5,6,7,8]])

prop_bbp : Property
prop_bbp =
  property1 . assert $
    test2Comps bbp
      [ [1,2,3,4,5,6]
      , [7,8,9,11,12,13]
      , [14,15,16,17,18,19]
      , [20,21,22,24,25,26]
      ]

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

-- the sum of orders of all connected components of a graph is
-- equal to the order of the graph (we do not miss or add any vertices)
prop_order : Property
prop_order =
  property $ do
    G o g <- forAll unlabeledGraphs
    o === sum (order <$> connectedComponents g)

-- the sum of sizes of all connected components of a graph is
-- equal to the size of the graph (we do not miss or add any edges)
prop_size : Property
prop_size =
  property $ do
    G o g <- forAll unlabeledGraphs
    size g === sum ((\(G _ h) => size h) <$> connectedComponents g)

-- every edge in a connected component can be linked to the
-- corresponding edge in the original graph with the same label
prop_edges : Property
prop_edges =
  property $ do
    G o g <- forAll unlabeledGraphs
    assert $
      all (\(G _ h) => all (testEdge g h) $ edges h) (connectedComponents g)

-- every node in a connected component can be linked to the
-- corresponding node in the original graph with the same label
prop_nodes : Property
prop_nodes =
  property $ do
    G o g <- forAll unlabeledGraphs
    assert $
      all (\(G _ h) => all (testNode g h) (nodes h)) (connectedComponents g)

-- every connected component of a graph must be connected (doh!)
prop_connected : Property
prop_connected =
  property $ do
    G o g <- forAll unlabeledGraphs
    assert $ all (\(G _ h) => isConnected h) (connectedComponents g)

-- every biconnected component of a graph must be biconnected (doh!)
prop_biconnected : Property
prop_biconnected =
  property $ do
    G o g <- forAll unlabeledGraphs
    assert $ all (\(G _ h) => isBiconnected h) (biconnectedComponents g)

-- every node in a biconnected component can be linked to the
-- corresponding node in the original graph with the same label
prop_biconnected_nodes : Property
prop_biconnected_nodes =
  property $ do
    G o g <- forAll unlabeledGraphs
    assert $
      all (\(G _ h) => all (testNode g h) (nodes h)) (biconnectedComponents g)

-- every edge in a biconnected component can be linked to the
-- corresponding edge in the original graph with the same label
prop_biconnected_edges : Property
prop_biconnected_edges =
  property $ do
    G o g <- forAll unlabeledGraphs
    assert $
      all (\(G _ h) => all (testEdge g h) $ edges h) (biconnectedComponents g)

export
props : Group
props =
  MkGroup "Subgraph"
    [ ("prop_order", prop_order)
    , ("prop_size", prop_size)
    , ("prop_edges", prop_edges)
    , ("prop_nodes", prop_nodes)
    , ("prop_connected", prop_connected)
    , ("prop_biconnected", prop_biconnected)
    , ("prop_biconnected_nodes", prop_biconnected_nodes)
    , ("prop_biconnected_edges", prop_biconnected_edges)
    , ("prop_phenole", prop_phenole)
    , ("prop_indole", prop_indole)
    , ("prop_skatole", prop_skatole)
    , ("prop_dmap", prop_dmap)
    , ("prop_bbp", prop_bbp)
    ]
