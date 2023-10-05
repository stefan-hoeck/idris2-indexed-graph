module Generators

import public Data.Graph.Indexed
import public Hedgehog

%default total

||| Generates a single `Edge` for a graph of order `k + 2`.
|||
||| Note: Since graphs of order 1 and 0 can't have any edges
|||       (remember, we don't support self-loops), the smallest
|||       graph with an edge has order two.
export
edge : {k : _} -> Gen e -> Gen (Edge (S $ S k) e)
edge lbl =
  let gnode = fin {n = S (S k)} (constant FZ last)
   in [| toEdge gnode gnode lbl |]
  where
    toEdge : Fin (S $ S k) -> Fin (S $ S k) -> e -> Edge (S $ S k) e
    toEdge k j l = fromMaybe (E 0 1 l) (mkEdge k j l)

||| Generates a list of edges for a graph of size `k`.
|||
||| Note: This is useful for sparse graphs. An alternative
|||       is to generate and edge between every pair of
|||       nodes with a certain probability.
export
edges :
     {k : _}
  -> (nrEdges    : Hedgehog.Range Nat)
  -> (label      : Gen e)
  -> Gen (List $ Edge k e)
edges {k = S (S m)} nr lbl = list nr (edge lbl)
edges               _  _   = pure []

||| Generates a graph with the numbers of nodes and edges in the
||| given ranges.
export
sparseGraph :
     (nrNodes   : Hedgehog.Range Nat)
  -> (nrEdges   : Hedgehog.Range Nat)
  -> (edgeLabel : Gen e)
  -> (nodeLabel : Gen n)
  -> Gen (Graph e n)
sparseGraph nrn nre el nl = do
  ns <- list nrn nl
  es <- edges nre el
  pure $ (G _ $ mkGraphL ns es)
