module Test.Data.Graph.Indexed.Generators

import Data.List
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
  -> (nrEdges : Hedgehog.Range Nat)
  -> (label   : Gen e)
  -> Gen (List $ Edge k e)
edges {k = S (S m)} nr lbl = list nr (edge lbl)
edges               _  _   = pure []

pairs : List a -> List (a,a)
pairs vs = [| MkPair vs vs |]

||| Decides for every possible pair of nodes in a graph of order `k`
||| whether to add an edge between these nodes by using a label
||| generator that returns a `Maybe e`.
|||
||| This allows us to create very sparse and very dense graphs based
||| on the edge generator, with nice edge distributions.
export
distEdges : {k : _} -> (label : Gen (Maybe e)) -> Gen (List $ Edge k e)
distEdges lbl = catMaybes <$> traverse gen (pairs $ allFinsFast k)
  where
    gen : (Fin k, Fin k) -> Gen (Maybe $ Edge k e)
    gen (x,y) with (compare x y) proof prf
      _ | LT = map (\v => E x y v) <$> lbl
      _ | _  = pure Nothing

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

||| Generates a graph with the numbers of nodes and a random distribution
||| of edges.
export
graph :
     (nrNodes   : Hedgehog.Range Nat)
  -> (edgeLabel : Gen $ Maybe e)
  -> (nodeLabel : Gen n)
  -> Gen (Graph e n)
graph nrn el nl = do
  ns <- list nrn nl
  es <- distEdges el
  pure $ (G _ $ mkGraphL ns es)
