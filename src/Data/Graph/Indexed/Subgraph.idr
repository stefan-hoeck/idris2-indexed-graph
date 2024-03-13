module Data.Graph.Indexed.Subgraph

import Data.Array
import Data.AssocList.Indexed
import Data.Graph.Indexed.Query.DFS
import Data.Graph.Indexed.Types
import Data.SortedMap

%default total

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

||| A mapping from indices in one array (or graph) to indices in another.
public export
0 NodeMap : (k,m : Nat) -> Type
NodeMap k m = SortedMap (Fin k) (Fin m)

||| Computes a node map from an array of indices.
export %inline
nodeMap : {k : _} -> IArray k (Fin m) -> NodeMap m k
nodeMap = foldrKV (flip insert) empty

||| Adjust an assoc list (a list of edges) according to a mapping from
||| old nodes to new nodes.
export %inline
adjAssocList : NodeMap k m -> AssocList k e -> AssocList m e
adjAssocList nm = foldl ins empty . pairs
  where
    ins : AssocList m e -> (Fin k,e) -> AssocList m e
    ins l (x,ve) = maybe l (\y => insert y ve l) (lookup x nm)

--------------------------------------------------------------------------------
-- Subgraphs
--------------------------------------------------------------------------------

||| An indexed graph that represents a subgraph on another one.
|||
||| Every node is linked to the node in the original graph.
public export
0 ISubgraph : (k,m : Nat) -> (e,n : Type) -> Type
ISubgraph k m e n = IGraph k e (Fin m, n)

||| An graph that represents a subgraph on another one.
|||
||| Every node is linked to the node in the original graph.
public export
0 Subgraph : (m : Nat) -> (e,n : Type) -> Type
Subgraph m e n = Graph e (Fin m, n)

||| Computes a subgraph of a graph containing the given nodes.
||| Runs in O(k * log (k)) for sparse graphs.
export
subgraph : {k : _} -> IGraph m e n -> IArray k (Fin m) -> ISubgraph k m e n
subgraph (IG g) arr = let m := nodeMap arr in IG $ map (adj m) arr

  where
    adj : NodeMap m k -> Fin m -> Adj k e (Fin m, n)
    adj m fm = let (A l ns) := at g fm in A (fm,l) (adjAssocList m ns)

||| Extracts the connected components of a potentially disconnected
||| graph.
|||
||| Runs in O(k * log(k)) for sparse graphs.
export
connectedComponents : {k : _} -> IGraph k e n -> List (Subgraph k e n)
connectedComponents g = map (toComp . (<>> [])) (components g)
  where
    toComp : List (Fin k) -> Subgraph k e n
    toComp xs = G _ $ subgraph g (arrayL xs)
