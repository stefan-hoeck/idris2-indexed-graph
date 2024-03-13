module Data.Graph.Indexed.Subgraph

import Data.Array
import Data.Array.Mutable
import Data.AssocList.Indexed
import Data.Graph.Indexed.Query.DFS
import Data.Graph.Indexed.Types
import Data.Graph.Indexed.Util
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

||| Computes a subgraph of a graph containing the given nodes.
||| Runs in O(k * log (k)) for sparse graphs.
export
subgraphL : IGraph m e n -> List (Fin m) -> Subgraph m e n
subgraphL g ns = G _ $ subgraph g (arrayL ns)

||| Extracts the connected components of a potentially disconnected
||| graph.
|||
||| Runs in O(k * log(k)) for sparse graphs.
export
connectedComponents : {k : _} -> IGraph k e n -> List (Subgraph k e n)
connectedComponents g = subgraphL g . (<>> []) <$> components g

--------------------------------------------------------------------------------
-- Biconnected Components
--------------------------------------------------------------------------------

record BCState (k : Nat) where
  constructor S
  1 depth : MArray k Nat
  stack   : List (Fin k)
  comps   : List (List $ Fin k)

||| Extracts the biconnected components of a graph (Hopcroft/Tarjan algorithm).
|||
||| A graph is "biconnected" or "2-connected" if at least two of
||| its edges need to be removed to get to a disconnected graph.
|||
||| Biconnected subgraphs only consist of cyclic vertices and edges.
||| When analyzing the cycles in a graph, for instance, when computing
||| the relevant cycles or a minimal cycle basis, it is always sufficient
||| - and often much more efficient - to inspect the biconnected
||| components in isolation.
export
biconnectedComponents : {k : _} -> IGraph k e n -> List (Subgraph k e n)
biconnectedComponents g =
  unrestricted $ alloc k 0 (\arr => go (allFinsFast k) (S arr [] []))
  where
    scMany : List (Fin k) -> Nat -> BCState k -@ CRes Nat (BCState k)
    scMany = ?fooobar

    sc : Fin k -> Nat -> BCState k -@ CRes Nat (BCState k)
    -- sc n depth (S d s cs) =
    --   let 0 # d2 := get n d | dpth # d2 => dpth # S d2 s cs
    --    in scMany (filter (/= n) $ neighbours g n) (S depth) (S d2 s cs)

    go : List (Fin k) -> BCState k -@ Ur (List $ Subgraph k e n)
    go []      (S d s cs) = discarding d (MkBang $ subgraphL g <$> cs)
    go (n::ns) (S d s cs) =
      let Z # d2 := get n d | _ # d2 => go ns (S d2 s cs)
          _ # s2 := sc n 1 (S d2 s cs)
       in go ns s2
