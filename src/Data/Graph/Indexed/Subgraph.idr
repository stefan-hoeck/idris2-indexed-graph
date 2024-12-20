module Data.Graph.Indexed.Subgraph

import Data.Array
import Data.Array.Mutable
import Data.AssocList.Indexed
import Data.Graph.Indexed.Query.DFS
import Data.Graph.Indexed.Types
import Data.Graph.Indexed.Util
import Data.Linear.Ref1
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
    adj m fm = let A l ns := at g fm in A (fm,l) (adjAssocList m ns)

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

||| Converts the node of a subgraph to the corresponding node in the
||| original graph.
export
origin : ISubgraph k m e n -> Fin k -> Fin m
origin s = fst . lab s

||| Converts the edge of a subgraph to the corresponding edge in the
||| original graph.
|||
||| This comes with the potential of failure, since we cannot prove that
||| the subgraph is injective, that is, distinct nodes in the subgraph
||| point at distinct nodes in the original graph.
export
originEdge : ISubgraph k m e n -> Edge k e -> Maybe (Edge m e)
originEdge s (E x y l) = mkEdge (origin s x) (origin s y) l

--------------------------------------------------------------------------------
-- Biconnected Components
--------------------------------------------------------------------------------

0 Stack : Nat -> Type
Stack n = Ref1 (List $ Fin n)

0 Comps : Nat -> Type
Comps n = Ref1 (List (List $ Fin n))

pop : (s : Stack k) -> F1' [d,s,c]
pop s = mod1 s $ \case h::t => t; [] => []

extractComp : Fin k -> (s : Stack k) -> (c : Comps k) -> F1' [d,s,c]
extractComp n s c t =
  let st # t := read1 s t
      (cmp,rem) := go [<] st
      _ # t     := mod1 c (cmp::) t
   in write1 s rem t

  where
    go : SnocList (Fin k) -> List (Fin k) -> (List $ Fin k, List $ Fin k)
    go sx (x :: xs) = if n == x then (sx <>> [x], xs) else go (sx :< x) xs
    go sx []        = (sx <>> [], []) -- this should not happen

parameters (g : IGraph k e n)
           (d : MArray k Nat)
           (s : Stack k)
           (c : Comps k)
    covering sc : Fin k -> Fin k -> Nat -> F1 [d,s,c] Nat

    covering scs : List (Fin k) -> Fin k -> Nat -> F1 [d,s,c] Nat
    scs []      p dpt t = dpt # t
    scs (x::xs) p dpt t =
      let r2 # t2 := sc x p dpt t
          r3 # t3 := scs xs p dpt t2
       in min r2 r3 # t3

    sc n p dpt t =
      let Z  # t := get d n t | res => res
          _ # t  := set d n dpt t
          _ # t  := mod1 s (n::) t
          dc # t := scs (filter (/= p) $ neighbours g n) n (S dpt) t
       in case compare dc dpt of
            LT => dc # t
            EQ => let _ # t := extractComp n s c t in dc # t
            GT => let _ # t := Subgraph.pop s t in dpt # t

    go : List (Fin k) -> F1 [d,s,c] (List $ Subgraph k e n)
    go []      t = mapR1 (map (subgraphL g)) (read1 c t)
    go (n::ns) t =
      let Z # t := get d n t | _ # t => go ns t
          _ # t := assert_total $ sc n n 1 t
       in go ns t

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
  run1 $ \t =>
    let c # t := ref1 (the (List (List $ Fin k)) []) t
        s # t := ref1 (the (List $ Fin k) []) t
        d # t := newMArray k Z t
        r # t := go g d s c (allFinsFast k) t
        _ # t := Core.release d t
        _ # t := Ref1.release s t
        _ # t := Ref1.release c t
     in r # t
