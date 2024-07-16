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

data BCS = ST | CO

0 Stack : Type -> Nat -> Type
Stack s n = Ref1 ST s (List $ Fin n)

0 Comps : Type -> Nat -> Type
Comps s n = Ref1 CO s (List (List $ Fin n))

pop : Stack s k => F1' s
pop = mod1At ST $ \case h::t => t; [] => []

extractComp : Fin k -> Stack s k => Comps s k => F1' s
extractComp n t =
  let st # t2 := read1At ST t
      (cmp,rem) := go [<] st
   in write1At ST rem (mod1At CO (cmp::) t2)

  where
    go : SnocList (Fin k) -> List (Fin k) -> (List $ Fin k, List $ Fin k)
    go sx (x :: xs) = if n == x then (sx <>> [x], xs) else go (sx :< x) xs
    go sx []        = (sx <>> [], []) -- this should not happen

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
  alloc k 0 $ \t =>
    let st # t2 := ref1At ST (the (List $ Fin k) []) t
        co # t3 := ref1At CO (the (List (List $ Fin k)) []) t2
     in go (allFinsFast k) t3
  where
    covering sc :
         Fin k
      -> Fin k
      -> Nat
      -> {auto _ : Stack s k}
      -> {auto _ : Comps s k}
      -> {auto _ : MArray () s k Nat}
      -> F1 s Nat

    covering scs :
         List (Fin k)
      -> Fin k
      -> Nat
      -> {auto _ : Stack s k}
      -> {auto _ : Comps s k}
      -> {auto _ : MArray () s k Nat}
      -> F1 s Nat
    scs []      p dpt t = dpt # t
    scs (x::xs) p dpt t =
      let r2 # t2 := sc x p dpt t
          r3 # t3 := scs xs p dpt t2
       in min r2 r3 # t3

    sc n p dpt t =
      let Z  # t2 := get n t | res => res
          t3      := set n dpt t2
          t4      := mod1At ST (n::) t3
          dc # t5 := scs (filter (/= p) $ neighbours g n) n (S dpt) t4
       in case compare dc dpt of
            LT => dc # t5
            EQ => dc # extractComp n t5
            GT => dpt # pop t5

    go :
         List (Fin k)
      -> {auto _ : Stack s k}
      -> {auto _ : Comps s k}
      -> {auto _ : MArray () s k Nat}
      -> F1 s (List $ Subgraph k e n)
    go []      t = mapR1 (map (subgraphL g)) (read1At CO t)
    go (n::ns) t =
      let Z # t2 := get n t | _ # t2 => go ns t2
          _ # t3 := assert_total $ sc n n 1 t2
       in go ns t3
