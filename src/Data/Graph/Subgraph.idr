module Data.Graph.Subgraph

import Data.Array
import Data.Array.Mutable
import Data.AssocList.Indexed
import Data.Graph
import Data.Graph.Query.DFS
import Data.Linear.Ref1
import Data.SortedMap

%default total

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

||| A mapping from indices in one array (or graph) to indices in another.
public export
0 NodeMap : (g : Graph e n) -> (m : Nat) -> Type
NodeMap g m = SortedMap (Node g) (Fin m)

||| Computes a node map from an array of indices.
export %inline
nodeMap : {k : _} -> IArray k (Node g) -> NodeMap g k
nodeMap = foldrKV (flip insert) empty

||| Adjust an assoc list (a list of edges) according to a mapping from
||| old nodes to new nodes.
export %inline
adjAssocList : NodeMap g m -> AssocList g.order e -> AssocList m e
adjAssocList nm = foldl ins empty . pairs
  where
    ins : AssocList m e -> (Fin g.order,e) -> AssocList m e
    ins l (x,ve) = maybe l (\y => insert y ve l) (lookup (N x) nm)

--------------------------------------------------------------------------------
-- Subgraphs
--------------------------------------------------------------------------------

||| An graph that represents a subgraph on another one.
|||
||| Every node is linked to the node in the original graph.
public export
0 Subgraph : (g : Graph e n) -> Type
Subgraph g = Graph e (Node g)

||| Computes a subgraph of a graph containing the given nodes.
||| Runs in O(k * log (k)) for sparse graphs.
export
subgraph : {k : _} -> (g : Graph e n) -> IArray k (Node g) -> Subgraph g
subgraph g arr =
 let m := nodeMap arr
  in G _ $ map (fun m) arr

  where
    fun : NodeMap g k -> Node g -> IAdj k e (Node g)
    fun m fm = let IA _ ns := gadj fm in IA fm (adjAssocList m ns)

||| Computes a subgraph of a graph containing the given nodes.
||| Runs in O(k * log (k)) for sparse graphs.
export
subgraphL : (g : Graph e n) -> Nodes g -> Subgraph g
subgraphL g ns = subgraph g (arrayL ns)

||| Extracts the connected components of a potentially disconnected
||| graph.
|||
||| Runs in O(k * log(k)) for sparse graphs.
export
connectedComponents : (g : Graph e n) -> List (Subgraph g)
connectedComponents g = subgraphL g . (<>> []) <$> components g

||| Converts the node of a subgraph to the corresponding node in the
||| original graph.
export %inline
origin : {h : Subgraph g} -> Node h -> Node g
origin = lab

||| Converts the edge of a subgraph to the corresponding edge in the
||| original graph.
|||
||| This comes with the potential of failure, since we cannot prove that
||| the subgraph is injective, that is, distinct nodes in the subgraph
||| point at distinct nodes in the original graph.
export
originEdge : {g : _} -> (h : Subgraph g) -> LEdg h -> Maybe (LEdg g)
originEdge h (LE x y l) = mkLEdg (origin x) (origin y) l

--------------------------------------------------------------------------------
-- Biconnected Components
--------------------------------------------------------------------------------

0 Stack : Type -> Graph e n -> Type
Stack s g = Ref s (List $ Node g)

0 Comps : Type -> Graph e n -> Type
Comps s g = Ref s (List (List $ Node g))

pop : Stack s g -> F1' s
pop s = mod1 s $ \case h::t => t; [] => []

extractComp : Node g -> Stack s g -> Comps s g -> F1' s
extractComp n s c t =
  let st # t := read1 s t
      (cmp,rem) := go [<] st
      _ # t     := mod1 c (cmp::) t
   in write1 s rem t

  where
    go : Sedon g -> Nodes g -> (Nodes g, Nodes g)
    go sx (x :: xs) = if n == x then (sx <>> [x], xs) else go (sx :< x) xs
    go sx []        = (sx <>> [], []) -- this should not happen

parameters (g : Graph e n)
           (d : MArray t g.order Nat)
           (s : Stack t g)
           (c : Comps t g)
    covering sc : Node g -> Node g -> Nat -> F1 t Nat

    covering scs : Nodes g -> Node g -> Nat -> F1 t Nat
    scs []      p dpt t = dpt # t
    scs (x::xs) p dpt t =
      let r2 # t2 := sc x p dpt t
          r3 # t3 := scs xs p dpt t2
       in min r2 r3 # t3

    sc n p dpt t =
      let Z  # t := get d n.node t | res => res
          _ # t  := set d n.node dpt t
          _ # t  := mod1 s (n::) t
          dc # t := scs (filter (/= p) $ neighbours n) n (S dpt) t
       in case compare dc dpt of
            LT => dc # t
            EQ => let _ # t := extractComp n s c t in dc # t
            GT => let _ # t := Subgraph.pop s t in dpt # t

    go : Nodes g -> F1 t (List $ Subgraph g)
    go []      t = mapR1 (map (subgraphL g)) (read1 c t)
    go (n::ns) t =
      let Z # t := get d n.node t | _ # t => go ns t
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
biconnectedComponents : (g : Graph e n) -> List (Subgraph g)
biconnectedComponents g =
  run1 $ \t =>
    let c # t := ref1 (the (List $ Nodes g) []) t
        s # t := ref1 (the (Nodes g) []) t
        d # t := marray1 g.order Z t
     in go g d s c (nodes g) t
