module Data.Graph.Indexed.Util

import Data.Array.Indexed
import Data.AssocList.Indexed
import Data.Graph.Indexed.Types
import Data.List
import Data.String

%default total

--------------------------------------------------------------------------------
--          Internal utilities
--------------------------------------------------------------------------------

||| Insert a single edge into a mutable array-representation of a graph.
export
linsEdge : Edge k e -> MArray k (Adj k e n) -@ MArray k (Adj k e n)
linsEdge (E n1 n2 el) a1 =
  let a2 := modify n1 {neighbours $= insert n2 el} a1
   in modify n2 {neighbours $= insert n1 el} a2

||| Delete a single edge from a mutable array-representation of a graph.
export
ldelEdge : (n1, n2 : Fin k) -> MArray k (Adj k e n) -@ MArray k (Adj k e n)
ldelEdge n1 n2 a1 =
  let a2 := modify n1 {neighbours $= delete n2} a1
   in modify n2 {neighbours $= delete n1} a2

||| Insert a bunch of edges into a mutable array-representation of a graph.
export
linsEdges :
     List (Edge k e)
  -> (MArray k (Adj k e n) -@ !* b)
  -@ MArray k (Adj k e n)
  -@ !* b
linsEdges []      f a1 = f a1
linsEdges (x::xs) f a1 = let a2 := linsEdge x a1 in linsEdges xs f a2

||| Insert a bunch of edges into a mutable array-representation of a graph.
export
ldelEdges :
     List (Fin k, Fin k)
  -> (MArray k (Adj k e n) -@ !* b)
  -@ MArray k (Adj k e n)
  -@ !* b
ldelEdges []          f a1 = f a1
ldelEdges ((x,y)::xs) f a1 = let a2 := ldelEdge x y a1 in ldelEdges xs f a2

-- we return only edges to nodes greater than the node in the
-- context to avoid returning every edge twice in `labEdges`.
ctxtEdges : Fin k -> Adj k e n -> SnocList (Edge k e)
ctxtEdges x (A _ ns) = foldlKV acc [<] ns
  where acc : Fin k -> SnocList (Edge k e) -> e -> SnocList (Edge k e)
        acc y sp v with (compFin x y) proof eq
          _ | LT = sp :< E x y v
          _ | _  = sp

--------------------------------------------------------------------------------
--          Inspecting Graphs
--------------------------------------------------------------------------------

||| A list of contexts of a graph
export
contexts : {k : _} -> IGraph k e n -> List (Context k e n)
contexts = foldrKV (\x,(A l ns),cs => C x l ns :: cs) [] . graph

||| A list of all labeled nodes of a `Graph`
export
labNodes  : {k : _} -> IGraph k e n -> List (Fin k, n)
labNodes = foldrKV (\x,(A l _),cs => (x,l) :: cs) [] . graph

export %inline
adj : IGraph k e n -> Fin k -> Adj k e n
adj (IG g) k = at g k

export %inline
lab : IGraph k e n -> Fin k -> n
lab g = label . adj g

export %inline
neighbours : IGraph k e n -> Fin k -> AssocList k e
neighbours g = neighbours . adj g

export
lneighbours : IGraph k e n -> Fin k -> AssocList k (e,n)
lneighbours g = mapKV (\x,e => (e, lab g x)) . neighbours g

||| Find the label for an `Edge`.
export
elab : IGraph k e n -> Fin k -> Fin k -> Maybe e
elab (IG g) x y = lookup y . neighbours $ at g x

||| List all 'Node's in the 'Graph'.
export
nodes : {k : _} -> IGraph k e n -> List (Fin k)
nodes = map fst . labNodes

||| A list of all `LEdge`s in the `Graph` (in lexicographic order).
export
edges  : {k : _} -> IGraph k e n -> List (Edge k e)
edges (IG g) = foldrKV (\x,adj,es => ctxtEdges x adj <>> es) [] g

||| The number of edges in the graph.
export
size : {k : _} -> IGraph k e n -> Nat
size = length . edges

||| The degree of the `Node`.
export
deg : IGraph k e n -> Fin k -> Nat
deg g = length . neighbours g

||| Checks if there is an undirected edge between two nodes.
export
hasNeighbour : IGraph k e n -> Fin k -> Fin k -> Bool
hasNeighbour g k = isJust . elab g k

--------------------------------------------------------------------------------
--          Making Graphs
--------------------------------------------------------------------------------

||| An empty `Graph`
export
empty : IGraph 0 e n
empty = IG empty

0 mapLen : (f : a -> b) -> (as : List a) -> length (map f as) === length as
mapLen f []        = Refl
mapLen f (x :: xs) = cong S $ mapLen f xs

%inline
relength : {auto 0 prf : k === m} -> MArray k x -@ MArray m x
relength v = replace {p = \a => MArray a x} prf v


||| Create a `Graph` from the list of labeled nodes and
||| edges.
export
mkGraph : (ns : List n) -> List (Edge (length ns) e) -> IGraph (length ns) e n
mkGraph []        _  = empty
mkGraph ns@(_::_) es =
  IG . unrestricted $ allocList (map (`A` empty) ns) $ \x =>
    let x2 := relength @{mapLen (`A` empty) ns} x in linsEdges es freeze x2

export %inline
generate : (k : Nat) -> (Fin k -> Adj k e n) -> IGraph k e n
generate k f = IG $ generate k f

--------------------------------------------------------------------------------
--          Modifying Graphs
--------------------------------------------------------------------------------

export
insEdges : {k : _} -> List (Edge k e) -> IGraph k e n -> IGraph k e n
insEdges {k = 0}   es g = empty
insEdges {k = S v} es g =
  IG . unrestricted $ allocGen (S v) (adj g) (linsEdges es freeze)

||| Insert an `Edge` into the 'IGraph'.
export %inline
insEdge : {k : _} -> Edge k e -> IGraph k e n -> IGraph k e n
insEdge = insEdges . pure

||| Remove multiple 'Edge's from the 'Graph'.
export
delEdges : {k : _} -> List (Fin k, Fin k) -> IGraph k e n -> IGraph k e n
delEdges {k = 0}   _  _ = empty
delEdges {k = S v} ps g =
  IG . unrestricted $ allocGen (S v) (adj g) (ldelEdges ps freeze)

||| Remove an 'Edge' from the 'Graph'.
export %inline
delEdge : {k : _} -> (x,y : Fin k) -> IGraph k e n -> IGraph k e n
delEdge x y = delEdges [(x,y)]

-- ||| Insert a labeled node into the `Graph`.
-- ||| The behavior is undefined if the node is already
-- ||| in the graph.
-- export
-- insNode : Node -> (lbl : n) -> Graph e n -> Graph e n
-- insNode v l (MkGraph m) = MkGraph $ insert v (MkAdj l $ MkAL []) m
--
--
-- ||| Insert multiple `LNode`s into the `Graph`.
-- export
-- insNodes : List (LNode n) -> Graph e n -> Graph e n
-- insNodes vs g = foldl (\g2,(MkLNode k l) => insNode k l g2) g vs
--
-- ||| Remove a 'Node' from the 'Graph'.
-- export
-- delNode : Node -> Graph e n -> Graph e n
-- delNode v g = case match v g of
--   Split _ gr => gr
--   Empty      => g
--
-- ||| Remove multiple 'Node's from the 'Graph'.
-- export
-- delNodes : List Node -> Graph e n -> Graph e n
-- delNodes vs g = foldl (flip delNode) g vs
--
-- ||| Returns the subgraph only containing the labelled nodes which
-- ||| satisfy the given predicate.
-- export
-- labnfilter : (LNode n -> Bool) -> Graph e n -> Graph e n
-- labnfilter p gr = delNodes (map node . filter (not . p) $ labNodes gr) gr
--
-- ||| Returns the subgraph only containing the nodes which satisfy the
-- ||| given predicate.
-- export
-- nfilter : (Node -> Bool) -> Graph e n -> Graph e n
-- nfilter f = labnfilter (f . node)
--
-- ||| Returns the subgraph only containing the nodes whose labels
-- ||| satisfy the given predicate.
-- export
-- labfilter : (n -> Bool) -> Graph e n -> Graph e n
-- labfilter f = labnfilter (f . label)
--
-- ||| Retruns the same graph additionaly containing list of connecting
-- ||| edges and labels to each node.
-- export
-- pairWithNeighbours : Graph e n -> Graph e (n, List (n,e))
-- pairWithNeighbours g =
--   MkGraph $ mapWithKey (\k => map (,neighbourLabels g k)) (graph g)
--
-- ||| Returns the same graph additionaly containing list of connecting
-- ||| labels to each node.
-- export
-- pairWithNeighbours' : Graph e n -> Graph e (n, List n)
-- pairWithNeighbours' g =
--   MkGraph $ mapWithKey (\k => map (,map fst $ neighbourLabels g k)) (graph g)

--------------------------------------------------------------------------------
--          Displaying Graphs
--------------------------------------------------------------------------------

export
{k : _} -> Show e => Show n => Show (IGraph k e n) where
  showPrec p g = showCon p "mkGraph" $ showArg (labNodes g) ++ showArg (edges g)

pl : Nat -> Fin k -> String
pl n = padLeft n ' ' . show . finToNat

export
pretty : {k : _} -> (e -> String) -> (n -> String) -> IGraph k e n -> String
pretty de dn g =
  let ns     := labNodes g
      es     := edges g
      maxLen := length $ show k
   in unlines $
        "Nodes:"   :: map (dispNode maxLen) ns ++
        "\nEdges:" :: map (dispEdge maxLen) es

  where dispNode : Nat -> (Fin k, n) -> String
        dispNode k (n1,l) =
          "  \{pl k n1} :> \{dn l}"

        dispEdge : Nat -> Edge k e -> String
        dispEdge k (E n1 n2 l) =
          "E \{pl k n1} \{pl k n2}  \{de l}"

