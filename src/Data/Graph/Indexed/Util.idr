module Data.Graph.Indexed.Util

import Data.Array
import Data.Array.Index
import Data.Array.Mutable
import Data.AssocList.Indexed
import Data.Graph.Indexed.Types
import Data.Linear.Traverse1
import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.String
import Data.Vect

%default total

--------------------------------------------------------------------------------
--          Internal utilities
--------------------------------------------------------------------------------

||| Updates all node labels in a mutable graph.
export %inline
lupdNodes : {k : _} -> MArray s k (Adj k e n) -> (n -> n) -> F1' s
lupdNodes r f = mupdate {label $= f} r

parameters (r : MArray s k (Adj k e n))

  ||| Updates the node label at the given position in a mutable graph.
  export %inline
  lupdNode : (n1 : Fin k) -> (n -> n) -> F1' s
  lupdNode n1 f = modify r n1 {label $= f}

  ||| Sets the node label at the given position in a mutable graph.
  export %inline
  lsetNode : (n1 : Fin k) -> n -> F1' s
  lsetNode n1 v = modify r n1 {label := v}

  ||| Insert a single edge into a mutable array-representation of a graph.
  export
  linsEdge : Edge k e ->F1' s
  linsEdge (E n1 n2 el) t =
    let _ # t := modify r n1 {neighbours $= insert n2 el} t
     in modify r n2 {neighbours $= insert n1 el} t

  ||| Delete a single edge from a mutable array-representation of a graph.
  export
  ldelEdge : (n1, n2 : Fin k) -> F1' s
  ldelEdge n1 n2 t =
    let _ # t := modify r n1 {neighbours $= delete n2} t
     in modify r n2 {neighbours $= delete n1} t

  ||| Insert a bunch of edges into a mutable array-representation of a graph.
  export %inline
  linsEdges : List (Edge k e) -> F1' s
  linsEdges = traverse1_ linsEdge

  ||| Insert a bunch of edges into a mutable array-representation of a graph.
  export %inline
  ldelEdges : List (Fin k, Fin k) -> F1' s
  ldelEdges = traverse1_ (\(x,y) => ldelEdge x y)

-- we return only edges to nodes greater than the node in the
-- context to avoid returning every edge twice in `labEdges`.
ctxtEdgs :
     {0 g : Graph e n}
  -> Fin g.order
  -> Adj g.order e n
  -> SnocList (LEdg g)
ctxtEdgs x (A _ ns) = foldlKV acc [<] ns

  where
    acc : Fin g.order -> SnocList (LEdg g) -> e -> SnocList (LEdg g)
    acc y sp v with (compare x y) proof eq
      _ | LT = sp :< LE (N x) (N y) v
      _ | _  = sp

--------------------------------------------------------------------------------
--          Inspecting Graphs
--------------------------------------------------------------------------------

parameters {g : Graph e n}

  ||| Returns the adjacency (node label plus labeled edges to neighbours)
  ||| of a node in a graph.
  export %inline
  adj : Node g -> Adj g.order e n
  adj = atN g.graph

  ||| Returns the label of a node in graph.
  export %inline
  lab : Node g -> n
  lab = label . adj

  ||| Returns the edges connecting a node as an `AssocList`
  ||| (nodes plus edge labels).
  export %inline
  neighboursAsAL : Node g -> AssocList g.order e
  neighboursAsAL = neighbours . adj

  ||| Returns the edges connecting a node as a list of pairs
  ||| (nodes plus edge labels).
  export %inline
  neighboursAsPairs : Node g -> List (Node g, e)
  neighboursAsPairs = fromAL . neighboursAsAL

  ||| Returns the list of neighbouring nodes of a node in a graph.
  export %inline
  neighbours : Node g -> Nodes g
  neighbours = fromFins . keys . neighboursAsAL

  ||| Returns the list of edges connecting a node.
  export %inline
  edgesTo : Node g -> List (LEdg g)
  edgesTo x = mapMaybe (\(n,l) => mkLEdg x n l) $ neighboursAsPairs x

  ||| Returns the list of neighboring nodes paired with their
  ||| corresponding labels.
  export
  lneighbours : Node g -> List (Node g, n)
  lneighbours = map (\x => (x, lab x)) . neighbours

  ||| Returns the edges connecting a node paired with the
  ||| neighbouring node labels.
  export
  lneighboursAsAL : Node g -> AssocList g.order (e, n)
  lneighboursAsAL = mapKV (\x => (, lab $ N x)) . neighboursAsAL

  ||| Returns the labels of neighbour nodes of a node.
  export
  neighbourLabels : Node g -> List n
  neighbourLabels = map lab . neighbours

  ||| Returns the labels of edges connecting a node.
  export %inline
  edgeLabels : Node g -> List e
  edgeLabels = values . neighbours . adj

  ||| Find the label for an `Edge`.
  export
  elab : (x,y : Node g) -> Maybe e
  elab x y = lookup y.node . neighbours $ adj x

  ||| Find the label for an `Edge`.
  export
  edge : (x,y : Node g) -> Maybe (LEdg g)
  edge x y = elab x y >>= mkLEdg x y

  ||| Tests if the given nodes are adjecent (connected via an edge).
  export
  adjacent : (x,y : Node g) -> Bool
  adjacent x y = isJust $ elab x y

  ||| The degree of the `Node`.
  export
  deg : Node g -> Nat
  deg = length . neighbours

  ||| Checks if there is an undirected edge between two nodes.
  export %inline
  hasNeighbour : (x,y : Node g) -> Bool
  hasNeighbour = adjacent

||| List all 'Node's in the 'Graph'.
export %inline
nodes : (g : Graph e n) -> Nodes g
nodes g = fromFins $ allFinsFast g.order

||| A list of all labeled nodes of a `Graph`
export
labNodes : (g : Graph e n) -> List (Node g, n)
labNodes g = map (\x => (x, lab x)) $ nodes g

||| A list of all labeled nodes of a `Graph`
export %inline
labels : Graph e n -> List n
labels g = map lab $ nodes g

||| A list of all `Edge`s in the `Graph` (in lexicographic order).
export
edges  : (g : Graph e n) -> List (LEdg g)
edges g = foldrKV (\x,adj,es => ctxtEdgs x adj <>> es) [] g.graph

||| The number of edges in the graph.
export %inline
size : Graph e n -> Nat
size g = length $ edges g

--------------------------------------------------------------------------------
--          Making Graphs
--------------------------------------------------------------------------------

||| An empty `Graph`
export
empty : Graph e n
empty = G _ empty

0 mapLen : (f : a -> b) -> (as : List a) -> length (map f as) === length as
mapLen f []        = Refl
mapLen f (x :: xs) = cong S $ mapLen f xs

||| Create a `Graph` from a list of labeled nodes and edges.
export
mkGraphL : (ns : List n) -> List (Edge (length ns) e) -> Graph e n
mkGraphL ns es =
  G _ $ allocListWith ns (`A` empty) $ \r,t =>
    let _ # t := linsEdges r es t
     in unsafeFreeze r t

||| Create a `Graph` from a vect of labeled nodes and edges.
export
mkGraph : {k : _} -> (ns : Vect k n) -> List (Edge k e) -> Graph e n
mkGraph ns es =
  G _ $ allocVect (map (`A` empty) ns) $ \r,t =>
    let _ # t := linsEdges r es t
     in unsafeFreeze r t

||| Create a `Graph` from a vect of labeled nodes and edges.
|||
||| Unlike `mkGraph`, this puts the nodes in the array in reverse order,
||| which is useful when they come from a parser with the last node being
||| at the head of the vector.
export
mkGraphRev : {k : _} -> (ns : Vect k n) -> List (Edge k e) -> Graph e n
mkGraphRev ns es =
 G _ $ allocVectRev (map (`A` empty) ns) $ \r,t =>
   let _ # t := linsEdges r es t
    in unsafeFreeze r t

export %inline
generate : (k : Nat) -> (Fin k -> Adj k e n) -> Graph e n
generate k f = G _ $ generate k f

--------------------------------------------------------------------------------
--          Folds and Traversals
--------------------------------------------------------------------------------

||| Map the adjacencies in a graph accoring to each node's context
export %inline
mapCtxt :
     (g : Graph e n)
  -> (Fin g.order -> Adj g.order e n -> Adj g.order e1 n1)
  -> Graph e1 n1
mapCtxt (G _ g) fun = G _ $ mapWithIndex fun g

||| Map the node labels in a graph accoring to each node's context
export %inline
mapWithCtxt :
     (g : Graph e n)
  -> (Fin g.order -> Adj g.order e n -> n1)
  -> Graph e n1
mapWithCtxt g fun = mapCtxt g (\x,adj => adj $> fun x adj)

||| Map the adjacencies in a graph
export %inline
mapAdj : (g : Graph e n) -> (Adj g.order e n -> Adj g.order f m) -> Graph f m
mapAdj (G _ g) fun = G _ $ map fun g

||| Map the node labels in a graph accoring to each node's adjacency
export %inline
mapWithAdj : (g : Graph e n) -> (Adj g.order e n -> m) -> Graph e m
mapWithAdj g fun = mapAdj g (\adj => adj $> fun adj)

export
traverseCtxt :
     {auto app : Applicative f}
  -> (g : Graph e n)
  -> (Fin g.order -> Adj g.order e n -> f (Adj g.order e1 n1))
  -> f (Graph e1 n1)
traverseCtxt (G _ g) fun = G _ <$> traverseWithIndex fun g

export
traverseWithCtxt :
     {auto app : Applicative f}
  -> (g : Graph e n)
  -> (Fin g.order -> Adj g.order e n -> f n1)
  -> f (Graph e n1)
traverseWithCtxt g fun = traverseCtxt g (\x,a => (`A` a.neighbours) <$> fun x a)

--------------------------------------------------------------------------------
--          Modifying Graphs
--------------------------------------------------------------------------------

||| Uses two functions for updating nodes in a graph:
|||
||| Once is used for the given node, the other for all other nodes.
export
updateNodes : {g : Graph e m} -> Node g -> (f,h : m -> n) -> Graph e n
updateNodes x f h =
  mapWithCtxt g (\y,a => if x.node == y then f a.label else h a.label)

||| Updates a single node in the graph at the given position.
export %inline
updateNode : {g : Graph e n} -> Node g -> (n -> n) -> Graph e n
updateNode x f = updateNodes x f id

||| Replaces a single node in the graph at the given position.
export %inline
setNode : {g : Graph e n} -> Node g -> n -> Graph e n
setNode x = updateNode x . const

||| Uses two functions for updating the edge labels in a graph.
|||
||| Once is used for the edge connecting the two given nodes, the other for
||| all other edges.
export
updateEdges :
     {g   : Graph e n}
  -> (x,y : Node g)
  -> (f,h : e -> e2)
  -> Graph e2 n
updateEdges (N x) (N y) f h =
  mapCtxt g $ \k,(A l a) =>
   A l $
     if      k == x then mapKV (\m,l => if m == y then f l else h l) a
     else if k == y then mapKV (\m,l => if m == x then f l else h l) a
     else    map h a

||| Uses a function for updating a single edge label in a graph.
export %inline
updateEdge : {g : Graph e n} -> (x,y : Node g) -> (f : e -> e) -> Graph e n
updateEdge x y f = updateEdges x y f id

||| Insert (or replace) a single edge in a graph.
export
insEdges : (g : Graph e n) -> List (LEdg g) -> Graph e n
insEdges g es =
  G _ $ allocGen g.order (adj {g} . N) $ \r,t =>
    let _ # t := linsEdges r (map toEdge es) t
     in unsafeFreeze r t

||| Insert an `Edge` into the 'IGraph'.
export %inline
insEdge : (g : Graph e n) -> LEdg g -> Graph e n
insEdge g x = insEdges g [x]

||| Remove multiple 'Edge's from the 'Graph'.
export
delEdges : {g : Graph e n} -> List (Node g, Node g) -> Graph e n
delEdges ps = G _ $ allocGen g.order (adj {g} . N) $ \r,t =>
  let _ # t := ldelEdges r (toFinPairs ps) t
   in unsafeFreeze r t

||| Remove an 'Edge' from the 'Graph'.
export %inline
delEdge : {g : Graph e n} -> (x,y : Node g) -> Graph e n
delEdge x y = delEdges [(x,y)]

||| Insert multiple `LNode`s into the `Graph`.
export
insNodes : {m : _} -> Graph e n -> (ns : Vect m n) -> Graph e n
insNodes (G o g) ns =
  let g' := map (weakenAdjN m) g
   in G (o+m) $ append g' (map fromLabel (array ns))

||| Proof about the order of a graph after inserting `m` nodes.
export
0 insLemma :
     (g : Graph e n)
  -> (ns : Vect m n)
  -> order (insNodes g ns) === (g.order + m)
insLemma (G o g) ns = Refl

||| Insert multiple `LNode`s into the `Graph`.
export
insNodesAndEdges :
     {m : _}
  -> (g  : Graph e n)
  -> (ns : Vect m n)
  -> (es : List (Edge (g.order + m) e))
  -> Graph e n
insNodesAndEdges g ns es =
  insEdges (insNodes g ns) (map toLEdg $ rewrite insLemma g ns in es)

||| Insert a labeled node into the `Graph`.
||| The behavior is undefined if the node is already
||| in the graph.
export %inline
insNode : Graph e n -> n -> Graph e n
insNode g v = insNodes g [v]

export
adjEdges : SortedMap (Fin x) (Fin y) -> Adj x e n -> Adj y e n
adjEdges m (A l ns) =
  let ps := mapMaybe (\(n,v) => (,v) <$> lookup n m) $ pairs ns
   in A l $ fromList ps

zipTR : SnocList (a,b) -> List a -> List b -> List (a,b)
zipTR sx []        _         = sx <>> []
zipTR sx _         []        = sx <>> []
zipTR sx (x :: xs) (y :: ys) = zipTR (sx:<(x,y)) xs ys

export
delNodes : {g : Graph e n} -> Nodes g -> Graph e n
delNodes {g = G 0 g}     _  = G 0 g
delNodes {g = G (S x) g} ks =
  let set       := SortedSet.fromList ks
      A (S y) h :=
        filterWithKey (\x,_ => not (contains (N x) set)) g | A 0 _ => G _ empty
      finX      := filter (\x => not (contains (N x) set)) $ allFinsFast (S x)
      finY      := allFinsFast (S y)
      proMap    := SortedMap.fromList $ zipTR [<] finX finY
   in G (S y) $ map (adjEdges proMap) h

||| Remove a 'Node' from the 'Graph'.
export
delNode : {g : Graph e n} -> Node g -> Graph e n
delNode = delNodes . pure

||| Merge two graphs connecting them via the given list of
||| edges
export
mergeGraphsWithEdges :
     {g1 : Graph e n}
  -> {g2 : Graph e n}
  -> List (Node g1, Node g2, e)
  -> Graph e n
mergeGraphsWithEdges es =
  let vNodes := label <$> toVect g2.graph
      cEdges := map (\(x,y,l) => compositeEdge x.node y.node l) es
      lEdges := incEdge g1.order <$> edges g2
   in insNodesAndEdges g1 vNodes (cEdges ++ lEdges)

||| Merge two graphs that have no bonds between them.
export
mergeGraphs : (g1,g2 : Graph e n) -> Graph e n
mergeGraphs g1 g2 =
  let vNodes := label <$> toVect g2.graph
      lEdges := incEdge g1.order <$> edges g2
   in insNodesAndEdges g1 vNodes lEdges

--------------------------------------------------------------------------------
--          Displaying Graphs
--------------------------------------------------------------------------------

export
Show e => Show n => Show (Graph e n) where
  showPrec p g = showCon p "mkGraph" $ showArg (labels g) ++ showArg (edges g)

pl : Nat -> Node g -> String
pl n = padLeft n ' ' . show

export
pretty : (e -> String) -> (n -> String) -> Graph e n -> String
pretty de dn g =
  let ns     := labNodes g
      es     := edges g
      maxLen := length $ show g.order
   in unlines $
        "Nodes:"   :: map (dispNode maxLen) ns ++
        "\nEdges:" :: map (dispEdge maxLen) es

  where
    dispNode : Nat -> (Node g, n) -> String
    dispNode k (n1,l) =
      "  \{pl k n1} :> \{dn l}"

    dispEdge : Nat -> LEdg g -> String
    dispEdge k (LE n1 n2 l) =
      "E \{pl k n1} \{pl k n2}  \{de l}"
