module Data.Graph.Indexed.Util

import Data.Array
import Data.Array.Mutable
import Data.AssocList.Indexed
import Data.Linear.Traverse1
import Data.Graph.Indexed.Types
import Data.SortedMap
import Data.SortedSet
import Data.List
import Data.String
import Data.Vect

%default total

||| Generates the list of all `Fin n` in linear type.
|||
||| This is a lot faster than `Data.Fin.allFins`, which runs in quadratic
||| time.
export
allFinsFast : (n : Nat) -> List (Fin n)
allFinsFast 0 = []
allFinsFast (S n) = go [] last
  where
    go : List (Fin $ S n) -> Fin (S n) -> List (Fin $ S n)
    go xs FZ     = FZ :: xs
    go xs (FS x) = go (FS x :: xs) (assert_smaller (FS x) $ weaken x)

--------------------------------------------------------------------------------
--          Internal utilities
--------------------------------------------------------------------------------

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
ctxtEdges : Fin k -> Adj k e n -> SnocList (Edge k e)
ctxtEdges x (A _ ns) = foldlKV acc [<] ns

  where
    acc : Fin k -> SnocList (Edge k e) -> e -> SnocList (Edge k e)
    acc y sp v with (compare x y) proof eq
      _ | LT = sp :< E x y v
      _ | _  = sp

--------------------------------------------------------------------------------
--          Inspecting Graphs
--------------------------------------------------------------------------------

||| A list of contexts of a graph
export
contexts : {k : _} -> IGraph k e n -> List (Context k e n)
contexts = foldrKV (\x,(A l ns),cs => C x l ns :: cs) [] . graph

||| List all 'Node's in the 'Graph'.
export %inline
nodes : {k : _} -> (0 _ : IGraph k e n) -> List (Fin k)
nodes _ = allFinsFast k

||| A list of all labeled nodes of a `Graph`
export
labNodes  : {k : _} -> IGraph k e n -> List (Fin k, n)
labNodes = foldrKV (\x,(A l _),cs => (x,l) :: cs) [] . graph

||| A list of all labeled nodes of a `Graph`
export
labels  : {k : _} -> IGraph k e n -> List n
labels = foldr (\(A l _) => (l ::)) [] . graph

||| Returns the adjacency (node label plus labeled edges to neighbours)
||| of a node in a graph.
export %inline
adj : IGraph k e n -> Fin k -> Adj k e n
adj (IG g) k = at g k

||| Returns the label of a node in graph.
export %inline
lab : IGraph k e n -> Fin k -> n
lab g = label . adj g

||| Returns the edges connecting a node as an `AssocList`
||| (nodes plus edge labels).
export %inline
neighboursAsAL : IGraph k e n -> Fin k -> AssocList k e
neighboursAsAL g = neighbours . adj g

||| Returns the edges connecting a node as a list of pairs
||| (nodes plus edge labels).
export %inline
neighboursAsPairs : IGraph k e n -> Fin k -> List (Fin k, e)
neighboursAsPairs g = pairs . neighboursAsAL g

||| Returns the list of neighbouring nodes of a node in a graph.
export %inline
neighbours : IGraph k e n -> Fin k -> List (Fin k)
neighbours g = keys . neighboursAsAL g

||| Returns the list of edges connecting a node.
export %inline
edgesTo : IGraph k e n -> Fin k -> List (Edge k e)
edgesTo g k =
  let A _ ns := adj g k
   in mapMaybe (\(n,l) => mkEdge k n l) $ pairs ns

||| Returns the list of neighboring nodes paired with their
||| corresponding labels.
export
lneighbours : IGraph k e n -> Fin k -> List (Fin k, n)
lneighbours g = map (\x => (x, lab g x)) . neighbours g

||| Returns the edges connecting a node paired with the
||| neighbouring node labels.
export
lneighboursAsAL : IGraph k e n -> Fin k -> AssocList k (e, n)
lneighboursAsAL g = mapKV (\x => (, lab g x)) . neighboursAsAL g

||| Returns the labels of neighbour nodes of a node.
export
neighbourLabels : IGraph k e n -> Fin k -> List n
neighbourLabels g = map (lab g) . neighbours g

||| Returns the labels of edges connecting a node.
export %inline
edgeLabels : IGraph k e n -> Fin k -> List e
edgeLabels g = values . neighbours . adj g

||| Find the label for an `Edge`.
export
elab : IGraph k e n -> Fin k -> Fin k -> Maybe e
elab (IG g) x y = lookup y . neighbours $ at g x

||| Tests if the given nodes are adjecent (connected via an edge).
export
adjacent : IGraph k e n -> Fin k -> Fin k -> Bool
adjacent g x y = isJust $ elab g x y

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

||| Create a `Graph` from a list of labeled nodes and edges.
export
mkGraphL : (ns : List n) -> List (Edge (length ns) e) -> IGraph (length ns) e n
mkGraphL ns es =
  IG $ allocListWith ns (`A` empty) $ \r,t =>
    let _ # t := linsEdges r es t
     in unsafeFreeze r t

||| Create a `Graph` from a vect of labeled nodes and edges.
export
mkGraph : {k : _} -> (ns : Vect k n) -> List (Edge k e) -> IGraph k e n
mkGraph ns es =
  IG $ allocVect (map (`A` empty) ns) $ \r,t =>
    let _ # t := linsEdges r es t
     in unsafeFreeze r t

||| Create a `Graph` from a vect of labeled nodes and edges.
|||
||| Unlike `mkGraph`, this puts the nodes in the array in reverse order,
||| which is useful when they come from a parser with the last node being
||| at the head of the vector.
export
mkGraphRev : {k : _} -> (ns : Vect k n) -> List (Edge k e) -> IGraph k e n
mkGraphRev ns es =
 IG $ allocVectRev (map (`A` empty) ns) $ \r,t =>
   let _ # t := linsEdges r es t
    in unsafeFreeze r t

export %inline
generate : (k : Nat) -> (Fin k -> Adj k e n) -> IGraph k e n
generate k f = IG $ generate k f

--------------------------------------------------------------------------------
--          Folds and Traversals
--------------------------------------------------------------------------------

||| Map the adjacencies in a graph accoring to each node's context
export %inline
mapCtxt :
     {k : _}
  -> (Fin k -> Adj k e n -> Adj k e1 n1)
  -> IGraph k e n
  -> IGraph k e1 n1
mapCtxt fun (IG g) = IG $ mapWithIndex fun g

||| Map the node labels in a graph accoring to each node's context
export %inline
mapWithCtxt :
     {k : _}
  -> (Fin k -> Adj k e n -> n1)
  -> IGraph k e n
  -> IGraph k e n1
mapWithCtxt fun = mapCtxt (\x,adj => adj $> fun x adj)

||| Map the adjacencies in a graph
export %inline
mapAdj : {k : _} -> (Adj k e n -> Adj k f m) -> IGraph k e n -> IGraph k f m
mapAdj fun (IG g) = IG $ map fun g

||| Map the node labels in a graph accoring to each node's adjacency
export %inline
mapWithAdj : {k : _} -> (Adj k e n -> m) -> IGraph k e n -> IGraph k e m
mapWithAdj fun = mapAdj (\adj => adj $> fun adj)

export
traverseCtxt :
     {k : _}
  -> {auto app : Applicative f}
  -> (Fin k -> Adj k e n -> f (Adj k e1 n1))
  -> IGraph k e n
  -> f (IGraph k e1 n1)
traverseCtxt fun (IG g) = IG <$> traverseWithIndex fun g

export
traverseWithCtxt :
     {k : _}
  -> {auto app : Applicative f}
  -> (Fin k -> Adj k e n -> f n1)
  -> IGraph k e n
  -> f (IGraph k e n1)
traverseWithCtxt fun = traverseCtxt (\x,a => (`A` a.neighbours) <$> fun x a)

--------------------------------------------------------------------------------
--          Modifying Graphs
--------------------------------------------------------------------------------

||| Uses two functions for updating nodes in a graph:
|||
||| Once is used for the given node, the other for all other nodes.
export
updateNodes : {k : _} -> Fin k -> (f,g : m -> n) -> IGraph k e m -> IGraph k e n
updateNodes x f g = mapWithCtxt (\y,a => if x == y then f a.label else g a.label)

||| Updates a single node in the graph at the given position.
export %inline
updateNode : {k : _} -> Fin k -> (n -> n) -> IGraph k e n -> IGraph k e n
updateNode x f = updateNodes x f id

||| Replaces a single node in the graph at the given position.
export %inline
setNode : {k : _} -> Fin k -> n -> IGraph k e n -> IGraph k e n
setNode x = updateNode x . const

||| Uses two functions for updating the edge labels in a graph.
|||
||| Once is used for the edge connecting the two given nodes, the other for
||| all other edges.
export
updateEdges :
     {k : _}
  -> (x,y : Fin k)
  -> (f,g : e -> e2)
  -> IGraph k e n
  -> IGraph k e2 n
updateEdges x y f g =
  mapCtxt $ \k,(A l a) =>
   A l $
     if      k == x then mapKV (\m,l => if m == y then f l else g l) a
     else if k == y then mapKV (\m,l => if m == x then f l else g l) a
     else    map g a

||| Uses a function for updating a single edge label in a graph.
export %inline
updateEdge :
     {k : _}
  -> (x,y : Fin k)
  -> (f : e -> e)
  -> IGraph k e n
  -> IGraph k e n
updateEdge x y f = updateEdges x y f id

||| Insert (or replace) a single edge in a graph.
export
insEdges : {k : _} -> List (Edge k e) -> IGraph k e n -> IGraph k e n
insEdges es g =
  IG $ allocGen k (adj g) $ \r,t =>
    let _ # t := linsEdges r es t
     in unsafeFreeze r t

||| Insert an `Edge` into the 'IGraph'.
export %inline
insEdge : {k : _} -> Edge k e -> IGraph k e n -> IGraph k e n
insEdge = insEdges . pure

||| Remove multiple 'Edge's from the 'Graph'.
export
delEdges : {k : _} -> List (Fin k, Fin k) -> IGraph k e n -> IGraph k e n
delEdges ps g = IG $ allocGen k (adj g) $ \r,t =>
  let _ # t := ldelEdges r ps t
   in unsafeFreeze r t

||| Remove an 'Edge' from the 'Graph'.
export %inline
delEdge : {k : _} -> (x,y : Fin k) -> IGraph k e n -> IGraph k e n
delEdge x y = delEdges [(x,y)]

||| Insert multiple `LNode`s into the `Graph`.
export
insNodes : {k,m : _} -> IGraph k e n -> (ns : Vect m n) -> IGraph (k + m) e n
insNodes (IG g) ns =
  let g'  := map (weakenAdjN m) g
   in IG $ append g' (map fromLabel (array ns))

||| Insert multiple `LNode`s into the `Graph`.
export
insNodesAndEdges :
     {k,m : _}
  -> IGraph k e n
  -> (ns : Vect m n)
  -> (es : List (Edge (k + m) e))
  -> IGraph (k + m) e n
insNodesAndEdges g ns es = insEdges es $ insNodes g ns

||| Insert a labeled node into the `Graph`.
||| The behavior is undefined if the node is already
||| in the graph.
export %inline
insNode : {k : _} -> IGraph k e n -> n -> IGraph (S k) e n
insNode g v = rewrite plusCommutative 1 k in insNodes g [v]

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
delNodes : {k : _} -> List (Fin k) -> IGraph k e n -> Graph e n
delNodes {k = 0} _ _ = G _ empty
delNodes {k = S x} ks (IG g) =
  let set       := SortedSet.fromList ks
      A (S y) h :=
        filterWithKey (\x,_ => not (contains x set)) g | A 0 _ => G _ empty
      finX      := filter (\x => not (contains x set)) $ allFinsFast (S x)
      finY      := allFinsFast (S y)
      proMap    := SortedMap.fromList $ zipTR [<] finX finY
   in G (S y) (IG $ map (adjEdges proMap) h)

||| Remove a 'Node' from the 'Graph'.
export
delNode : {k : _} -> Fin k -> IGraph k e n -> Graph e n
delNode = delNodes . pure

||| Merge two graphs connecting them via the given list of
||| edges
export
mergeGraphsWithEdges :
     {k,m : _}
  -> (g1 : IGraph k e n)
  -> (g2 : IGraph m e n)
  -> List (Fin k, Fin m, e)
  -> IGraph (k + m) e n
mergeGraphsWithEdges {k} g t es =
  let vNodes := label <$> toVect t.graph
      cEdges := map (\(x,y,l) => compositeEdge x y l) es
      lEdges := incEdge k <$> edges t
   in insNodesAndEdges g vNodes (cEdges ++ lEdges)

||| Merge two graphs that have no bonds between them.
export
mergeGraphs :
     {k,m : _}
  -> (g1 : IGraph k e n)
  -> (g2 : IGraph m e n)
  -> IGraph (k + m) e n
mergeGraphs {k} g t =
  let vNodes := label <$> toVect t.graph
      lEdges := incEdge k <$> edges t
   in insNodesAndEdges g vNodes lEdges

--------------------------------------------------------------------------------
--          Displaying Graphs
--------------------------------------------------------------------------------

export
{k : _} -> Show e => Show n => Show (IGraph k e n) where
  showPrec p g = showCon p "mkGraph" $ showArg (labels g) ++ showArg (edges g)

export
Show e => Show n => Show (Graph e n) where
  showPrec p (G o g) = showCon p "G" $ showArg o ++ showArg g

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

  where
    dispNode : Nat -> (Fin k, n) -> String
    dispNode k (n1,l) =
      "  \{pl k n1} :> \{dn l}"

    dispEdge : Nat -> Edge k e -> String
    dispEdge k (E n1 n2 l) =
      "E \{pl k n1} \{pl k n2}  \{de l}"
