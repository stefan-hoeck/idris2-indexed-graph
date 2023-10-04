module Data.Graph.Indexed.Util

import Data.Array.Indexed
import Data.AssocList.Indexed
import Data.Graph.Indexed.Types
import Data.SortedMap
import Data.SortedSet
import Data.List
import Data.String
import Data.Vect

%default total

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

||| A list of all labeled nodes of a `Graph`
export
labNodes  : {k : _} -> IGraph k e n -> List (Fin k, n)
labNodes = foldrKV (\x,(A l _),cs => (x,l) :: cs) [] . graph

||| A list of all labeled nodes of a `Graph`
export
labels  : {k : _} -> IGraph k e n -> List n
labels = foldr (\(A l _) => (l ::)) [] . graph

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

||| Create a `Graph` from a list of labeled nodes and edges.
export
mkGraphL : (ns : List n) -> List (Edge (length ns) e) -> IGraph (length ns) e n
mkGraphL []        _  = empty
mkGraphL ns@(_::_) es =
  IG . unrestricted $ allocList (map (`A` empty) ns) $ \x =>
    let x2 := relength @{mapLen (`A` empty) ns} x in linsEdges es freeze x2

||| Create a `Graph` from a vect of labeled nodes and edges.
export
mkGraph : {k : _} -> (ns : Vect k n) -> List (Edge k e) -> IGraph k e n
mkGraph {k = 0}   []        _  = empty
mkGraph {k = S m} ns@(_::_) es =
  IG . unrestricted $ allocVect (map (`A` empty) ns) $ linsEdges es freeze

||| Create a `Graph` from a vect of labeled nodes and edges.
|||
||| Unlike `mkGraph`, this puts the nodes in the array in reverse order,
||| which is useful when they come from a parser with the last node being
||| at the head of the vector.
export
mkGraphRev : {k : _} -> (ns : Vect k n) -> List (Edge k e) -> IGraph k e n
mkGraphRev {k = 0}   []        _  = empty
mkGraphRev {k = S m} ns@(_::_) es =
  IG . unrestricted $ allocRevVect (map (`A` empty) ns) $ linsEdges es freeze

export %inline
generate : (k : Nat) -> (Fin k -> Adj k e n) -> IGraph k e n
generate k f = IG $ generate k f

--------------------------------------------------------------------------------
--          Folds and Traversals
--------------------------------------------------------------------------------

export
mapCtxt :
     {k : _}
  -> (Fin k -> Adj k e n -> Adj k e1 n1)
  -> IGraph k e n
  -> IGraph k e1 n1
mapCtxt fun (IG g) = IG $ mapWithIndex fun g

export %inline
mapWithCtxt :
     {k : _}
  -> (Fin k -> Adj k e n -> n1)
  -> IGraph k e n
  -> IGraph k e n1
mapWithCtxt fun = mapCtxt (\x,adj => adj $> fun x adj)

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

||| Updates a single node in the graph at the given position.
export
updateNode : {k : _} -> Fin k -> (n -> n) -> IGraph k e n -> IGraph k e n
updateNode x f = mapWithCtxt (\y,a => if x == y then f a.label else a.label)

||| Replaces a single node in the graph at the given position.
export %inline
setNode : {k : _} -> Fin k -> n -> IGraph k e n -> IGraph k e n
setNode x = updateNode x . const

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

||| Insert multiple `LNode`s into the `Graph`.
export
insNodes :
     {k,m : _}
  -> IGraph k e n
  -> (ns : Vect m n)
  -> IGraph (m + k) e n
insNodes (IG g) ns =
  let g'  := map (weakenAdjN m) g
   in rewrite plusCommutative m k in IG $ append g' (map fromLabel (array ns))

||| Insert multiple `LNode`s into the `Graph`.
export
insNodesAndEdges :
     {k,m : _}
  -> IGraph k e n
  -> (ns : Vect m n)
  -> (es : List (Edge (m + k) e))
  -> IGraph (m + k) e n
insNodesAndEdges g ns es = insEdges es $ insNodes g ns

||| Insert a labeled node into the `Graph`.
||| The behavior is undefined if the node is already
||| in the graph.
export %inline
insNode : {k : _} -> IGraph k e n -> n -> IGraph (S k) e n
insNode g v = insNodes g [v]

adjEdges : SortedMap (Fin x) (Fin y) -> Adj x e n -> Adj y e n
adjEdges m (A l ns) =
  let ps := mapMaybe (\(n,v) => (,v) <$> lookup n m) $ pairs ns
   in A l $ fromList ps

export
delNodes : {k : _} -> List (Fin k) -> IGraph k e n -> Graph e n
delNodes {k = 0} _ _ = G _ empty
delNodes {k = S x} ks (IG g) =
  let set       := SortedSet.fromList ks
      A (S y) h :=
        filterWithKey (\x,_ => not (contains x set)) g | A 0 _ => G _ empty
      finX      := filter (\x => not (contains x set)) $ allFinsFast (S x)
      finY      := allFinsFast (S y)
      proMap    := SortedMap.fromList $ zip finX finY
   in G (S y) (IG $ map (adjEdges proMap) h)

||| Remove a 'Node' from the 'Graph'.
export
delNode : {k : _} -> Fin k -> IGraph k e n -> Graph e n
delNode = delNodes . pure

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
