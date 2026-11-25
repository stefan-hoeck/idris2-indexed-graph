module Data.Graph

import Data.SortedMap
import Data.SortedSet
import public Data.Graph.Indexed
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Graph
--------------------------------------------------------------------------------

||| An order-indexed graph.
public export
record Graph (e,n : Type) where
  constructor G
  order : Nat
  graph : IArray order (IAdj order e n)

export %inline
(.igraph) : (g : Graph e n) -> IGraph g.order e n
g.igraph = IG g.graph

export %inline
toGraph : {o : _} -> IGraph o e n -> Graph e n
toGraph g = G o g.graph

export
Eq e => Eq n => Eq (Graph e n) where
  G o1 g1 == G o2 g2 with (o1 == o2) proof eq
    _ | True  = (rewrite eqOpReflectsEquals o1 o2 eq in g2) == g1
    _ | False = False

export
Functor (Graph e) where
  map f (G o g) = G o $ map (map f) g

export
Foldable (Graph e) where
  foldl f a  (G _ g) = foldl (\a',adj => f a' adj.label) a g
  foldr f a  (G _ g) = foldr (f . label) a g
  foldMap  f (G _ g) = foldMap (f . label) g
  toList     (G _ g) = map label $ toList g
  null       (G o g) = o == 0

export
Traversable (Graph e) where
  traverse f (G o g) = G o <$> traverse (traverse f) g

export
Bifunctor Graph where
  bimap  f g (G o m) = G o $ bimap f g <$> m
  mapFst f   (G o m) = G o $ mapFst f <$> m
  mapSnd g   (G o m) = G o $ mapSnd g <$> m

export
Bifoldable Graph where
  bifoldr f g acc (G _ x) = foldr (flip $ bifoldr f g) acc x
  bifoldl f g acc (G _ x) = foldl (bifoldl f g) acc x
  binull          (G _ x) = null x

export
Bitraversable Graph where
  bitraverse f g (G o h) = G o <$> traverse (bitraverse f g) h

--------------------------------------------------------------------------------
-- Indexed Nodes
--------------------------------------------------------------------------------

public export
record Node (g : Graph e n) where
  constructor N
  node : Fin g.order

%runElab deriveIndexed "Node" [Eq,Ord]

export %inline
Show (Node g) where show = show . node

export %inline
Cast (Node g) (Fin g.order) where cast = node

export %inline
Cast (Node g) Nat where cast = finToNat . node

export %inline
Cast (Node g) Integer where cast = cast . finToNat . node

||| A list of nodes in a graph
public export
0 Nodes : Graph e n -> Type
Nodes g = List (Node g)

||| A snoclist of nodes in a graph
public export
0 Sedon : Graph e n -> Type
Sedon g = SnocList (Node g)

export
fromFins : {0 g : Graph e n} -> List (Fin g.order) -> Nodes g
fromFins []        = []
fromFins (x :: xs) = N x :: fromFins xs

export
toFins : Nodes g -> List (Fin g.order)
toFins []          = []
toFins (N x :: xs) = x :: toFins xs

export
toFinPairs : List (Node g,Node g) -> List (Fin g.order, Fin g.order)
toFinPairs []                = []
toFinPairs ((N x,N y) :: xs) = (x,y) :: toFinPairs xs

export
fromPairs : {0 g : Graph e n} -> List (Fin g.order,a) -> List (Node g,a)
fromPairs []            = []
fromPairs ((x,l) :: xs) = (N x,l) :: fromPairs xs

export
fromAL : {0 g : Graph e n} -> AssocList g.order e -> List (Node g,e)
fromAL al = fromPairs $ pairs al

export %inline
alNodes : {0 g : Graph e n} -> AssocList g.order e -> List (Node g)
alNodes al = fromFins $ keys al

export %inline
atN : IArray g.order a -> Node g -> a
atN arr (N x) = at arr x

export
tryNode : {g : _} -> Nat -> Maybe (Node g)
tryNode n = map N $ tryNatToFin n

--------------------------------------------------------------------------------
-- Edges
--------------------------------------------------------------------------------

public export
record Edg (g : Graph e n) where
  constructor EG
  node1 : Node g
  node2 : Node g
  {auto 0 prf : CompFin node1.node node2.node === LT}

%runElab deriveIndexed "Edg" [Show,Eq,Ord]

public export
record LEdg (g : Graph e n) where
  constructor LE
  node1 : Node g
  node2 : Node g
  label : e
  {auto 0 prf : CompFin node1.node node2.node === LT}

export %inline
toIEdge : {0 g : Graph e n} -> LEdg g -> IEdge g.order e
toIEdge (LE n1 n2 l) = IE n1.node n2.node l

export %inline
toLEdg : {0 g : Graph e n} -> IEdge g.order e -> LEdg g
toLEdg (IE n1 n2 l) = LE (N n1) (N n2) l

export %inline
toEdg : {0 g : _} -> LEdg g -> Edg g
toEdg (LE n1 n2 _) = EG n1 n2

export
mkLEdg : {0 g : Graph e n} -> Node g -> Node g -> e -> Maybe (LEdg g)
mkLEdg x y l  with (compareNat (finToNat x.node) (finToNat y.node)) proof prf
  _ | LT = Just (LE x y l )
  _ | EQ = Nothing
  _ | GT = Just (LE y x l @{compareGT x.node y.node prf})

export
mkEdg : {0 g : _} -> Node g -> Node g -> Maybe (Edg g)
mkEdg x y with (compareNat (finToNat x.node) (finToNat y.node)) proof prf
  _ | LT = Just (EG x y)
  _ | EQ = Nothing
  _ | GT = Just (EG y x @{compareGT x.node y.node prf})

export %inline
{0 g : Graph e n} -> Eq e => Eq (LEdg g) where (==) = (==) `on` toIEdge

export %inline
{0 g : Graph e n} -> Ord e => Ord (LEdg g) where compare = compare `on` toIEdge

export
{0 g : Graph e n} -> Show e => Show (LEdg g) where
  showPrec p (LE n1 n2 l) =
    showCon p "LE" (showArg n1 ++ showArg n2 ++ showArg l)

--------------------------------------------------------------------------------
-- Adjacency
--------------------------------------------------------------------------------

public export
record Adj (g : Graph e n) where
  constructor A
  label      : n
  neighbours : List (Node g, e)

export %inline
toAdj : {0 g : Graph e n} -> IAdj g.order e n -> Adj g
toAdj (IA l ns) = A l (fromAL ns)

--------------------------------------------------------------------------------
--          Inspecting Graphs
--------------------------------------------------------------------------------

parameters {g : Graph e n}

  ||| Returns the adjacency (node label plus labeled edges to neighbours)
  ||| of a node in a graph.
  export %inline
  gadj : Node g -> IAdj g.order e n
  gadj = atN g.graph

  ||| Returns the adjacency (node label plus labeled edges to neighbours)
  ||| of a node in a graph.
  export %inline
  adj : Node g -> Adj g
  adj = toAdj . gadj

  ||| Returns the label of a node in graph.
  export %inline
  lab : Node g -> n
  lab = label . gadj

  ||| Returns the edges connecting a node as an `AssocList`
  ||| (nodes plus edge labels).
  export %inline
  neighboursAsAL : Node g -> AssocList g.order e
  neighboursAsAL = neighbours . gadj

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
  edgeLabels = map snd . neighboursAsPairs

  ||| Find the label for an `Edge`.
  export
  elab : (x,y : Node g) -> Maybe e
  elab x y = lookup y.node . neighbours $ gadj x

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
edges g = map toLEdg (iedges $ IG g.graph)

||| The number of edges in the graph.
export %inline
size : Graph e n -> Nat
size g = isize (IG g.graph)

--------------------------------------------------------------------------------
--          Making Graphs
--------------------------------------------------------------------------------

||| An empty `Graph`
export
empty : Graph e n
empty = G _ empty

||| Create a `Graph` from a list of labeled nodes and edges.
export
mkGraphL : List n -> List (Nat,Nat,e) -> Graph e n
mkGraphL ns es = G _ $ graph $ mkIGraphL ns es

||| Create a `Graph` from a vect of labeled nodes and edges.
export
mkGraph : {k : _} -> (ns : Vect k n) -> List (IEdge k e) -> Graph e n
mkGraph ns es = G _ $ graph $ mkIGraph ns es

||| Create a `Graph` from a vect of labeled nodes and edges.
|||
||| Unlike `mkGraph`, this puts the nodes in the array in reverse order,
||| which is useful when they come from a parser with the last node being
||| at the head of the vector.
export
mkGraphRev : {k : _} -> (ns : Vect k n) -> List (IEdge k e) -> Graph e n
mkGraphRev ns es = G _ $ graph $ mkIGraphRev ns es

--------------------------------------------------------------------------------
--          Folds and Traversals
--------------------------------------------------------------------------------

||| Map the adjacencies in a graph accoring to each node's context
export %inline
mapCtxt :
     (g : Graph e n)
  -> (Node g -> Adj g -> IAdj g.order e1 n1)
  -> Graph e1 n1
mapCtxt (G _ g) fun = G _ $ mapWithIndex (\x,a => fun (N x) (toAdj a)) g

||| Map the node labels in a graph accoring to each node's context
export %inline
mapWithCtxt : (g : Graph e n) -> (Node g -> Adj g -> n1) -> Graph e n1
mapWithCtxt (G _ g) fun =
  G _ $ mapWithIndex (\x,a => a $> fun (N x) (toAdj a)) g

||| Map the adjacencies in a graph
export %inline
mapAdj : (g : Graph e n) -> (Adj g -> IAdj g.order f m) -> Graph f m
mapAdj (G _ g) fun = G _ $ map (fun . toAdj) g

||| Map the node labels in a graph accoring to each node's adjacency
export %inline
mapWithAdj : (g : Graph e n) -> (Adj g -> m) -> Graph e m
mapWithAdj (G _ g) fun = G _ $ map (\a => a $> fun (toAdj a)) g

export
traverseCtxt :
     {auto app : Applicative f}
  -> (g : Graph e n)
  -> (Node g -> Adj g -> f (IAdj g.order e1 n1))
  -> f (Graph e1 n1)
traverseCtxt (G _ g) fun =
  toGraph <$> itraverseCtxt (IG g) (\x,a => fun (N x) (toAdj a))

export
traverseWithCtxt :
     {auto app : Applicative f}
  -> (g : Graph e n)
  -> (Node g -> Adj g -> f n1)
  -> f (Graph e n1)
traverseWithCtxt (G _ g) fun =
  toGraph <$> itraverseWithCtxt (IG g) (\x => fun (N x) . toAdj)

adjEdges : SortedMap (Fin x) (Fin y) -> IAdj x e n -> IAdj y e n
adjEdges m (IA l ns) =
  let ps := mapMaybe (\(n,v) => (,v) <$> lookup n m) $ pairs ns
   in IA l $ fromList ps

zipTR : SnocList (a,b) -> List a -> List b -> List (a,b)
zipTR sx []        _         = sx <>> []
zipTR sx _         []        = sx <>> []
zipTR sx (x :: xs) (y :: ys) = zipTR (sx:<(x,y)) xs ys

export
delNodes : {g : Graph e n} -> Nodes g -> Graph e n
delNodes {g = G 0 g}     _  = G 0 g
delNodes {g = G (S x) g} ns =
  let fs        := toFins ns
      set       := SortedSet.fromList fs
      A (S y) h :=
        filterWithKey (\x,_ => not (contains x set)) g | A 0 _ => G _ empty
      finX      := filter (\x => not (contains x set)) $ allFinsFast (S x)
      finY      := allFinsFast (S y)
      proMap    := SortedMap.fromList $ zipTR [<] finX finY
   in G (S y) $ map (adjEdges proMap) h

||| Remove a 'Node' from the 'Graph'.
export
delNode : {g : Graph e n} -> Node g -> Graph e n
delNode = delNodes . pure

--------------------------------------------------------------------------------
--          Displaying Graphs
--------------------------------------------------------------------------------

export
Show e => Show n => Show (Graph e n) where
  showPrec p g = showCon p "mkGraph" $ showArg (labels g) ++ showArg (edges g)

export
pretty : (e -> String) -> (n -> String) -> Graph e n -> String
pretty de dn g = ipretty de dn g.igraph
