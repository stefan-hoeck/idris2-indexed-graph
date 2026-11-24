||| A representation for sparse, simple, undirected
||| labeled graphs, indexed by their order and backed by an
||| immutable array for fast O(1) node lookups.
|||
||| This module provides only the data types plus
||| interface implementations.
module Data.Graph.Indexed.Types

import Data.Array
import Data.AssocList.Indexed
import Data.List
import Derive.Prelude
import public Data.Graph.Indexed.Edge

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Context
--------------------------------------------------------------------------------

||| Adjacency info of a `Node` in a labeled graph.
|||
||| This consists of the node's label plus
||| a list of all its neighboring nodes and
||| the labels of the edges connecting them.
|||
||| This is what is stored in underlying `BitMap`
||| representing the graph.
public export
record Adj k e n where
  constructor A
  label       : n
  neighbours  : AssocList k e

%runElab derivePattern "Adj" [I,P,P] [Show,Eq]

export
weakenAdj : Adj k e n -> Adj (S k) e n
weakenAdj (A l ns) = A l $ weakenAL ns

export
weakenAdjN : (0 m : Nat) -> Adj k e n -> Adj (k + m) e n
weakenAdjN m (A l ns) = A l $ weakenALN m ns

export %inline
fromLabel : n -> Adj k e n
fromLabel v = A v empty

export %inline
Functor (Adj k e) where
  map f = { label $= f }

export
Foldable (Adj k e) where
  foldl f a n  = f a n.label
  foldr f a n  = f n.label a
  foldMap  f n = f n.label
  null _       = False
  toList n     = [n.label]
  foldlM f a n = f a n.label

export %inline
Traversable (Adj k e) where
  traverse f (A n l) = (`A` l) <$> f n

namespace AdjFunctor
  export
  [AdjEdge] Functor (\e => Adj k e n) where
    map f = {neighbours $= map f}

namespace AdjFoldable
  export
  [AdjEdge] Foldable (\e => Adj k e n) where
    foldl f a  = foldl f a . neighbours
    foldr f a  = foldr f a . neighbours
    foldMap  f = foldMap f . neighbours
    null       = null . neighbours
    toList     = toList . neighbours
    foldlM f a = foldlM f a . neighbours

export
Bifunctor (Adj k) where
  bimap  f g (A l es) = A (g l) (map f es)
  mapFst f (A l es)   = A l (map f es)
  mapSnd g (A l es)   = A (g l) es

export
Bifoldable (Adj k) where
  bifoldr f g acc (A l es) = foldr f (g l acc) es
  bifoldl f g acc (A l es) = g (foldl f acc es) l
  binull                 _ = False

export
Bitraversable (Adj k) where
  bitraverse f g (A l es) = [| A (g l) (traverse f es) |]

--------------------------------------------------------------------------------
--          Graph
--------------------------------------------------------------------------------

||| An order-indexed graph.
public export
record Graph (e,n : Type) where
  constructor G
  order : Nat
  graph : IArray order (Adj order e n)

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

namespace GraphFunctor
  export
  [OnEdge] Functor (\e => Graph e n) where
    map f (G o g) = G o $ map {neighbours $= map f} g

namespace GraphFoldable
  export
  [OnEdge] Foldable (\e => Graph e n) where
    foldr f a (G _ g) = foldr (\v,x => foldr f x v.neighbours) a g
    foldl f a (G _ g) = foldl (\x,v => foldl f x v.neighbours) a g
    foldMap f (G _ g) = foldMap (\v => foldMap f v.neighbours) g
    toList    (G _ g) = toList g >>= toList . neighbours
    null      (G _ g) = all (null . neighbours) g

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
-- Indexed Edges
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
toEdge : {0 g : Graph e n} -> LEdg g -> Edge g.order e
toEdge (LE n1 n2 l) = E n1.node n2.node l

export %inline
toLEdg : {0 g : Graph e n} -> Edge g.order e -> LEdg g
toLEdg (E n1 n2 l) = LE (N n1) (N n2) l

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
{0 g : Graph e n} -> Eq e => Eq (LEdg g) where (==) = (==) `on` toEdge

export %inline
{0 g : Graph e n} -> Ord e => Ord (LEdg g) where compare = compare `on` toEdge

export
{0 g : Graph e n} -> Show e => Show (LEdg g) where
  showPrec p (LE n1 n2 l) =
    showCon p "LE" (showArg n1 ++ showArg n2 ++ showArg l)

||| Increase both nodes in an edge by the same natural number
export
incEdge : {0 g : Graph e n} -> (k : Nat) -> LEdg g -> Edge (k + g.order) e
incEdge k (LE n1 n2 l @{prf}) =
  fromNat
    (k + finToNat n1.node)
    (k + finToNat n2.node)
    @{ltPlusLeft $ finLT g.order n1.node}
    @{ltPlusLeft $ finLT g.order n2.node}
    @{ltPlusLeft $ ltLemma2 _ _ prf}
    l
