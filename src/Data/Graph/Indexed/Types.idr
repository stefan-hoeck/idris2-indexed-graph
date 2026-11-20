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

%default total

--------------------------------------------------------------------------------
--          Lemmata
--------------------------------------------------------------------------------

public export
0 CompFin : Fin k -> Fin k -> Ordering
CompFin x y = compareNat (finToNat x) (finToNat y)

0 weakenL : (x,y : Fin k) -> CompFin (weaken x) (weaken y) === CompFin x y
weakenL FZ FZ         = Refl
weakenL FZ (FS x)     = Refl
weakenL (FS x) FZ     = Refl
weakenL (FS x) (FS y) = weakenL x y

0 weakenLN :
     (m : Nat)
  -> (x,y : Fin k)
  -> CompFin (weakenN m x) (weakenN m y) === CompFin x y
weakenLN m FZ FZ         = Refl
weakenLN m FZ (FS x)     = Refl
weakenLN m (FS x) FZ     = Refl
weakenLN m (FS x) (FS y) = weakenLN m x y

0 finLT : (k : Nat) -> (x : Fin k) -> LT (finToNat x) k
finLT (S k) FZ     = LTESucc LTEZero
finLT (S k) (FS x) = LTESucc $ finLT k x
finLT Z x impossible

0 weakenToNatL : (x : Fin k) -> finToNat x === finToNat (weaken x)
weakenToNatL FZ     = Refl
weakenToNatL (FS x) = cong S $ weakenToNatL x

0 lastLemma : (n : Nat) -> n === finToNat (last {n})
lastLemma 0     = Refl
lastLemma (S k) = cong S (lastLemma k)

0 ltLemma : (m,n : Nat) -> LT m n -> compareNat m n === LT
ltLemma 0     (S j) x           = Refl
ltLemma (S k) (S j) (LTESucc x) = ltLemma k j x
ltLemma (S k) Z x impossible
ltLemma Z Z x impossible

0 ltLemma2 : (m,n : Nat) -> compareNat m n === LT -> LT m n
ltLemma2 Z     Z     prf impossible
ltLemma2 (S x) Z     prf impossible
ltLemma2 0     (S y) prf = LTESucc LTEZero
ltLemma2 (S x) (S y) prf = LTESucc $ ltLemma2 x y prf

0 edgeLemma :
     (n : Nat)
  -> (x : Fin n)
  -> CompFin (weaken x) (Fin.last {n}) === LT
edgeLemma n x =
  let p1 := rewrite (sym $ lastLemma n) in finLT n x
      p2 := replace {p = \y => LT y (finToNat (last {n}))} (weakenToNatL x) p1
   in ltLemma _ _ p2

0 fromNatLemma :
     (x,y : Nat)
  -> (p1 : LT x k)
  -> (p2 : LT y k)
  -> (p3 : LT x y)
  -> CompFin (natToFinLT {n = k} x) (natToFinLT {n = k} y) === LT
fromNatLemma _ 0 _ _ p3 = absurd p3
fromNatLemma 0     (S j) (LTESucc x) (LTESucc y) _           = Refl
fromNatLemma (S i) (S j) (LTESucc x) (LTESucc y) (LTESucc z) =
  fromNatLemma i j x y z

0 ltPlusRight : LT k m -> LT (k + n) (m + n)
ltPlusRight {k = S x} {m = S y} (LTESucc p) = LTESucc $ ltPlusRight p
ltPlusRight {k = _}   {m = 0}   p           = absurd p
ltPlusRight {k = 0}   {m = S y} p           =
  rewrite plusCommutative y n in LTESucc (lteAddRight n)

0 ltPlusLeft : LT k m -> LT (n + k) (n + m)
ltPlusLeft x =
  rewrite plusCommutative n k in
  rewrite plusCommutative n m in ltPlusRight x

0 lteAddLeft : (n : Nat) -> LTE n (m + n)
lteAddLeft n = rewrite plusCommutative m n in lteAddRight n

--------------------------------------------------------------------------------
--          Edges
--------------------------------------------------------------------------------

||| A labeled edge in a simple, undirected graph.
||| Since edges go in both directions and loops are not allowed,
||| we can enforce without loss of generality
||| that `node2 > node1 = True`.
public export
record Edge (k : Nat) (e : Type) where
  constructor E
  node1 : Fin k
  node2 : Fin k
  label : e
  {auto 0 prf : CompFin node1 node2 === LT}

export
fromNat :
     (x,y : Nat)
  -> {auto 0 p1 : LT x k}
  -> {auto 0 p2 : LT y k}
  -> {auto 0 p3 : LT x y}
  -> (l : e)
  -> Edge k e
fromNat x y l = E (natToFinLT x) (natToFinLT y) l @{fromNatLemma x y p1 p2 p3}

export
weakenEdge : Edge k e -> Edge (S k) e
weakenEdge (E x y e @{p}) = E (weaken x) (weaken y) e @{weakenL x y `trans` p}

export
weakenEdgeN : (0 m : Nat) -> Edge k e -> Edge (k + m) e
weakenEdgeN m (E x y e @{p}) =
  E (weakenN m x) (weakenN m y) e @{weakenLN m x y `trans` p}

||| Increase both nodes in an edge by the same natural number
export
incEdge : (k : Nat) -> Edge m e -> Edge (k + m) e
incEdge k (E n1 n2 l @{prf}) =
  fromNat
    (k + finToNat n1)
    (k + finToNat n2)
    @{ltPlusLeft $ finLT m n1}
    @{ltPlusLeft $ finLT m n2}
    @{ltPlusLeft $ ltLemma2 _ _ prf}
    l

||| Creates an edge between two nodes from different graphs,
||| resulting in a new edge of their composite graph.
|||
||| Note: This assumes that nodes in the first graph (of order `k`)
|||       will stay the same, while nodes in the second graph
|||       (of order `m`) will be increased by `k`.
export
compositeEdge : {k : _} -> Fin k -> Fin m -> (l : e) -> Edge (k+m) e
compositeEdge x y l =
  fromNat
    (finToNat x)
    (k + finToNat y)
    @{transitive (finLT k x) (lteAddRight _)}
    @{ltPlusLeft $ finLT m y}
    @{transitive (finLT k x) $ lteAddRight _}
    l

0 compareGT : (x,y : Fin k) -> CompFin x y === GT -> CompFin y x === LT
compareGT (FS x) FZ     prf = Refl
compareGT (FS x) (FS y) prf = compareGT x y prf
compareGT FZ     FZ prf     impossible
compareGT FZ     (FS x) prf impossible

||| Tries to create an edge from two nodes plus a label.
|||
||| Returns `Nothing` in case the two nodes are identical.
public export
mkEdge : Fin k -> Fin k -> e -> Maybe (Edge k e)
mkEdge k j l with (compareNat (finToNat k) (finToNat j)) proof prf
  _ | LT = Just (E k j l )
  _ | EQ = Nothing
  _ | GT = Just (E j k l @{compareGT k j prf})

||| Tries to create an edge from two natural numbers plus a label.
|||
||| Returns `Nothing` in case the two numbers are not in the correct
||| range or are identical.
export
tryFromNat : {k : _} -> (x,y : Nat) -> (l : e) -> Maybe (Edge k e)
tryFromNat x y l =
  let Just fx := tryNatToFin x | Nothing => Nothing
      Just fy := tryNatToFin y | Nothing => Nothing
   in mkEdge fx fy l

public export
edge : {k : _} -> Fin k -> e -> Edge (S k) e
edge x l = E (weaken x) last l @{edgeLemma k x}

public export
Eq e => Eq (Edge k e) where
  E m1 n1 l1 == E m2 n2 l2 = m1 == m2 && n1 == n2 && l1 == l2

public export
Ord e => Ord (Edge k e) where
  compare (E m1 n1 l1) (E m2 n2 l2) =
    let EQ := compare m1 m2 | r => r
        EQ := compare n1 n2 | r => r
     in compare l1 l2

export
Show e => Show (Edge k e) where
  showPrec p (E x y l) =
    showCon p "E" $ showArg (finToNat x) ++ showArg (finToNat y) ++ showArg l

export
Functor (Edge k) where
  map f (E x y l) = E x y (f l)

export
Foldable (Edge k) where
  foldl f x (E _ _ l) = f x l
  foldr f x (E _ _ l) = f l x
  toList (E _ _ l)    = [l]
  foldMap f (E _ _ l) = f l
  null _              = False

export
Traversable (Edge k) where
  traverse f (E x y l) = map (\v => E x y v) (f l)
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

export
weakenAdj : Adj k e n -> Adj (S k) e n
weakenAdj (A l ns) = A l $ weakenAL ns

export
weakenAdjN : (0 m : Nat) -> Adj k e n -> Adj (k + m) e n
weakenAdjN m (A l ns) = A l $ weakenALN m ns

export %inline
fromLabel : n -> Adj k e n
fromLabel v = A v empty

export
Eq e => Eq n => Eq (Adj k e n) where
  A l1 ns1 == A l2 ns2 = l1 == l2 && ns1 == ns2

export
Show e => Show n => Show (Adj k e n) where
  showPrec p (A lbl ns) = showCon p "A" $ showArg lbl ++ showArg ns

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

export %inline
Eq (Node g) where N x == N y = x == y

export %inline
Ord (Node g) where compare (N x) (N y) = compare x y

export %inline
Show (Node g) where show = show . finToNat . node

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
atN : IArray g.order a -> Node g -> a
atN arr (N x) = at arr x
