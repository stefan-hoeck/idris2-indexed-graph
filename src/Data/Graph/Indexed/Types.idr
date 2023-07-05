||| A representation for sparse, simple, undirected
||| labeled graphs, indexed by their order and backed by an
||| immutable array for fast O(1) node lookups.
|||
||| This module provides only the data types plus
||| interface implementations.
module Data.Graph.Indexed.Types

import Data.Array.Indexed
import Data.AssocList.Indexed
import Data.List

%default total

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
  {auto 0 prf : compFin node1 node2 === LT}

0 compFinGT : (x,y : Fin k) -> compFin x y === GT -> compFin y x === LT
compFinGT (FS x) FZ     prf = Refl
compFinGT (FS x) (FS y) prf = compFinGT x y prf
compFinGT FZ     FZ prf     impossible
compFinGT FZ     (FS x) prf impossible

public export
mkEdge : Fin k -> Fin k -> e -> Maybe (Edge k e)
mkEdge k j l with (compFin k j) proof prf
  _ | LT = Just (E k j l)
  _ | EQ = Nothing
  _ | GT = Just (E j k l @{compFinGT k j prf})

public export
Eq e => Eq (Edge k e) where
  E m1 n1 l1 == E m2 n2 l2 = heqFin m1 m2 && heqFin n1 n2 && l1 == l2

export
Show e => Show (Edge k e) where
  showPrec p (E x y l) =
    showCon p "E" $ showArg (finToNat x) ++ showArg (finToNat y) ++ showArg l

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

public export
record Context (k : Nat) (e,n : Type) where
  constructor C
  node       : Fin k
  label      : n
  neighbours : AssocList k e

export %inline
Eq e => Eq n => Eq (Context k e n) where
  C n1 l1 ns1 == C n2 l2 ns2 =
    heqFin n1 n2 && l1 == l2 && ns1 == ns2

export
Show e => Show n => Show (Context k e n) where
  showPrec p (C n l s) =
    showCon p "C" $ showArg (finToNat n) ++ showArg l ++ showArg s

export
Functor (Context k e) where
  map f = { label $= f }

export
Foldable (Context k e) where
  foldl f a n  = f a n.label
  foldr f a n  = f n.label a
  foldMap  f n = f n.label
  null _       = False
  toList n     = [n.label]
  foldlM f a n = f a n.label

namespace ContextFunctor
  export
  [CtxtEdge] Functor (\e => Context k e n) where
    map f = {neighbours $= map f}

namespace ContextFoldable
  export
  [CtxtEdge] Foldable (\e => Context k e n) where
    foldl f a  = foldl f a . neighbours
    foldr f a  = foldr f a . neighbours
    foldMap  f = foldMap f . neighbours
    null       = null . neighbours
    toList     = toList . neighbours
    foldlM f a = foldlM f a . neighbours

export %inline
Traversable (Context k e) where
  traverse f (C n l es) =
    (\l2 => C n l2 es) <$> f l

export
Bifunctor (Context k) where
  bimap  f g (C n l es) = C n (g l) (map f es)
  mapFst f (C n l es)   = C n l (map f es)
  mapSnd g (C n l es)   = C n (g l) es

export
Bifoldable (Context k) where
  bifoldr f g acc (C _ l es) = foldr f (g l acc) es
  bifoldl f g acc (C _ l es) = g (foldl f acc es) l
  binull _                           = False

export
Bitraversable (Context k) where
  bitraverse f g (C n l es) =
    [| C (pure n) (g l) (traverse f es) |]

--------------------------------------------------------------------------------
--          IGraph
--------------------------------------------------------------------------------

||| An order-indexed graph.
public export
record IGraph (k : Nat) (e,n : Type) where
  constructor IG
  graph : IArray k (Adj k e n)

export
{k : _} -> Eq e => Eq n => Eq (IGraph k e n) where
  IG g1 == IG g2 = g1 == g2

export
{k : _} -> Functor (IGraph k e) where
  map f = { graph $= map (map f) }

export
{k : _} -> Foldable (IGraph k e) where
  foldl f a  = foldl (\a',adj => f a' adj.label) a . graph
  foldr f a  = foldr (f . label) a . graph
  foldMap  f = foldMap (f . label) . graph
  toList     = map label . toList . graph
  null _     = k == 0

export
{k : _} -> Traversable (IGraph k e) where
  traverse f (IG g) = IG <$> traverse (traverse f) g

namespace IGraphFunctor
  export
  [OnEdge] {k : _} -> Functor (\e => IGraph k e n) where
    map f g = { graph $= map {neighbours $= map f} } g

namespace IGraphFoldable
  export
  [OnEdge] {k : _} -> Foldable (\e => IGraph k e n) where
    foldr f a = foldr (\v,x => foldr f x v.neighbours) a . graph
    foldl f a = foldl (\x,v => foldl f x v.neighbours) a . graph
    foldMap f = foldMap (\v => foldMap f v.neighbours) . graph
    toList g  = toList g.graph >>= toList . neighbours
    null   g  = all (null . neighbours) g.graph

export
{k : _} -> Bifunctor (IGraph k) where
  bimap  f g (IG m) = IG $ bimap f g <$> m
  mapFst f (IG m)   = IG $ mapFst f <$> m
  mapSnd g (IG m)   = IG $ mapSnd g <$> m

export
{k : _} -> Bifoldable (IGraph k) where
  bifoldr f g acc =
    foldr (flip $ bifoldr f g) acc . graph
  bifoldl f g acc =
    foldl (bifoldl f g) acc . graph
  binull = null

export
{k : _} -> Bitraversable (IGraph k) where
  bitraverse f g (IG h) = IG <$> traverse (bitraverse f g) h

--------------------------------------------------------------------------------
--          Graph
--------------------------------------------------------------------------------

||| A graph together with its order
public export
record Graph (e,n : Type) where
  constructor G
  order : Nat
  graph : IArray order (Adj order e n)

export
Eq e => Eq n => Eq (Graph e n) where
  G s1 g1 == G s2 g2 with (s1 == s2) proof eq
    _ | True  = (rewrite eqOpReflectsEquals s1 s2 eq in g2) == g1
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
  traverse f (G s g) = G s <$> traverse (traverse f) g

namespace GraphFunctor
  export
  [OnEdge] Functor (\e => Graph e n) where
    map f (G o g) = G o $ map {neighbours $= map f} g

namespace GraphFoldable
  export
  [OnEdge] Foldable (\e => Graph e n) where
    foldr f a (G o g) = foldr (\v,x => foldr f x v.neighbours) a g
    foldl f a (G o g) = foldl (\x,v => foldl f x v.neighbours) a g
    foldMap f (G o g) = foldMap (\v => foldMap f v.neighbours) g
    toList    (G o g) = toList g >>= toList . neighbours
    null      (G o g) = all (null . neighbours) g

export
Bifunctor (Graph) where
  bimap  f g (G o m) = G o $ bimap f g <$> m
  mapFst f (G o m)   = G o $ mapFst f <$> m
  mapSnd g (G o m)   = G o $ mapSnd g <$> m

export
Bifoldable (Graph) where
  bifoldr f g acc (G o m) =
    foldr (flip $ bifoldr f g) acc m
  bifoldl f g acc (G o m) =
    foldl (bifoldl f g) acc m
  binull = null

export
Bitraversable Graph where
  bitraverse f g (G s h) = G s <$> traverse (bitraverse f g) h
