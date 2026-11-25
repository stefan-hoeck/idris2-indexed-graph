module Data.Graph.Indexed.Edge

import Data.Array.Index
import Derive.Prelude

%default total
%language ElabReflection

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

export
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

export
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

export
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
record IEdge (k : Nat) (e : Type) where
  constructor IE
  node1 : Fin k
  node2 : Fin k
  label : e
  {auto 0 prf : CompFin node1 node2 === LT}

%runElab derivePattern "IEdge" [I,P] [Show,Eq,Ord]

export
fromNat :
     (x,y : Nat)
  -> {auto 0 p1 : LT x k}
  -> {auto 0 p2 : LT y k}
  -> {auto 0 p3 : LT x y}
  -> (l : e)
  -> IEdge k e
fromNat x y l = IE (natToFinLT x) (natToFinLT y) l @{fromNatLemma x y p1 p2 p3}

export
weakenEdge : IEdge k e -> IEdge (S k) e
weakenEdge (IE x y e @{p}) = IE (weaken x) (weaken y) e @{weakenL x y `trans` p}

export
weakenEdgeN : (0 m : Nat) -> IEdge k e -> IEdge (k + m) e
weakenEdgeN m (IE x y e @{p}) =
  IE (weakenN m x) (weakenN m y) e @{weakenLN m x y `trans` p}

||| Creates an edge between two nodes from different graphs,
||| resulting in a new edge of their composite graph.
|||
||| Note: This assumes that nodes in the first graph (of order `k`)
|||       will stay the same, while nodes in the second graph
|||       (of order `m`) will be increased by `k`.
export
compositeEdge : {k : _} -> Fin k -> Fin m -> (l : e) -> IEdge (k+m) e
compositeEdge x y l =
  fromNat
    (finToNat x)
    (k + finToNat y)
    @{transitive (finLT k x) (lteAddRight _)}
    @{ltPlusLeft $ finLT m y}
    @{transitive (finLT k x) $ lteAddRight _}
    l

export
0 compareGT : (x,y : Fin k) -> CompFin x y === GT -> CompFin y x === LT
compareGT (FS x) FZ     prf = Refl
compareGT (FS x) (FS y) prf = compareGT x y prf
compareGT FZ     FZ prf     impossible
compareGT FZ     (FS x) prf impossible

||| Tries to create an edge from two nodes plus a label.
|||
||| Returns `Nothing` in case the two nodes are identical.
public export
mkEdge : Fin k -> Fin k -> e -> Maybe (IEdge k e)
mkEdge k j l with (compareNat (finToNat k) (finToNat j)) proof prf
  _ | LT = Just (IE k j l )
  _ | EQ = Nothing
  _ | GT = Just (IE j k l @{compareGT k j prf})

||| Tries to create an edge from two natural numbers plus a label.
|||
||| Returns `Nothing` in case the two numbers are not in the correct
||| range or are identical.
export
tryFromNat : {k : _} -> (x,y : Nat) -> (l : e) -> Maybe (IEdge k e)
tryFromNat x y l =
  let Just fx := tryNatToFin x | Nothing => Nothing
      Just fy := tryNatToFin y | Nothing => Nothing
   in mkEdge fx fy l

public export
edge : {k : _} -> Fin k -> e -> IEdge (S k) e
edge x l = IE (weaken x) last l @{edgeLemma k x}

||| Increase both nodes in an edge by the same natural number
export
incEdge : (k : Nat) -> IEdge o e -> IEdge (k+o) e
incEdge k (IE n1 n2 l @{prf}) =
  fromNat
    (k + finToNat n1)
    (k + finToNat n2)
    @{ltPlusLeft $ finLT o n1}
    @{ltPlusLeft $ finLT o n2}
    @{ltPlusLeft $ ltLemma2 _ _ prf}
    l

export
Functor (IEdge k) where
  map f (IE x y l) = IE x y (f l)

export
Foldable (IEdge k) where
  foldl f x (IE _ _ l) = f x l
  foldr f x (IE _ _ l) = f l x
  toList (IE _ _ l)    = [l]
  foldMap f (IE _ _ l) = f l
  null _              = False

export
Traversable (IEdge k) where
  traverse f (IE x y l) = map (\v => IE x y v) (f l)
