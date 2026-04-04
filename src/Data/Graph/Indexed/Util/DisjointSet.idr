module Data.Graph.Indexed.Util.DisjointSet

import Data.Array
import Data.SortedMap
import Data.Linear.Token
import Syntax.T1

%default total

data DSNode : Nat -> Type where
  R : (size   : Nat) -> DSNode k -- root of set
  N : (parent : Fin k) -> DSNode k -- child node of set

||| A simple [disjoint set](https://en.wikipedia.org/wiki/Disjoint-set_data_structure)
||| implementation.
|||
||| This allows us to efficiently partition the values from 0 to `k-1`
||| into disjoint sets. Operations like `root`, `size`, and `union`
||| are de-facto amortized O(1).
export
record DisjointSet (s : Type) (k : Nat) where
  constructor DSF
  arr : MArray s k (DSNode k)

||| Allocates a fresh `DisjointSet` data type with all
||| values from `0` to `k-1` in their own partition.
export
ds : (k : Nat) -> F1 s (DisjointSet s k)
ds k t = let m # t := marray1 k (R 1) t in DSF m # t

dspair : DisjointSet s k -> Fin k -> F1 s (Fin k,Nat)
dspair ds x t =
  case get ds.arr x t of
    R s # t => (x,s) # t
    N p # t =>
     let r # t := dspair ds (assert_smaller x p) t
         _ # t := set ds.arr x (N $ fst r) t
      in r # t

||| Returns the current root node of `x`, used for identifying
||| the partition, to which `x` currently belongs.
export %inline
root : DisjointSet s k -> (x : Fin k) -> F1 s (Fin k)
root ds x t = let p # t := dspair ds x t in fst p # t

||| Returns the size of the partition `x` currently belongs to.
export %inline
size : DisjointSet s k -> (x : Fin k) -> F1 s Nat
size ds x t = let p # t := dspair ds x t in snd p # t

||| Returns `True` if `x` and `y` belong to the same partition,
||| `False` otherwise.
export
samePartition : DisjointSet s k -> (x,y : Fin k) -> F1 s Bool
samePartition ds x y t =
 let rx # t := root ds x t
     ry # t := root ds y t
  in (rx == ry) # t

||| Computes the set union of the partitions of `x` and `y`.
export
union : DisjointSet s k -> (x,y : Fin k) -> F1' s
union ds x y = T1.do
  (rx,sx) <- dspair ds x
  (ry,sy) <- dspair ds y
  case rx == ry of
    True  => pure ()
    False => case sx > sy of
      True  => set ds.arr rx (R $ sx + sy) >> set ds.arr ry (N rx)
      False => set ds.arr ry (R $ sx + sy) >> set ds.arr rx (N ry)

export
sets : {k : _} -> DisjointSet s k -> F1 s (List $ List (Fin k))
sets ds = go empty k
  where
    go :
         SortedMap (Fin k) (List $ Fin k)
      -> (n : Nat)
      -> {auto 0 lte : LTE n k}
      -> F1 s (List $ List (Fin k))
    go m 0     t = values m # t
    go m (S j) t =
     let x     := natToFinLT j
         r # t := root ds x t
      in go (update (Just . maybe [x] (x::)) r m) j t
