module Data.Graph.Indexed.Query.Visited

import Data.Bits
import Data.Buffer
import Data.Linear.Traverse1
import public Data.Buffer.Mutable

%default total

--------------------------------------------------------------------------------
--          MVisited
--------------------------------------------------------------------------------

public export
data Vis : Type where

public export
0 MVisited : Type -> Nat -> Type
MVisited s n = MBuffer Vis s n

||| Set the current node to "visited".
export %inline
mvisit : MVisited s k => Fin k -> F1' s
mvisit i = setAt Vis i 1

||| Set all given nodes to "visited"
export %inline
mvisitAll : List (Fin k) -> MVisited s k => F1' s
mvisitAll xs = traverse1_ mvisit xs

||| Test, if the current node has been visited.
export %inline
mvisited : Fin k -> MVisited s k => F1 s Bool
mvisited x t =
  case Core.getAt Vis x t of
    1 # t => True  # t
    _ # t => False # t

||| Allocate a linear byte array and use it to run the given
||| computation, discarding it at the end.
|||
||| This is a convenience alias for `visiting` for those cases, where
||| we already have a function returning a linear pair of values.
export
visiting : (k : Nat) -> ({0 s : _} -> MVisited s k => F1 s a) -> a
visiting k f =
  run1 $ \t =>
    let buf # t2 := newMBufferAt Vis k t
     in f t2

--------------------------------------------------------------------------------
--          Visited
--------------------------------------------------------------------------------

||| Immutable value for keeping track of the visited nodes in a graph.
|||
||| Note: Profiling on the Chez backend showed, that this is considerably
|||       faster than `MVisited` for `k < 64`. For larger `k`, however,
|||       `MVisited` outperforms this by far.
export
record Visited (k : Nat) where
  constructor V
  vis : Integer

||| Initial `Visited` state
export
ini : Visited k
ini = V 0

||| Set the current node to "visited".
export
visit : Fin k -> Visited k -> Visited k
visit i (V b) = V $ setBit b (finToNat i)

||| Set all given nodes to "visited".
export %inline
visitAll : List (Fin k) -> Visited k -> Visited k
visitAll vs v = foldl (flip visit) v vs

||| Test, if the current node has been visited.
export
visited : Fin k -> Visited k -> Bool
visited i (V b) = testBit b (finToNat i)
