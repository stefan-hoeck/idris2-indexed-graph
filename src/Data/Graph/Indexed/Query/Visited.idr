module Data.Graph.Indexed.Query.Visited

import Data.Bits
import Data.Buffer
import Data.Linear.Traverse1
import public Data.Graph.Indexed
import public Data.Buffer.Mutable

%default total

--------------------------------------------------------------------------------
--          MVisited
--------------------------------------------------------------------------------

parameters {0 g : Graph e n}
           (r   : MBuffer s g.order)

  ||| Set the current node to "visited".
  export %inline
  mvisit : Node g -> F1' s
  mvisit (N i) = set r i 1

  ||| Set all given nodes to "visited"
  export %inline
  mvisitAll : List (Node g) -> F1' s
  mvisitAll = traverse1_ mvisit

  ||| True, if the current node has been visited.
  export %inline
  mvisited : Node g -> F1 s Bool
  mvisited (N x) t =
    case Buffer.Core.get r x t of
      1 # t => True  # t
      _ # t => False # t

  ||| True, if the current node has not yet been visited.
  export %inline
  munvisited : Node g -> F1 s Bool
  munvisited (N x) t =
    case Buffer.Core.get r x t of
      1 # t => False # t
      _ # t => True  # t

||| Allocate a linear byte array and use it to run the given
||| computation, discarding it at the end.
|||
||| This is a convenience alias for `visiting` for those cases, where
||| we already have a function returning a linear pair of values.
export %inline
visiting : (g : Graph e n) -> WithMBuffer g.order a -> a
visiting g = alloc g.order

--------------------------------------------------------------------------------
--          Visited
--------------------------------------------------------------------------------

||| Immutable value for keeping track of the visited nodes in a graph.
|||
||| Note: Profiling on the Chez backend showed, that this is considerably
|||       faster than `MVisited` for `k < 64`. For larger `k`, however,
|||       `MVisited` outperforms this by far.
export
record Visited (g : Graph e n) where
  constructor V
  vis : Integer

||| Initial `Visited` state
export
ini : Visited g
ini = V 0

||| Set the current node to "visited".
export %inline
visit : Node g -> Visited g -> Visited g
visit (N i) (V b) = V $ setBit b (finToNat i)

||| Set all given nodes to "visited".
export %inline
visitAll : List (Node g) -> Visited g -> Visited g
visitAll vs v = foldl (flip visit) v vs

||| True, if the current node has been visited.
export %inline
visited : Node g -> Visited g -> Bool
visited (N i) (V b) = testBit b (finToNat i)

||| True, if the current node has not yet been visited.
export %inline
unvisited : Node g -> Visited g -> Bool
unvisited i = not . visited i
