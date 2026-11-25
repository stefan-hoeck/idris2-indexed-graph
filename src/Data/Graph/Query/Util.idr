||| Utilities for graph traversals.
module Data.Graph.Query.Util

import Data.Graph.Query.Visited

%default total

||| Extract a value from a `Left` because we know the `Right` is
||| uninhabited.
public export %inline
fromLeft : Either a Void -> a
fromLeft (Left v) = v
fromLeft (Right _) impossible

||| Convert a binary function to one returning an `Left`
public export %inline
fleft2 : (a -> b -> c) -> a -> b -> Either c Void
fleft2 f x = Left . f x

||| Convert a ternary function to one returning an `Left`
public export %inline
fleft3 : (a -> b -> c -> d) -> a -> b -> c -> Either d Void
fleft3 f x y = Left . f x y

||| Internal alias for stateful functions when visiting large graphs
public export
0 MVis : Type -> (g : Graph e n) -> Type -> Type
MVis t g a = MBuffer t g.order -> F1 t a

export %inline
fromLeftMVis : R1 s (Either a Void) -@ R1 s a
fromLeftMVis (x # m) = fromLeft x # m
