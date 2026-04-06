module Data.Graph.Indexed.Util.Bipartite

import Data.Graph.Indexed
import Data.Linear.List
import Data.Linear.Token
import Data.Linear.Traverse1
import Data.Queue

%default total

data Color = Unset | Even | Odd

toBool : Color -> Bool
toBool Odd = False
toBool _   = True

not : Color -> Color
not Even = Odd
not _    = Even

matches : Color -> Color -> Bool
matches Even Even = True
matches Odd  Odd  = True
matches _    _    = False

parameters (g  : IGraph k e n)
           (cs : MArray s k Color)

  setc : Fin k -> Color -> Queue (Color,Fin k) -> F1 s (Queue (Color,Fin k))
  setc x c q t =
   let _ # t := set cs x c t
    in enqueueAll q ((not c,) <$> neighbours g x) # t

  bfs : Queue (Color,Fin k) -> F1 s Bool
  bfs q t =
    case dequeue q of
      Nothing         => True # t
      Just ((c,x),q2) => case Core.get cs x t of
        Unset # t => let q3 # t := setc x c q2 t in bfs (assert_smaller q q3) t
        col   # t => case matches c col of
          True  => bfs (assert_smaller q q2) t
          False => False # t

||| Tries to color a graph with only two colors, so that all
||| edges in the graph connect nodes of distinct colors.
|||
||| Returns the coloring in case of a success and `Nothing` otherwise.
export
bipartite : {k : _} -> IGraph k e n -> Maybe (IArray k Bool)
bipartite g = alloc k Unset (go $ nodes g)
  where
    go : List (Fin k) -> MArray s k Color -> F1 s (Maybe $ IArray k Bool)
    go []        cs t =
     let ci # t := unsafeFreeze cs t
      in Just (map toBool ci) # t
    go (x :: xs) cs t =
     let Unset # t := Core.get cs x t                 | _ # t => go xs cs t
         True  # t := bfs g cs (fromList [(Odd,x)]) t | _ # t => Nothing # t
      in go xs cs t

--------------------------------------------------------------------------------
-- Matches on bipartite graphs
--------------------------------------------------------------------------------

||| Finds a maximal matching for a bipartite graph. Returns `Nothing`
||| in case the graph is not bipartite.
export
match : {k : _} -> IGraph k e n -> Maybe (IArray k (Maybe $ Fin k))
-- implementation below

||| Tries to find a perfect matching for a bipartite graph.
||| Returns `Nothing` in case the graph is not bipartite or no
||| perfect matching exists.
export
perfectMatch : {k : _} -> IGraph k e n -> Maybe (IArray k (Fin k))
perfectMatch g = match g >>= sequence

--------------------------------------------------------------------------------
-- Hopcroft-Karp: Implementation
--------------------------------------------------------------------------------

0 Q : Nat -> Type
Q k = Queue (Fin k)

0 MDist : Type -> Nat -> Type
MDist s k = MArray s k Nat

0 Dist : Nat -> Type
Dist k = IArray k Nat

0 Pair : Type -> Nat -> Type
Pair s k = MArray s k (Maybe $ Fin k)

%inline
link : Pair s k => Fin k -> F1 s (Maybe $ Fin k)
link @{p} = Core.get p

%inline
isFree : Pair s k => Fin k -> F1 s Bool
isFree x t =
  case link x t of
    Nothing # t => True # t
    _       # t => False # t

%inline
doLink : Pair s k => (x,y : Fin k) -> F1 s Bool
doLink @{p} x y t =
 let _ # t := Core.set p x (Just y) t
     _ # t := Core.set p y (Just x) t
  in True # t

%inline
dist : MDist s k => Fin k -> F1 s Nat
dist @{d} = Core.get d

%inline
putDist : MDist s k => Fin k -> Nat -> F1' s
putDist @{d} = Core.set d

enq : Pair s k => MDist s k => Nat -> List (Fin k) -> Q k -> F1 s (Q k)
enq _ []      q t = q # t
enq l (v::vs) q t =
 let Just u # t := link v t | _ # t => enq l vs q t
     Z      # t := dist u t | _ # t => enq l vs q t
     _      # t := putDist u l t
  in enq l vs (enqueue q u) t

parameters {0 s,e,n : Type}
           (g    : IGraph k e n)

  layers : (d : MDist s k) => Pair s k => Q k -> F1 s (Dist k)
  layers q t =
    case dequeue q of
      Nothing     => unsafeFreeze d t
      Just (u,q2) =>
       let du # t := dist u t
           q3 # t := enq (S du) (neighbours g u) q2 t
        in layers (assert_smaller q q3) t

  dfs : Pair s k => Dist k -> Fin k -> F1 s Bool
  dfs dist u t = go (neighbours g u) t
    where
      go : List (Fin k) -> F1 s Bool
      go []      t = False # t
      go (v::vs) t =
       let Just w # t := link v t                        | _ # t => doLink u v t
           True       := at dist w == S (at dist u)      | False => go vs t
           True # t   := dfs dist (assert_smaller u w) t | _ # t => go vs t
        in doLink u v t

match g =
  map
    (\cs => alloc k Nothing $ \x => loop @{x} (filter (at cs) (nodes g)))
    (bipartite g)
  where
    loop : Pair s k => List (Fin k) -> F1 s (IArray k (Maybe $ Fin k))
    loop @{p} es t =
     let fs # t := filter1 isFree es t
         md # t := marray1 k Z t
         _  # t := for1_ fs (\x => putDist x 1) t
         ds # t := layers g (fromList fs) t
         [] # t := filter1 (dfs g ds) fs t | _ # t => loop (assert_smaller es fs) t
      in unsafeFreeze p t
