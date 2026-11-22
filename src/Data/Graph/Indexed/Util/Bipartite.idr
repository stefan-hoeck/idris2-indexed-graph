module Data.Graph.Indexed.Util.Bipartite

import Data.Graph.Indexed
import Data.Graph.Indexed.Subgraph
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

parameters (g  : Graph e n)
           (cs : MArray s g.order Color)

  setc : Node g -> Color -> Queue (Color,Node g) -> F1 s (Queue (Color,Node g))
  setc x c q t =
   let _ # t := set cs x.node c t
    in enqueueAll q ((not c,) <$> neighbours x) # t

  bfs : Queue (Color,Node g) -> F1 s Bool
  bfs q t =
    case dequeue q of
      Nothing         => True # t
      Just ((c,x),q2) => case Core.get cs x.node t of
        Unset # t => let q3 # t := setc x c q2 t in bfs (assert_smaller q q3) t
        col   # t => case matches c col of
          True  => bfs (assert_smaller q q2) t
          False => False # t

||| Tries to color a graph with only two colors, so that all
||| edges in the graph connect nodes of distinct colors.
|||
||| Returns the coloring in case of a success and `Nothing` otherwise.
export
bipartite : (g : Graph e n) -> Maybe (IArray g.order Bool)
bipartite g = alloc g.order Unset (go $ nodes g)
  where
    go : Nodes g -> MArray s g.order Color -> F1 s (Maybe $ IArray g.order Bool)
    go []        cs t =
     let ci # t := unsafeFreeze cs t
      in Just (map toBool ci) # t
    go (x :: xs) cs t =
     let Unset # t := Core.get cs x.node t            | _ # t => go xs cs t
         True  # t := bfs g cs (fromList [(Odd,x)]) t | _ # t => Nothing # t
      in go xs cs t

--------------------------------------------------------------------------------
-- Matches on bipartite graphs
--------------------------------------------------------------------------------

||| Finds a maximal matching for a bipartite graph. Returns `Nothing`
||| in case the graph is not bipartite.
export
match : (g : Graph e n) -> Maybe (IArray g.order (Maybe $ Node g))
-- implementation below

||| Tries to find a perfect matching for a bipartite graph.
||| Returns `Nothing` in case the graph is not bipartite or no
||| perfect matching exists.
export
perfectMatch : (g : Graph e n) -> Maybe (IArray g.order (Node g))
perfectMatch g = match g >>= sequence

||| Finds the edges of a maximal matching in a graph.
export
matchEdges : (g : Graph e n) -> List (LEdg g)
matchEdges g = maybe [] (\a => mapMaybe (edg a) (nodes g)) (match g)
  where
    edg : IArray g.order (Maybe $ Node g) -> Node g -> Maybe (LEdg g)
    edg a x = atN a x >>= \y => if x < y then edge x y else Nothing

||| Finds the edges of a maximal matching in a subgraph.
export
matchEdgesWhere :
     (g    : Graph e n)
  -> (pred : Node g -> Bool)
  -> List (LEdg g)
matchEdgesWhere g pred =
 let sg := subgraphL g (filter pred $ nodes g)
  in mapMaybe (originEdge sg) (matchEdges sg)

--------------------------------------------------------------------------------
-- Hopcroft-Karp: Implementation
--------------------------------------------------------------------------------

0 Q : Graph e n -> Type
Q g = Queue (Node g)

0 MDist : Type -> Graph e n -> Type
MDist s g = MArray s g.order Nat

0 Dist : Graph e n -> Type
Dist g = IArray g.order Nat

0 Pair : Type -> Graph e n -> Type
Pair s g = MArray s g.order (Maybe $ Node g)

%inline
link : Pair s g => Node g -> F1 s (Maybe $ Node g)
link @{p} n = Core.get p n.node

%inline
isFree : Pair s g => Node g -> F1 s Bool
isFree x t =
  case link x t of
    Nothing # t => True # t
    _       # t => False # t

%inline
doLink : Pair s g => (x,y : Node g) -> F1 s Bool
doLink @{p} x y t =
 let _ # t := Core.set p x.node (Just y) t
     _ # t := Core.set p y.node (Just x) t
  in True # t

%inline
dist : MDist s g => Node g -> F1 s Nat
dist @{d} n = Core.get d n.node

%inline
putDist : MDist s g => Node g -> Nat -> F1' s
putDist @{d} n = Core.set d n.node

enq : Pair s g => MDist s g => Nat -> Nodes g -> Q g -> F1 s (Q g)
enq _ []      q t = q # t
enq l (v::vs) q t =
 let Just u # t := link v t | _ # t => enq l vs q t
     Z      # t := dist u t | _ # t => enq l vs q t
     _      # t := putDist u l t
  in enq l vs (enqueue q u) t

parameters {0 s,e,n : Type}
           (g       : Graph e n)

  layers : (d : MDist s g) => Pair s g => Q g -> F1 s (Dist g)
  layers q t =
    case dequeue q of
      Nothing     => unsafeFreeze d t
      Just (u,q2) =>
       let du # t := dist u t
           q3 # t := enq (S du) (neighbours u) q2 t
        in layers (assert_smaller q q3) t

  dfs : Pair s g => Dist g -> Node g -> F1 s Bool
  dfs dist u t = go (neighbours u) t
    where
      go : Nodes g -> F1 s Bool
      go []      t = False # t
      go (v::vs) t =
       let Just w # t := link v t                        | _ # t => doLink u v t
           True       := atN dist w == S (atN dist u)    | False => go vs t
           True # t   := dfs dist (assert_smaller u w) t | _ # t => go vs t
        in doLink u v t

match g =
  map
    (\cs => alloc g.order Nothing $ \x => loop @{x} (filter (atN cs) (nodes g)))
    (bipartite g)
  where
    loop : Pair s g => Nodes g -> F1 s (IArray g.order (Maybe $ Node g))
    loop @{p} es t =
     let fs # t := filter1 isFree es t
         md # t := marray1 g.order Z t
         _  # t := for1_ fs (\x => putDist x 1) t
         ds # t := layers g (fromList fs) t
         [] # t := filter1 (dfs g ds) fs t | _ # t => loop (assert_smaller es fs) t
      in unsafeFreeze p t
