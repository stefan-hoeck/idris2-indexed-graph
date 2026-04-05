module Data.Graph.Indexed.Util.Bipartite

import Data.Graph.Indexed
import Data.Linear.Token
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
