||| This module provides utilities used to compute families of relevant cycles
||| as described by Vismara et al in "Union of all the minimum cycle bases of a graph"
||| (The Electronic Journal of Combinatorics 4 (1997)).
|||
||| In particular, it computes candidates of relevant cycle familes.
module Data.Graph.Indexed.Ring.Relevant.Candidates

import Data.Graph.Indexed.Ring.Relevant.ShortestPath
import Data.Graph.Indexed.Ring.Relevant.Types
import Data.SnocList

%default total

export
origin : (sg : Subgraph g) -> NCycle sg -> NCycle g
origin g = {path $= map Subgraph.origin}

isolate : Subgraph g -> Maybe (NCycle g)
isolate g@(G n@(S (S _)) _) = Just $ NC (map origin $ nodes g ++ [N FZ]) (S n) 1
isolate _                   = Nothing

notLast : Node g -> Sedon g -> Bool
notLast x (_ :< y :< _) = x /= y
notLast x _             = True

revOnto : SnocList a -> SnocList a -> List a
revOnto sx [<] = sx <>> []
revOnto sx (sy:<y) = revOnto (sx :< y) sy

appMaybe : SnocList a -> Maybe a -> SnocList a
appMaybe sc = maybe sc (sc:<)

gte3 : Nat -> Maybe (Subset Nat (LTE 3))
gte3 n =
  case tryLTE {n} 3 of
    Just0 prf => Just (Element n prf)
    Nothing0  => Nothing

parameters (g    : Graph e n)
           (root : Node g)
           (degs : IArray g.order Nat)

  connector : Sedon g -> Sedon g -> Node g -> Bool
  connector sx sy x = smaller root degs x && notLast x sx && notLast x sy

  -- Takes a list of reverse paths starting all from the same node and
  -- sorted by length (this is by construction: the `shortestPaths` algorithm
  -- will produce shorter paths earlier than longer paths), pairs every
  -- path with all successors of equal length (resulting in odd cycles) and
  -- one node longer (resulting in even cycles), and connect the two parts if
  -- they form a proper elementary cycle.
  cycleSystem : List (NCycle g)
  cycleSystem = go [<] (shortestPaths g degs root)
    where
      -- computes an odd cycle by concatenating two paths ending
      --
      %inline
      odd : (p1,p2 : Path g) -> Maybe (NCycle g)
      odd p1 p2 =
        flip map (gte3 (pred $ p1.length + p2.length)) $ \(Element s _) =>
          NC (revOnto p1.path p2.path) s (p1.combos * p2.combos)

      %inline
      even : (p1,p2 : Path g) -> Node g -> Maybe (NCycle g)
      even p1 p2 x =
        if connector p1.path p2.path x
          then
            flip map (gte3 (p1.length + p2.length)) $ \(Element s _) =>
              NC (revOnto (p1.path :< x) p2.path) s (p1.combos * p2.combos)
          else Nothing

      addCs : SnocList (NCycle g) -> Path g -> List (Path g) -> SnocList (NCycle g)
      addCs sc p [] = sc
      addCs sc p@(P len1 p1 _ f1 l1 _) (q@(P len2 p2 _ f2 l2 _)::qs) =
        let True  := len1 == len2     | False => sc
            False := f1 == f2         | True  => addCs sc p qs
            False := adjacent l1 l2   | True  => addCs (appMaybe sc $ odd p q) p qs
            ns    := fromFins $ keys $ intersect (neighboursAsAL l1) (neighboursAsAL l2)
         in addCs (sc <>< mapMaybe (even p q) ns) p qs

      -- for the current path, we take from the remaining paths those
      -- that are at most one node longer and try to pair them to
      -- form a cycle.
      go : SnocList (NCycle g) -> List (Path g) -> List (NCycle g)
      go sxs []        = sxs <>> []
      go sxs (p :: ps) = go (addCs sxs p ps) ps

findCandidates : (sg : Subgraph g) -> IArray sg.order Nat -> Candidates g
findCandidates sg degs =
  case filter ((2 <) . atN degs) (nodes sg) of
    [] => maybe Empty (Isolate sg) (isolate sg)
    ns => System sg (ns >>= \n => cycleSystem sg n degs)

||| Computes the potential relevant cycle familes for a biconnected
||| component of a graph.
export %inline
componentCandidates : Subgraph g -> Candidates g
componentCandidates g = findCandidates g (generate g.order (deg {g} . N))

||| Cuts a graph into strongly connected components and computes
||| the potential relevant cycle families for each component in
||| isolation.
export %inline
candidates : (g : Graph e n) -> List (Candidates g)
candidates g = map componentCandidates $ biconnectedComponents g
