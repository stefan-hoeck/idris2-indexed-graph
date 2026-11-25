module Data.Graph.Indexed

import Data.Array
import Data.Array.Index
import Data.Array.Mutable
import Data.Linear.Traverse1
import Derive.Prelude
import public Data.Array
import public Data.AssocList.Indexed
import public Data.Graph.Indexed.Edge

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Adjacency
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
record IAdj k e n where
  constructor IA
  label       : n
  neighbours  : AssocList k e

%runElab derivePattern "IAdj" [I,P,P] [Show,Eq]

export
weakenAdj : IAdj k e n -> IAdj (S k) e n
weakenAdj (IA l ns) = IA l $ weakenAL ns

export
weakenAdjN : (0 m : Nat) -> IAdj k e n -> IAdj (k + m) e n
weakenAdjN m (IA l ns) = IA l $ weakenALN m ns

export %inline
fromLabel : n -> IAdj k e n
fromLabel v = IA v empty

export %inline
Functor (IAdj k e) where
  map f = { label $= f }

export
Foldable (IAdj k e) where
  foldl f a n  = f a n.label
  foldr f a n  = f n.label a
  foldMap  f n = f n.label
  null _       = False
  toList n     = [n.label]
  foldlM f a n = f a n.label

export %inline
Traversable (IAdj k e) where
  traverse f (IA n l) = (`IA` l) <$> f n

namespace AdjFunctor
  export
  [AdjEdge] Functor (\e => IAdj k e n) where
    map f = {neighbours $= map f}

namespace AdjFoldable
  export
  [AdjEdge] Foldable (\e => IAdj k e n) where
    foldl f a  = foldl f a . neighbours
    foldr f a  = foldr f a . neighbours
    foldMap  f = foldMap f . neighbours
    null       = null . neighbours
    toList     = toList . neighbours
    foldlM f a = foldlM f a . neighbours

export
Bifunctor (IAdj k) where
  bimap  f g (IA l es) = IA (g l) (map f es)
  mapFst f (IA l es)   = IA l (map f es)
  mapSnd g (IA l es)   = IA (g l) es

export
Bifoldable (IAdj k) where
  bifoldr f g acc (IA l es) = foldr f (g l acc) es
  bifoldl f g acc (IA l es) = g (foldl f acc es) l
  binull                 _ = False

export
Bitraversable (IAdj k) where
  bitraverse f g (IA l es) = [| IA (g l) (traverse f es) |]

--------------------------------------------------------------------------------
--          Indexed Graph
--------------------------------------------------------------------------------

||| An order-indexed graph.
public export
record IGraph (o : Nat) (e,n : Type) where
  constructor IG
  graph : IArray o (IAdj o e n)

export
{o : _} -> Eq e => Eq n => Eq (IGraph o e n) where
  IG x == IG y = x == y

export
{o : _} -> Functor (IGraph o e) where
  map f (IG g) = IG $ map (map f) g

export
{o : _} -> Foldable (IGraph o e) where
  foldl f a  (IG g) = foldl (\a',adj => f a' adj.label) a g
  foldr f a  (IG g) = foldr (f . label) a g
  foldMap  f (IG g) = foldMap (f . label) g
  toList     (IG g) = map label $ toList g
  null       (IG g) = o == 0

export
{o : _} -> Traversable (IGraph o e) where
  traverse f (IG g) = IG <$> traverse (traverse f) g

export
{o : _} -> Bifunctor (IGraph o) where
  bimap  f g (IG m) = IG $ bimap f g <$> m
  mapFst f   (IG m) = IG $ mapFst f <$> m
  mapSnd g   (IG m) = IG $ mapSnd g <$> m

export
{o : _} -> Bifoldable (IGraph o) where
  bifoldr f g acc (IG x) = foldr (flip $ bifoldr f g) acc x
  bifoldl f g acc (IG x) = foldl (bifoldl f g) acc x
  binull          (IG x) = null x

export
{o : _} -> Bitraversable (IGraph o) where
  bitraverse f g (IG h) = IG <$> traverse (bitraverse f g) h

--------------------------------------------------------------------------------
--          Internal utilities
--------------------------------------------------------------------------------

||| Updates all node labels in a mutable graph.
export %inline
lupdNodes : {k : _} -> MArray s k (IAdj k e n) -> (n -> n) -> F1' s
lupdNodes r f = mupdate {label $= f} r

parameters (r : MArray s k (IAdj k e n))

  ||| Updates the node label at the given position in a mutable graph.
  export %inline
  lupdNode : (n1 : Fin k) -> (n -> n) -> F1' s
  lupdNode n1 f = modify r n1 {label $= f}

  ||| Sets the node label at the given position in a mutable graph.
  export %inline
  lsetNode : (n1 : Fin k) -> n -> F1' s
  lsetNode n1 v = modify r n1 {label := v}

  ||| Insert a single edge into a mutable array-representation of a graph.
  export
  linsEdge : IEdge k e ->F1' s
  linsEdge (IE n1 n2 el) t =
    let _ # t := modify r n1 {neighbours $= insert n2 el} t
     in modify r n2 {neighbours $= insert n1 el} t

  ||| Delete a single edge from a mutable array-representation of a graph.
  export
  ldelEdge : (n1, n2 : Fin k) -> F1' s
  ldelEdge n1 n2 t =
    let _ # t := modify r n1 {neighbours $= delete n2} t
     in modify r n2 {neighbours $= delete n1} t

  ||| Insert a bunch of edges into a mutable array-representation of a graph.
  export %inline
  linsEdges : List (IEdge k e) -> F1' s
  linsEdges = traverse1_ linsEdge

  ||| Insert a bunch of edges into a mutable array-representation of a graph.
  export %inline
  ldelEdges : List (Fin k, Fin k) -> F1' s
  ldelEdges = traverse1_ (\(x,y) => ldelEdge x y)

--------------------------------------------------------------------------------
--          Inspecting Graphs
--------------------------------------------------------------------------------

parameters (g : IGraph o e n)

  ||| Returns the adjacency (node label plus labeled edges to neighbours)
  ||| of a node in a graph.
  export %inline
  iadj : Fin o -> IAdj o e n
  iadj = at g.graph

  ||| Returns the label of a node in graph.
  export %inline
  ilab : Fin o -> n
  ilab = label . iadj

  ||| Returns the edges connecting a node as an `AssocList`
  ||| (nodes plus edge labels).
  export %inline
  ineighboursAsAL : Fin o -> AssocList o e
  ineighboursAsAL = neighbours . iadj

  ||| Returns the edges connecting a node as a list of pairs
  ||| (nodes plus edge labels).
  export %inline
  ineighboursAsPairs : Fin o -> List (Fin o, e)
  ineighboursAsPairs = pairs . ineighboursAsAL

  ||| Returns the list of neighbouring nodes of a node in a graph.
  export %inline
  ineighbours : Fin o -> List (Fin o)
  ineighbours = keys . ineighboursAsAL

  ||| Returns the list of edges connecting a node.
  export %inline
  iedgesTo : Fin o -> List (IEdge o e)
  iedgesTo x = mapMaybe (\(n,l) => mkEdge x n l) $ ineighboursAsPairs x

  ||| Returns the list of neighboring nodes paired with their
  ||| corresponding labels.
  export
  ilneighbours : Fin o -> List (Fin o, n)
  ilneighbours = map (\x => (x, ilab x)) . ineighbours

  ||| Returns the edges connecting a node paired with the
  ||| neighbouring node labels.
  export
  ilneighboursAsAL : Fin o -> AssocList o (e, n)
  ilneighboursAsAL = mapKV (\x => (, ilab x)) . ineighboursAsAL

  ||| Returns the labels of neighbour nodes of a node.
  export
  ineighbourLabels : Fin o -> List n
  ineighbourLabels = map ilab . ineighbours

  ||| Returns the labels of edges connecting a node.
  export %inline
  iedgeLabels : Fin o -> List e
  iedgeLabels = values . neighbours . iadj

  ||| Find the label for an `IEdge`.
  export
  ielab : (x,y : Fin o) -> Maybe e
  ielab x y = lookup y . neighbours $ iadj x

  ||| Find the label for an `IEdge`.
  export
  iedge : (x,y : Fin o) -> Maybe (IEdge o e)
  iedge x y = ielab x y >>= mkEdge x y

  ||| Tests if the given nodes are adjecent (connected via an edge).
  export
  iadjacent : (x,y : Fin o) -> Bool
  iadjacent x y = isJust $ ielab x y

  ||| The degree of the `Node`.
  export %inline
  ideg : Fin o -> Nat
  ideg = length . ineighbours

||| List all 'Node's in the 'Graph'.
export %inline
inodes : {o : _} -> (0 g : IGraph o e n) -> List (Fin o)
inodes g = allFinsFast o

||| A list of all labeled nodes of a `Graph`
export
ilabNodes : {o : _} -> IGraph o e n -> List (Fin o, n)
ilabNodes g = map (\x => (x, ilab g x)) $ inodes g

||| A list of all labeled nodes of a `Graph`
export %inline
ilabels : {o : _} -> IGraph o e n -> List n
ilabels g = ilab g <$> inodes g

-- we return only edges to nodes greater than the node in the
-- context to avoid returning every edge twice in `labEdges`.
ctxtEdgs : Fin o -> IAdj o e n -> SnocList (IEdge o e)
ctxtEdgs x (IA _ ns) = foldlKV acc [<] ns

  where
    acc : Fin o -> SnocList (IEdge o e) -> e -> SnocList (IEdge o e)
    acc y sp v with (compare x y) proof eq
      _ | LT = sp :< IE x y v
      _ | _  = sp

||| A list of all `IEdge`s in the `Graph` (in lexicographic order).
export
iedges  : {o : _} -> IGraph o e n -> List (IEdge o e)
iedges (IG g) = foldrKV (\x,adj,es => ctxtEdgs x adj <>> es) [] g

||| The number of edges in the graph.
export %inline
isize : {o : _} -> IGraph o e n -> Nat
isize g = length $ iedges g

--------------------------------------------------------------------------------
--          Making Graphs
--------------------------------------------------------------------------------

||| An empty `Graph`
export
iempty : IGraph 0 e n
iempty = IG empty

||| Create a `Graph` from a vect of labeled nodes and edges.
export
mkIGraph : {o : _} -> (ns : Vect o n) -> List (IEdge o e) -> IGraph o e n
mkIGraph ns es =
  IG $ allocVect (map (`IA` empty) ns) $ \r,t =>
    let _ # t := linsEdges r es t
     in unsafeFreeze r t

||| Create a `Graph` from a vect of labeled nodes and edges.
export
mkIGraph' : {o : _} -> (ns : Vect o n) -> List (Nat,Nat,e) -> IGraph o e n
mkIGraph' ns = mkIGraph ns . mapMaybe (\(x,y,l) => tryFromNat x y l)

||| Create a `Graph` from a list of labeled nodes and edges.
export
mkIGraphL : (ns : List n) -> List (Nat,Nat,e) -> IGraph (length ns) e n
mkIGraphL ns = mkIGraph' (fromList ns)

||| Create a `Graph` from a vect of labeled nodes and edges.
|||
||| Unlike `mkGraph`, this puts the nodes in the array in reverse order,
||| which is useful when they come from a parser with the last node being
||| at the head of the vector.
export
mkIGraphRev : {o : _} -> (ns : Vect o n) -> List (IEdge o e) -> IGraph o e n
mkIGraphRev ns es =
 IG $ allocVectRev (map (`IA` empty) ns) $ \r,t =>
   let _ # t := linsEdges r es t
    in unsafeFreeze r t

export %inline
igenerate : (o : Nat) -> (Fin o -> IAdj o e n) -> IGraph o e n
igenerate o = IG . generate o

--------------------------------------------------------------------------------
--          Folds and Traversals
--------------------------------------------------------------------------------

parameters {o : Nat}
           (g : IGraph o e n)

  ||| Map the adjacencies in a graph accoring to each node's context
  export %inline
  imapCtxt : (Fin o -> IAdj o e n -> IAdj o e1 n1) -> IGraph o e1 n1
  imapCtxt fun = IG $ mapWithIndex fun g.graph

  ||| Map the node labels in a graph accoring to each node's context
  export %inline
  imapWithCtxt : (Fin o -> IAdj o e n -> n1) -> IGraph o e n1
  imapWithCtxt fun = imapCtxt (\x,adj => adj $> fun x adj)

  ||| Map the adjacencies in a graph
  export %inline
  imapAdj : (IAdj o e n -> IAdj o f m) -> IGraph o f m
  imapAdj fun = IG $ map fun g.graph

  ||| Map the node labels in a graph accoring to each node's adjacency
  export %inline
  imapWithAdj : (IAdj o e n -> m) -> IGraph o e m
  imapWithAdj fun = imapAdj (\adj => adj $> fun adj)

  export
  itraverseCtxt :
       {auto app : Applicative f}
    -> (Fin o -> IAdj o e n -> f (IAdj o e1 n1))
    -> f (IGraph o e1 n1)
  itraverseCtxt fun = IG <$> traverseWithIndex fun g.graph

  export
  itraverseWithCtxt :
       {auto app : Applicative f}
    -> (Fin o -> IAdj o e n -> f n1)
    -> f (IGraph o e n1)
  itraverseWithCtxt fun = itraverseCtxt (\x,a => (`IA` a.neighbours) <$> fun x a)

--------------------------------------------------------------------------------
--          Modifying Graphs
--------------------------------------------------------------------------------

  ||| Uses two functions for updating nodes in a graph:
  |||
  ||| Once is used for the given node, the other for all other nodes.
  export
  updateNodes : Fin o -> (f,h : n -> m) -> IGraph o e m
  updateNodes x f h =
    imapWithCtxt (\y,a => if x == y then f a.label else h a.label)

  ||| Updates a single node in the graph at the given position.
  export %inline
  updateNode : Fin o -> (n -> n) -> IGraph o e n
  updateNode x f = updateNodes x f id

  ||| Replaces a single node in the graph at the given position.
  export %inline
  setNode : Fin o -> n -> IGraph o e n
  setNode x = updateNode x . const

  ||| Uses two functions for updating the edge labels in a graph.
  |||
  ||| Once is used for the edge connecting the two given nodes, the other for
  ||| all other edges.
  export
  updateEdges : (x,y : Fin o) -> (f,h : e -> e2) -> IGraph o e2 n
  updateEdges x y f h =
    imapCtxt $ \k,(IA l a) =>
     IA l $
       if      k == x then mapKV (\m,l => if m == y then f l else h l) a
       else if k == y then mapKV (\m,l => if m == x then f l else h l) a
       else    map h a

  ||| Uses a function for updating a single edge label in a graph.
  export %inline
  updateEdge : (x,y : Fin o) -> (f : e -> e) -> IGraph o e n
  updateEdge x y f = updateEdges x y f id

  ||| Insert (or replace) a single edge in a graph.
  export
  insEdges : List (IEdge o e) -> IGraph o e n
  insEdges es =
    IG $ allocGen o (iadj g) $ \r,t =>
      let _ # t := linsEdges r es t in unsafeFreeze r t

  ||| Insert an `IEdge` into the 'IGraph'.
  export %inline
  insEdge : IEdge o e -> IGraph o e n
  insEdge x = insEdges [x]

  ||| Remove multiple 'IEdge's from the 'Graph'.
  export
  delEdges : List (Fin o, Fin o) -> IGraph o e n
  delEdges ps =
    IG $ allocGen o (iadj g) $ \r,t =>
      let _ # t := ldelEdges r ps t in unsafeFreeze r t

  ||| Remove an 'IEdge' from the 'Graph'.
  export %inline
  delEdge : (x,y : Fin o) -> IGraph o e n
  delEdge x y = delEdges [(x,y)]

  ||| Insert multiple `LNode`s into the `Graph`.
  export
  insNodes : {m : _} -> (ns : Vect m n) -> IGraph (o+m) e n
  insNodes ns =
    let g' := map (weakenAdjN m) g.graph
     in IG $ append g' (map fromLabel (array ns))

  ||| Insert a labeled node into the `Graph`.
  ||| The behavior is undefined if the node is already
  ||| in the graph.
  export %inline
  insNode : n -> IGraph (S o) e n
  insNode v = rewrite plusCommutative 1 o in insNodes [v]

||| Insert multiple `LNode`s into the `Graph`.
export %inline
insNodesAndEdges :
     {m,o : _}
  -> (g  : IGraph o e n)
  -> (ns : Vect m n)
  -> (es : List (IEdge (o+m) e))
  -> IGraph (o+m) e n
insNodesAndEdges g = insEdges . insNodes g

||| Merge two graphs connecting them via the given list of
||| edges
export
mergeGraphsWithEdges :
     {o,m : _}
  -> (g1 : IGraph o e n)
  -> (g2 : IGraph m e n)
  -> List (Fin o, Fin m, e)
  -> IGraph (o+m) e n
mergeGraphsWithEdges g1 g2 es =
  let vNodes := label <$> toVect g2.graph
      cEdges := map (\(x,y,l) => compositeEdge x y l) es
      lEdges := incEdge o <$> iedges g2
   in insNodesAndEdges g1 vNodes (cEdges ++ lEdges)

||| Merge two graphs that have no bonds between them.
export
mergeGraphs : {o,m : _} -> IGraph o e n -> IGraph m e n -> IGraph (o+m) e n
mergeGraphs g1 g2 =
  let vNodes := label <$> toVect g2.graph
      lEdges := incEdge o <$> iedges g2
   in insNodesAndEdges g1 vNodes lEdges

--------------------------------------------------------------------------------
--          Displaying Graphs
--------------------------------------------------------------------------------

export
{o : _} -> Show e => Show n => Show (IGraph o e n) where
  showPrec p g =
    showCon p "mkIGraph" $ showArg (ilabels g) ++ showArg (iedges g)

pl : Nat -> Fin o -> String
pl n = padLeft n ' ' . show

export
ipretty : {o : _} -> (e -> String) -> (n -> String) -> IGraph o e n -> String
ipretty de dn g =
  let ns     := ilabNodes g
      es     := iedges g
      maxLen := length $ show o
   in unlines $
        "Nodes:"   :: map (dispNode maxLen) ns ++
        "\nEdges:" :: map (dispEdge maxLen) es

  where
    dispNode : Nat -> (Fin o, n) -> String
    dispNode k (n1,l) =
      "  \{pl k n1} :> \{dn l}"

    dispEdge : Nat -> IEdge o e -> String
    dispEdge k (IE n1 n2 l) =
      "IE \{pl k n1} \{pl k n2}  \{de l}"
