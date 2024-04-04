module Data.AssocList.Indexed

import Data.Array
import Data.Array.Mutable
import Data.List

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

weakenp : (Fin n, t) -> (Fin (S n), t)
weakenp (x,v) = (weaken x, v)

weakenpN : (0 m : Nat) -> (Fin n, t) -> (Fin (n + m), t)
weakenpN m (x,v) = (weakenN m x, v)

--------------------------------------------------------------------------------
--          Rep
--------------------------------------------------------------------------------

0 Rep : Nat -> Type -> Type
Rep n t = List (Fin n, t)

heqRep : Eq e => Rep k e -> Rep m e -> Bool
heqRep [] []               = True
heqRep ((n1,e1) :: xs) ((n2,e2) :: ys) =
  case finToNat n1 == finToNat n2 && e1 == e2 of
    True  => heqRep xs ys
    False => False
heqRep _         _         = False

insertRep : Fin n -> e -> Rep n e -> Rep n e
insertRep k el []        = [(k,el)]
insertRep k el (x :: xs) = case compare k (fst x) of
  LT => (k,el) :: x :: xs
  EQ => (k,el) :: xs
  GT => x :: insertRep k el xs

insertWithRep : (e -> e -> e) -> Fin n -> e -> Rep n e -> Rep n e
insertWithRep f k el []        = [(k,el)]
insertWithRep f k el (x :: xs) = case compare k (fst x) of
  LT => (k,el) :: x :: xs
  EQ => (k,f el (snd x)) :: xs
  GT => x :: insertWithRep f k el xs

lookupRep : Fin n -> Rep n e -> Maybe e
lookupRep x []        = Nothing
lookupRep x (y :: xs) = case compare x (fst y) of
  GT => lookupRep x xs
  EQ => Just (snd y)
  LT => Nothing

unionRep : Rep k e -> Rep k e -> Rep k e
unionRep []      ys      = ys
unionRep xs      []      = xs
unionRep l@(x::xs) r@(y::ys) = case compare (fst x) (fst y) of
  LT => x :: unionRep xs r
  EQ => x :: unionRep xs ys
  GT => y :: unionRep l ys

unionMapRep : (e -> e -> b) -> (e -> b) -> Rep k e -> Rep k e -> Rep k b
unionMapRep f g []        ys                    = map (map g) ys
unionMapRep f g xs        []                    = map (map g) xs
unionMapRep f g l@((k1,l1)::xs) r@((k2,l2)::ys) = case compare k1 k2 of
  LT => (k1, g l1)    :: unionMapRep f g xs r
  EQ => (k1, f l1 l2) :: unionMapRep f g xs ys
  GT => (k2, g l2)    :: unionMapRep f g l  ys

intersectWithRep : (e -> e -> b) -> Rep k e -> Rep k e -> Rep k b
intersectWithRep f []        ys                    = []
intersectWithRep f xs        []                    = []
intersectWithRep f l@((k1,l1)::xs) r@((k2,l2)::ys) = case compare k1 k2 of
  LT => intersectWithRep f xs r
  EQ => (k1, f l1 l2) :: intersectWithRep f xs ys
  GT => intersectWithRep f l  ys

weakenRep : Rep k e -> Rep (S k) e
weakenRep []        = []
weakenRep (x :: xs) = weakenp x :: weakenRep xs

weakenRepN : (0 m : Nat) -> Rep k e -> Rep (k + m) e
weakenRepN m []        = []
weakenRepN m (x :: xs) = weakenpN m x :: weakenRepN m xs

--------------------------------------------------------------------------------
--          AssocList
--------------------------------------------------------------------------------

export
record AssocList (k : Nat) (e : Type) where
  constructor AL
  ps : Rep k e

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Functor (AssocList k) where
  map f (AL ps) = AL $ map (map f) ps

export %inline
Foldable (AssocList k) where
  foldr c n (AL r) = foldr (c . snd) n r
  foldl c n (AL r) = foldl (\x => c x . snd) n r
  null (AL r)      = null r
  foldMap f (AL r) = foldMap (f . snd) r
  toList (AL r)    = map snd r

export %inline
Traversable (AssocList k) where
  traverse f (AL r) = AL <$> traverse (\(n,l) => (n,) <$> f l) r

export %inline
Eq e => Eq (AssocList k e) where
  AL r1 == AL r2 = heqRep r1 r2

export
Show e => Show (AssocList k e) where
  showPrec p (AL r) =
    showCon p "fromList" $ showArg (map (\(n,l) => (finToNat n, l)) r)

export
weakenAL : AssocList k e -> AssocList (S k) e
weakenAL (AL r) = AL $ weakenRep r

export
weakenALN : (0 m : Nat) -> AssocList k e -> AssocList (k + m) e
weakenALN m (AL g) = AL $ weakenRepN m g

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

export %inline
empty : AssocList k e
empty = AL []

export %inline
singleton : Fin k -> e -> AssocList k e
singleton n v = AL [(n,v)]

export %inline
pairs : AssocList k e -> List (Fin k, e)
pairs = ps

export %inline
mapKV : (Fin k -> e -> b) -> AssocList k e -> AssocList k b
mapKV f (AL r) = AL $ map (\(x,v) => (x, f x v)) r

export %inline
foldlKV : (Fin k -> acc -> e -> acc) -> acc -> AssocList k e -> acc
foldlKV f ini (AL r) = foldl (\v,(x,l) => f x v l) ini r

public export
traverseKV :
     {auto _ : Applicative f}
  -> ((Fin k,e) -> f b)
  -> AssocList k e
  -> f (AssocList k b)
traverseKV f (AL r) = AL <$> traverse (\(n,l) => (n,) <$> f (n,l)) r

||| Lookup a key in an assoc list.
export %inline
lookup : Fin k -> AssocList k e -> Maybe e
lookup k (AL r) = lookupRep k r

||| Checks if an `AssocList` has an entry for the given key.
export %inline
hasKey : AssocList k e -> Fin k -> Bool
hasKey l k = isJust $ lookup k l

export %inline
nonEmpty : AssocList k e -> Bool
nonEmpty (AL []) = False
nonEmpty _       = True

export %inline
isEmpty : AssocList k e -> Bool
isEmpty (AL []) = True
isEmpty _       = False

||| Extracts the keys from the assoc list.
export %inline
keys : AssocList k e -> List (Fin k)
keys = map fst . ps

||| Extracts the values from the assoc list.
export %inline
values : AssocList k e -> List e
values = map snd . ps

export %inline
length : AssocList k e -> Nat
length = length . ps

||| Inserts a new key / value pair into an assoc list.
|||
||| Note: If the given key `k` is already present in the assoc list,
||| its associated value will be replaced with the new value.
export %inline
insert : Fin k -> e -> AssocList k e -> AssocList k e
insert key lbl (AL r) = AL $ insertRep key lbl r

||| Like `insert` but in case `k` is already present in the assoc
||| list, the `v` will be cobine with the old value via function `f`.
export %inline
insertWith :
     (f : e -> e -> e)
  -> Fin k
  -> (v : e)
  -> AssocList k e
  -> AssocList k e
insertWith f x v (AL r) = AL $ insertWithRep f x v r

export
fromList : List (Fin k,e) -> AssocList k e
fromList = foldl (\al,(k,v) => insert k v al) empty

||| Tries to remove the entry with the given key from the
||| assoc list. The key index of the result will be equal to
||| or greater than `m`.
export %inline
delete : Fin k -> AssocList k e -> AssocList k e
delete x (AL r) = AL $ filter ((/= x) . fst) r

||| Applies the given function to all values, keeping only the
||| `Just` results.
export %inline
mapMaybe : (e -> Maybe b) -> AssocList k e -> AssocList k b
mapMaybe f (AL r) = AL $ mapMaybe (\(x,l) => (x,) <$> f l) r

||| Applies the given function to all key / value pairs, keeping only the
||| `Just` results.
export %inline
mapMaybeK : (Fin k -> e -> Maybe b) -> AssocList k e -> AssocList k b
mapMaybeK f (AL r) = AL $ mapMaybe (\(x,l) => (x,) <$> f x l) r

||| Updates the value at the given position by applying the given function.
export %inline
update : Fin k -> (e -> e) -> AssocList k e -> AssocList k e
update k f (AL r) =
  AL $ map (\(x,l) => if k == x then (x, f l) else (x,l)) r

||| Updates the value at the given position by applying the given effectful
||| computation.
export %inline
updateA : Applicative f => Fin k -> (e -> f e) -> AssocList k e -> f (AssocList k e)
updateA k g (AL r) =
  AL <$> traverse (\(x,l) => if k == x then (x,) <$> g l else pure (x,l)) r

||| Computes the union of two assoc lists.
|||
||| In case of identical keys, the value of the second list
||| is dropped. Use `unionWith` for better control over handling
||| duplicate entries.
export %inline
union : AssocList k e -> AssocList k e -> AssocList k e
union (AL r1) (AL r2) = AL $ unionRep r1 r2

||| Like `union` but in case of identical keys appearing in
||| both lists, the associated values are combined using
||| function `f`. Otherwise, values are converted with `g`.
export %inline
unionMap :
     (f : e -> e -> b)
  -> (g : e -> b)
  -> AssocList k e
  -> AssocList k e
  -> AssocList k b
unionMap f g (AL r1) (AL r2) = AL $ unionMapRep f g r1 r2

||| Like `union` but in case of identical keys appearing in
||| both lists, the associated values are combined using
||| function `f`.
export %inline
unionWith : (e -> e -> e) -> AssocList k e -> AssocList k e -> AssocList k e
unionWith f = unionMap f id

||| Computes the intersection of two assoc lists, keeping
||| only entries appearing in both lists. Values of the two
||| lists are combine using function `f`.
export
intersectWith : (e -> e -> b) -> AssocList k e -> AssocList k e -> AssocList k b
intersectWith f (AL r1) (AL r2) = AL $ intersectWithRep f r1 r2

||| Computes the intersection of two assoc lists, keeping
||| only entries appearing in both lists. Only the values of
||| the first list are being kept.
export %inline
intersect : AssocList k e -> AssocList k e -> AssocList k e
intersect = intersectWith const

||| Filter an assoc list via a linear function.
export %inline
filterLin :
     (Fin k -> m -@ CRes Bool m)
  -> AssocList k e
  -> m
  -@ CRes (AssocList k e) m
filterLin f (AL ps) m1 =
  let ps2 # m2 := Mutable.filterLin (\(x,_) => f x) ps m1
   in AL ps2 # m2

||| Using a comparator, find the minimal value and its
||| index in an assoc list.
export %inline
minBy : Ord b => (a -> b) -> AssocList k a -> Maybe (Fin k, a)
minBy _ (AL [])        = Nothing
minBy f (AL $ p :: ps) = Just $ go p (f $ snd p) ps
  where
    go : (Fin k, a) -> b -> List (Fin k, a) -> (Fin k, a)
    go p v [] = p
    go p v (h :: t) =
      let v2 := f (snd h)
       in if v2 < v then go h v2 t else go p v t
