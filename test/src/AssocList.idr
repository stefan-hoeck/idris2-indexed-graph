module AssocList

import Data.SOP
import Test.Data.Graph.Indexed.Generators

%default total

assocList10 : Gen (AssocList 10 Bits8)
assocList10 = assocList anyBits8

fin10 : Gen (Fin 10)
fin10 = anyFin

prop_fromPairs : Property
prop_fromPairs = property $ do
  al <- forAll assocList10
  al === fromList (pairs al)

prop_singleton : Property
prop_singleton = property $ do
  [n,v] <- forAll $ np [fin10, anyBits8]
  [(n,v)] === pairs (singleton n v)

prop_singleton_lookup : Property
prop_singleton_lookup = property $ do
  [n,v] <- forAll $ np [fin10, anyBits8]
  Just v === lookup n (singleton n v)

prop_insert : Property
prop_insert = property $ do
  [al,n,v] <- forAll $ np [assocList10, fin10, anyBits8]
  let al2 := insert n v al
  assert $ nonEmpty al2
  assert $ not (isEmpty al2)
  assert $ hasKey al2 n
  Just v === lookup n (insert n v al)

prop_insertWith : Property
prop_insertWith = property $ do
  [al,n,v1,v2] <- forAll $ np [assocList10, fin10, anyBits8, anyBits8]
  Just (v1 + v2) === lookup n (insertWith (+) n v2 $ insert n v1 al)

prop_delete : Property
prop_delete = property $ do
  [al,n] <- forAll $ np [assocList10, fin10]
  Nothing === lookup n (delete n al)

prop_mapMaybe_Just : Property
prop_mapMaybe_Just = property $ do
  al <- forAll assocList10
  al === mapMaybe Just al

prop_mapMaybe_Nothing : Property
prop_mapMaybe_Nothing = property $ do
  al <- forAll assocList10
  empty === mapMaybe {b = Bits8} (const Nothing) al

prop_update : Property
prop_update = property $ do
  [al,n] <- forAll $ np [assocList10, fin10]
  map (2*) (lookup n al) === lookup n (update n (2*) al)

prop_union_self : Property
prop_union_self = property $ do
  al <- forAll assocList10
  al === union al al

prop_union_empty : Property
prop_union_empty = property $ do
  al <- forAll assocList10
  al === union empty al

export
props : Group
props =
  MkGroup "AssocList"
    [ ("prop_fromPairs", prop_fromPairs)
    , ("prop_singleton", prop_singleton)
    , ("prop_singleton_lookup", prop_singleton_lookup)
    , ("prop_insert", prop_insert)
    , ("prop_insertWith", prop_insertWith)
    , ("prop_delete", prop_delete)
    , ("prop_mapMaybe_Just", prop_mapMaybe_Just)
    , ("prop_mapMaybe_Nothing", prop_mapMaybe_Nothing)
    , ("prop_update", prop_update)
    , ("prop_union_self", prop_union_self)
    , ("prop_union_empty", prop_union_empty)
    ]
