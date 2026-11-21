module Visited

import Data.Graph.Indexed.Query.Visited
import Test.Data.Graph.Indexed.Generators

%default total

gr : Gen (Graph () ())
gr = graph (linear 1 127) (maybe $ pure ()) (pure ())

prop_minitUnset : Property
prop_minitUnset = property $ do
  g <- forAll gr
  n <- forNode g
  assert (test n)

  where
    test : {g : _} -> Node g -> Bool
    test n = visiting g $ \r,t => mapR1 not (mvisited r n t)

prop_iniUnset : Property
prop_iniUnset = property $ do
  g <- forAll gr
  n <- forNode g
  assert (not $ visited n ini)

prop_mset : Property
prop_mset = property $ do
  g <- forAll gr
  n <- forNode g
  assert (test n)

  where
    test : {g : _} -> Node g -> Bool
    test n = visiting g $ \r,t => let _ # t := mvisit r n t in mvisited r n t

prop_set : Property
prop_set = property $ do
  g <- forAll gr
  n <- forNode g
  assert (visited n $ visit n ini)

export
props : Group
props =
  MkGroup "Visited"
    [ ("prop_minitUnset", prop_minitUnset)
    , ("prop_mset", prop_mset)
    , ("prop_iniUnset", prop_iniUnset)
    , ("prop_set", prop_set)
    ]
