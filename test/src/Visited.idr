module Visited

import Data.Graph.Indexed.Query.Visited
import Test.Data.Graph.Indexed.Generators

%default total

prop_minitUnset : Property
prop_minitUnset = property $ do
  k <- forAll (nat $ linear 0 127)
  n <- forAll (anyFin {k})
  assert (test n)

  where
    test : {k : _} -> Fin k -> Bool
    test n = visiting k $ \r,t => mapR1 not (mvisited r n t)

prop_iniUnset : Property
prop_iniUnset = property $ do
  k <- forAll (nat $ linear 0 127)
  n <- forAll (anyFin {k})
  assert (not $ visited n ini)

prop_mset : Property
prop_mset = property $ do
  k <- forAll (nat $ linear 0 127)
  n <- forAll (anyFin {k})
  assert (test n)

  where
    test : {k : _} -> Fin k -> Bool
    test n = visiting k $ \r,t => mvisited r n (mvisit r n t)

prop_set : Property
prop_set = property $ do
  k <- forAll (nat $ linear 0 127)
  n <- forAll (anyFin {k})
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
