module Visited

import Data.Graph.Indexed.Query.Visited
import Test.Data.Graph.Indexed.Generators

%default total

prop_initUnset : Property
prop_initUnset = property $ do
  k <- forAll (nat $ linear 0 127)
  n <- forAll (anyFin {k})
  assert (test n)

  where
    test : {k : _} -> Fin k -> Bool
    test n =
      visiting k $ \v =>
        let b # v2 := visited n v in done (not b) v2


prop_set : Property
prop_set = property $ do
  k <- forAll (nat $ linear 0 127)
  n <- forAll (anyFin {k})
  assert (test n)

  where
    test : {k : _} -> Fin k -> Bool
    test n =
      visiting k $ \v =>
        let v2     := visit n v
            b # v3 := visited n v2
         in done b v3


export
props : Group
props =
  MkGroup "Visited"
    [ ("prop_initUnset", prop_initUnset)
    , ("prop_set", prop_set)
    ]
