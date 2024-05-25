module Ring.Util

import Data.Graph.Indexed.Ring.Util
import Data.List
import Data.SortedSet
import Test.Data.Graph.Indexed.Generators
import Text.Smiles.Simple

%default total

ring3Test : String -> List Nat -> Property
ring3Test s ns =
  property1 $ assert $ case readSmiles s of
    Nothing      => False
    Just (G o g) =>
      sort (map cast $ filter (inThreeMemberedRing g) (nodes g)) == ns

export
props : Group
props =
  MkGroup "Ring.Util"
    [ ("prop_ethanol", ring3Test "CCO" [])
    , ("prop_benzene", ring3Test "C1=CC=CC=C1" [])
    , ("prop_bicycle", ring3Test "C12CC1CC2" [0,1,2])
    , ("prop_disconnected", ring3Test "CC.C1OC1.C1CCC1" [2,3,4])
    ]
