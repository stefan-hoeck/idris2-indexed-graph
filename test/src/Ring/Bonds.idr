module Ring.Bonds

import Data.Graph.Indexed.Ring.Bonds
import Data.Graph.Indexed.Ring.Util
import Data.SortedSet
import Test.Data.Graph.Indexed.Generators
import Text.Smiles.Simple

%default total

toEdge : {o : _} -> (Nat, Nat) -> Maybe (Edge o ())
toEdge (x,y) = do
  fx <- tryNatToFin x
  fy <- tryNatToFin y
  mkEdge fx fy ()

rbTest : String -> List (Nat,Nat) -> Property
rbTest s ps =
  property1 $ assert $ case readSmiles s of
    Nothing => False
    Just (G o g) => ringBonds g == toEdgeSet ps

prop_ethanol : Property
prop_ethanol = rbTest "CCO" []

prop_benzene : Property
prop_benzene =
  rbTest "C1=CC=CC=C1" [(0,1),(1,2),(2,3),(3,4),(4,5),(0,5)]

prop_bicycle : Property
prop_bicycle =
  rbTest "C12CC1CC2" [(0,1),(0,2),(0,4),(1,2),(2,3),(3,4)]

prop_disconnected : Property
prop_disconnected =
  rbTest "C1CC1.C1CCC1" [(0,1),(0,2),(1,2),(3,4),(4,5),(5,6),(3,6)]

export
props : Group
props =
  MkGroup "Ring.Bonds"
    [ ("prop_ethanol", prop_ethanol)
    , ("prop_benzene", prop_benzene)
    , ("prop_bicycle", prop_bicycle)
    , ("prop_disconnected", prop_disconnected)
    ]
