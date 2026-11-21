module Util.DisjointSet

import Data.Graph.Indexed.Util.DisjointSet
import Data.Graph.Indexed.Subgraph
import Data.Linear.Token
import Data.Linear.Traverse1
import Data.List
import Hedgehog
import Syntax.T1
import Test.Data.Graph.Indexed.Generators
import Text.Smiles.Simple

%default total

disjointSet : Graph e n -> List (List Nat)
disjointSet g =
  run1 $ T1.do
    d <- ds g.order
    for1_ (edges g) $ \(E x y _) => union d x y
    ss <- sets d
    pure $ sort (map finToNat <$> ss)

sortedComponents : Graph e n -> List (List Nat)
sortedComponents g =
     connectedComponents g
  |> map (\h => sort . map cast $ labels h)
  |> sort

prop_disjointSet : Property
prop_disjointSet =
  property $ do
    g <- forAll $ sparseGraph (linear 0 20) (linear 0 30) unit unit
    disjointSet g === sortedComponents g

export
props : Group
props =
  MkGroup "DisjointSet"
    [ ("prop_disjointSet", prop_disjointSet) ]
