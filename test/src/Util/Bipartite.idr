module Util.Bipartite

import Data.Graph.Indexed.Util.Bipartite
import Data.List
import Hedgehog
import Syntax.T1
import Test.Data.Graph.Indexed.Generators
import Text.Smiles.Simple

%default total

testBipartite : {k : _} -> IGraph k e n -> IArray k Bool -> Bool
testBipartite g cs = all (\(E x y _) => at cs x /= at cs y) (edges g)

prop_bipartite : Property
prop_bipartite =
  property $ do
    G _ g <- forAll $ sparseGraph (linear 0 20) (linear 0 30) unit unit
    case bipartite g of
      Nothing => pure ()
      Just cs => assert (testBipartite g cs)

isEven : Nat -> Bool
isEven n = prim__and_Integer 1 (cast n) == 0

prop_bipartiteRing : Property
prop_bipartiteRing =
  property $ do
    G o g <- forAll rings'
    isJust (bipartite g) === isEven o

export
props : Group
props =
  MkGroup "Bipartite"
    [ ("prop_bipartite", prop_bipartite)
    , ("prop_bipartiteRing", prop_bipartiteRing)
    ]
