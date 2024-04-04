module SubgraphIso

import Data.Graph.Indexed.Query.Subgraph
import Data.Vect
import Test.Data.Graph.Indexed.Generators
import Text.Smiles.Simple

testQuery : String -> String -> Maybe (List Nat) -> Property
testQuery x y vs = property1 $ test === Just vs
  where
    test : Maybe (Maybe $ List Nat)
    test = do
      G o1 g1 <- readSmiles x
      G o2 g2 <- readSmiles y
      pure $ toList . map finToNat <$> query (==) (==) g1 g2

prop_ethanol : Property
prop_ethanol = testQuery "CCO" "CCCCO" (Just [2,3,4])

prop_acid : Property
prop_acid = testQuery "C(O)=O" "CCC(C(=O)O)CCC" (Just [3,5,4])

prop_nitrile : Property
prop_nitrile =
  testQuery "C(C)(F)C#N" "C1CC(CC(C#N)F)CC1" $ Just [4,3,7,5,6]
          -- 0 1  2 3 4   0 12 34 5 6 7

prop_amine : Property
prop_amine =
  testQuery "C(C12)N3C1.C2.C3" "O=C(CCC=1C=CC=CC=1)N1CCC1C=1C=CC=CC=1" Nothing

prop_amine2 : Property
prop_amine2 =
  testQuery "CN(C)C" "C1NC1" $ Nothing

export
props : Group
props =
  MkGroup "Query.Subgraph"
    [ ("prop_ethanol", prop_ethanol)
    , ("prop_acid", prop_acid)
    , ("prop_nitrile", prop_nitrile)
    , ("prop_amine", prop_amine)
    , ("prop_amine2", prop_amine2)
    ]
