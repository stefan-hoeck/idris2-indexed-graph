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

testMatch : String -> Maybe (Array $ Maybe Nat)
testMatch s =
 let G k g := readSmilesOrEmpty s
  in A k <$> (map . map . map) finToNat (match g)

prop_match : Property
prop_match =
  property1 $ Prelude.do
    testMatch "CCC(CC(CC)(C)CCC)CCCC" ===
      Just (Array.fromList
        [ Just 1, Just 0, Just 3, Just 2, Just 7, Just 6
        , Just 5, Just 4, Just 9, Just 8, Nothing
        , Just 12, Just 11, Just 14, Just 13])
    testMatch "C1CCCCC1" ===
      Just (Array.fromList [Just 1, Just 0, Just 3, Just 2, Just 5, Just 4])
    testMatch "C1CC(C)CCC1C" ===
      Just (Array.fromList [Just 1, Just 0, Just 3, Just 2, Just 5, Just 4, Just 7, Just 6])

export
props : Group
props =
  MkGroup "Bipartite"
    [ ("prop_bipartite", prop_bipartite)
    , ("prop_bipartiteRing", prop_bipartiteRing)
    , ("prop_match", prop_match)
    ]
