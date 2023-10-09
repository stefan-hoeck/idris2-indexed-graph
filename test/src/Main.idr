module Main

import Debug.Trace
import Data.Vect
import Test.Data.Graph.Indexed.Generators

%default total

saneIGraph : Show e => {k : _} -> IGraph k e n -> Bool
saneIGraph g = all bondsUndirected (contexts g)
  where
    bondUndirected : Fin k -> (Fin k, e) -> Bool
    bondUndirected m (n,_) = neighbours g n `hasKey` m

    bondsUndirected : Context k e n -> Bool
    bondsUndirected (C n _ ns) = all (bondUndirected n) $ pairs ns

u : Gen ()
u = pure ()

sparseUGraph : Gen (Graph () ())
sparseUGraph = sparseGraph (linear 0 20) (linear 0 20) u u

ugraph : Gen (Graph () ())
ugraph = graph (linear 0 20) (element [Nothing, Just ()]) u

prop_saneGraphSparse : Property
prop_saneGraphSparse =
  property $ do
    G _ g <- forAll sparseUGraph
    assert $ saneIGraph g

prop_saneGraph : Property
prop_saneGraph =
  property $ do
    G _ g <- forAll ugraph
    assert $ saneIGraph g

main : IO ()
main =
  test . pure $
    MkGroup "indexed-graph"
      [ ("prop_saneGraphSparse", prop_saneGraphSparse)
      , ("prop_saneGraph", prop_saneGraph)
      ]
