module Main

import Test.Data.Graph.Indexed.Generators

%default total

saneIGraph : {k : _} -> IGraph k e n -> Bool
saneIGraph g = all bondsUndirected (contexts g)
  where
    bondUndirected : Fin k -> (Fin k, e) -> Bool
    bondUndirected m (n,_) = neighbours g n `hasKey` m

    bondsUndirected : Context k e n -> Bool
    bondsUndirected (C n _ ns) = all (bondUndirected n) $ pairs ns

u : Gen ()
u = pure ()

prop_saneGraphSparse : Property
prop_saneGraphSparse =
  property $ do
    G _ g <- forAll $ sparseGraph (linear 0 20) (linear 0 20) u u
    assert $ saneIGraph g

main : IO ()
main = putStrLn "Hello indexed graph test"
