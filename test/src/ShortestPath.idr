module ShortestPath

import Data.Graph.Indexed.Query.ShortestPath
import Data.Graph.Indexed.Subgraph
import Data.List
import Hedgehog
import Test.Data.Graph.Indexed.Generators
import Text.Smiles.Simple

%default total

prettyPath : Path k -> String
prettyPath p =
  "Last: \{show p.last}; Length: \{show p.length}; Combos: \{show p.combos}"

testPaths : String -> IO ()
testPaths s =
 let Just (G _ g) := readSmiles s | Nothing => putStrLn "invalid smiles code"
     G _ s        := toDegs $ subgraphL g (nodes g)
  in for_ (nodes s) $ \n => do
       putStrLn "Root \{show n}"
       for_ (shortestPaths s n) $ \p =>
         putStrLn "  \{prettyPath p}"

rings : Nat -> String
rings n = fastConcat $ replicate n "C(C1)CC1"
