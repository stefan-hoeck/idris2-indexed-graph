module ShortestPath

import Data.Graph.Indexed.Ring.Relevant.Types
import Data.Graph.Indexed.Ring.Relevant.ShortestPath
import Data.List
import Derive.Prelude
import Hedgehog
import Test.Data.Graph.Indexed.Generators
import Text.Smiles.Simple

%default total
%language ElabReflection

record SimplePath  where
  constructor SP
  root   : Nat
  last   : Nat
  length : Nat
  combos : Nat

%runElab derive "SimplePath" [Show,Eq]

toSimplePath : Fin k -> Path k -> SimplePath
toSimplePath r p = SP (cast r) (cast p.last) p.length p.combos

paths : Graph e n -> List SimplePath
paths (G _ g) =
 let G _ s := toDegs $ subgraphL g (nodes g)
  in nodes s >>= \n => toSimplePath n <$> shortestPaths s n

spaths : String -> List SimplePath
spaths = maybe [] paths . readSmiles

prop_ring4 : Property
prop_ring4 = property1 $
  spaths "C1CCC1" === [SP 0 1 2 1, SP 0 3 2 1, SP 1 2 2 1, SP 2 3 2 1]

-- An octahedron
--      _C_
--    /__C__\
--   /       \
--  C----C---C
--   \___C___/
prop_bridged : Property
prop_bridged = property1 $
  spaths "C(C1)(C2)(C3)CC123" ===
    [ SP 0 1 2 1
    , SP 0 2 2 1
    , SP 0 3 2 1
    , SP 0 4 2 1
    , SP 0 5 3 4
    , SP 5 1 2 1
    , SP 5 2 2 1
    , SP 5 3 2 1
    , SP 5 4 2 1
    ]

-- Two octahedrons in succession. There are 16 shortest paths from
-- carbon 1 to carbon 12
--          _C_          _C_
--        /__C__\      /__C__\
--       /       \    /       \
--  C - C----C---C - C----C---C
--       \___C___/    \___C___/
prop_bridged2 : Property
prop_bridged2 = property1 $
  filter ((> 1) . combos) (spaths "CC(C1)(C2)(C3)CC123C(C1)(C2)(C3)CC123") ===
    [ SP 1 6 3 4
    , SP 1 7 4 4
    , SP 1 8 5 4
    , SP 1 9 5 4
    , SP 1 10 5 4
    , SP 1 11 5 4
    , SP 1 12 6 16
    , SP 6 12 4 4
    , SP 7 12 3 4
    ]

export
props : Group
props =
  MkGroup "Data.Graph.Indexed.Query.ShortestPath"
    [ ("prop_ring4", prop_ring4)
    , ("prop_bridged", prop_bridged)
    , ("prop_bridged2", prop_bridged2)
    ]

-- for manual testing at the REPL
testPaths : String -> IO ()
testPaths s =
 let Just g := readSmiles s | Nothing => putStrLn "invalid smiles code"
  in for_ (paths g) printLn
