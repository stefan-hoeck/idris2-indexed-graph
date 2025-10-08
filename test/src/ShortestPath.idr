module ShortestPath

import Data.Graph.Indexed.Ring.Relevant.ShortestPath
import Data.Graph.Indexed.Ring.Relevant.Types
import Data.List
import Data.List.Quantifiers
import Data.SortedSet as SS
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

valid : Path k -> Path k -> Bool
valid p q = p.first == q.first || disjoint (p.path <>> []) (q.path <>> [])
  where
    disjoint : List (Fin k) -> List (Fin k) -> Bool
    disjoint (_::xs) (_::ys) =
      intersection (SS.fromList xs) (SS.fromList ys) == SS.empty
    disjoint _ _ = True

toSimplePath : Fin k -> Path k -> SimplePath
toSimplePath r p = SP (cast r) (cast p.last) p.length p.combos

paths : Graph e n -> List SimplePath
paths (G _ g) =
 let G _ s := toDegs $ subgraphL g (nodes g)
  in nodes s >>= \n => toSimplePath n <$> shortestPaths s n

spaths : String -> List SimplePath
spaths = paths . readSmilesOrEmpty

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

testDisjoint : List (Path k) -> PropertyT ()
testDisjoint []        = pure ()
testDisjoint (x :: xs) = do
  for_ xs $ \y => do
    footnote (show x)
    footnote (show y)
    assert (valid x y)
  testDisjoint xs

prop_validDiamond : Property
prop_validDiamond =
  property $ do
   [cl,nc] <- forAll $ hlist [nat (linear 1 5), nat (linear 1 10)]
   let G _ g := diamond cl nc
       G _ s := toDegs $ subgraphL g (nodes g)
   footnote (pretty (const "()") (const "()") g)
   for_ (nodes s) (\n => testDisjoint $ shortestPaths s n)

prop_validDiamondChain : Property
prop_validDiamondChain =
  property $ do
   [nd,cl,nc] <- forAll $ hlist [nat (linear 2 4), nat (linear 1 3), nat (linear 1 4)]
   let G _ g := diamondChain nd cl nc
       G _ s := toDegs $ subgraphL g (nodes g)
   footnote (pretty (const "()") (const "()") g)
   for_ (nodes s) (\n => testDisjoint $ shortestPaths s n)

prop_validDiamondBracelet : Property
prop_validDiamondBracelet =
  property $ do
   [nd,cl,nc] <- forAll $ hlist [nat (linear 2 4), nat (linear 1 3), nat (linear 1 4)]
   let G _ g := diamondBracelet nd cl nc
       G _ s := toDegs $ subgraphL g (nodes g)
   footnote (pretty (const "()") (const "()") g)
   for_ (nodes s) (\n => testDisjoint $ shortestPaths s n)

export
props : Group
props =
  MkGroup "Data.Graph.Indexed.Query.ShortestPath"
    [ ("prop_ring4", prop_ring4)
    , ("prop_bridged", prop_bridged)
    , ("prop_bridged2", prop_bridged2)
    , ("prop_validDiamond", prop_validDiamond)
    , ("prop_validDiamondChain", prop_validDiamondChain)
    , ("prop_validDiamondBracelet", prop_validDiamondBracelet)
    ]

-- for manual testing at the REPL
testPaths : String -> IO ()
testPaths s =
 let Just g := readSmiles s | Nothing => putStrLn "invalid smiles code"
  in for_ (paths g) printLn
