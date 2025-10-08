module RelevantCycles

import Data.List.Quantifiers
import Data.Graph.Indexed.Ring.Relevant
import Derive.Prelude
import Hedgehog
import ShortestPath
import Test.Data.Graph.Indexed.Generators
import Text.Smiles.Simple

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

record Sizes where
  constructor SS
  relevantFamilies : Nat
  relevantTotal    : Nat
  mcb              : Nat

%runElab derive "Sizes" [Show,Eq]

natEdge : {n : Nat} -> (x,y : Nat) -> Maybe (Edge n ())
natEdge x y = join [| mkEdge (tryNatToFin x) (tryNatToFin y) (pure ()) |]

toNext : {n : Nat} -> (x : Nat) -> Maybe (Edge n ())
toNext x = natEdge x (S x)

crSize : Graph e n -> Sizes
crSize (G _ g) =
 let CS cr mcb := computeCrAndMCB g
  in SS (length cr) (sum $ (combos . ncycle) <$> cr) (length mcb)

crSizeSmiles : String -> Sizes
crSizeSmiles = crSize . readSmilesOrEmpty

prop_cyclomaticChain : Property
prop_cyclomaticChain =
  property $ do
    G _ g <- forAll chains'
    computeCyclomaticN g === 0

prop_cyclesChain : Property
prop_cyclesChain =
  property $ do
    g <- forAll chains'
    crSize g === SS 0 0 0

prop_cyclomaticTree : Property
prop_cyclomaticTree =
  property $ do
    G _ g <- forAll trees'
    computeCyclomaticN g === 0

prop_cyclesTree : Property
prop_cyclesTree =
  property $ do
    g <- forAll trees'
    crSize g === SS 0 0 0

prop_cyclomaticRing : Property
prop_cyclomaticRing =
  property $ do
    G _ g <- forAll rings'
    computeCyclomaticN g === 1

prop_cyclesRing : Property
prop_cyclesRing =
  property $ do
    g <- forAll rings'
    crSize g === SS 1 1 1

prop_cyclomaticDiamond : Property
prop_cyclomaticDiamond =
  property $ do
    [chainLength,nchains] <- forAll $ hlist [nat (linear 1 10), nat (linear 1 10)]
    let G _ g := diamond chainLength nchains
    footnote (pretty (const "()") (const "()") g)
    computeCyclomaticN g === pred nchains

-- A "diamond" of `n` chains consists of to nodes connected via
-- `n` chains. This means, that such a diamond has a cyclomatic number
-- or `n-1` but `sum n = n * (n-1) / 2` relevant cycles.
-- A diamond of 4 chains of length n corresponds to
-- the molecule "[n.n.n.n]paddelane".
diamondCrSize : Nat -> Nat
diamondCrSize n =
 let i := cast {to = Integer} n
  in cast $ (i * (i-1)) `div` 2

prop_cyclesDiamond : Property
prop_cyclesDiamond =
  property $ do
    [chainLength,nchains] <- forAll $ hlist [nat (linear 1 5), nat (linear 1 30)]
    let G _ g := diamond chainLength nchains
    footnote (pretty (const "()") (const "()") g)
    let ds := diamondCrSize nchains
    crSize (G _ g) === SS ds ds (pred nchains)

prop_cycle : Property
prop_cycle = property1 $ crSizeSmiles "C1CC2CCC1C3CCCCC23" === SS 4 4 3

prop_c60 : Property
prop_c60 =
  property1 $
        crSizeSmiles "C12=C3C4=C5C6=C1C7=C8C9=C1C%10=C%11C(=C29)C3=C2C3=C4C4=C5C5=C9C6=C7C6=C7C8=C1C1=C8C%10=C%10C%11=C2C2=C3C3=C4C4=C5C5=C%11C%12=C(C6=C95)C7=C1C1=C%12C5=C%11C4=C3C3=C5C(=C81)C%10=C23"
    === SS 32 32 31

prop_c70 : Property
prop_c70 =
  property1 $
        crSizeSmiles "C12=C3C4=C5C6=C7C8=C9C%10=C%11C%12=C%13C%10=C%10C8=C5C1=C%10C1=C%13C5=C8C1=C2C1=C3C2=C3C%10=C%13C%14=C3C1=C8C1=C3C5=C%12C5=C8C%11=C%11C9=C7C7=C9C6=C4C2=C2C%10=C4C(=C29)C2=C6C(=C8C8=C9C6=C4C%13=C9C(=C%141)C3=C85)C%11=C27"
    === SS 37 37 36

--------------------------------------------------------------------------------
--          Ring Sets Testfunctionalities
--------------------------------------------------------------------------------


-- -- an `S m x S n` square grid
-- grid : (m,n : Nat) -> IGraph (S m * S n) () ()
-- grid m n =
--   mkGraph (replicate _ ()) (ho ++ ve)
--   where
--     ho, ve : List (Edge (S m * S n) ())
--     ho = do
--       x <- [0..m]
--       y <- [0..S n]
--       let p := x + S m * y
--       toList $ natEdge p (S p)
--
--     ve = do
--       x <- [0..S m]
--       y <- [0..n]
--       let p := x + S m * y
--       toList $ natEdge p (p + S m)

export
props : Group
props =
  MkGroup "Data.Graph.Indexed.Ring.Relevant"
    [ ("prop_cyclomaticChain", prop_cyclomaticChain)
    , ("prop_cyclomaticTree", prop_cyclomaticTree)
    , ("prop_cyclomaticRing", prop_cyclomaticRing)
    , ("prop_cyclomaticDiamond", prop_cyclomaticDiamond)
    , ("prop_cyclesChain", prop_cyclesChain)
    , ("prop_cyclesTree", prop_cyclesTree)
    , ("prop_cyclesRing", prop_cyclesRing)
    , ("prop_cyclesDiamond", prop_cyclesDiamond)
    , ("prop_c60", prop_c60)
    , ("prop_c70", prop_c70)
    , ("prop_cycle", prop_cycle)
    ]
