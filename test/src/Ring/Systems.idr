module Ring.Systems

import Data.Graph.Ring.Systems
import Data.List
import Hedgehog
import Test.Data.Graph.Generators
import Text.Smiles.Simple
import System.Info

%default total

chainSize : Nat
chainSize = if codegen == "node" then 100 else 100000

rsSmiles : String -> DPair SmilesGraph RingSystems
rsSmiles s = let g := readSmilesOrEmpty s in (g ** ringSystems g)

nsystems : String -> Nat
nsystems s = let (_ ** rs) := rsSmiles s in rs.systems

chain : Nat -> String
chain n = fastConcat (replicate n "CC1CC1")

prop_nsystems : Property
prop_nsystems =
  property1 $ Prelude.do
    nsystems "CCO" === 0
    nsystems "C1CCCCC1" === 1
    nsystems "C12CCC2CCCCC1" === 1
    nsystems "C1CC1CCCC1CC1CCCC1CC1" === 3
    nsystems (chain 3) === 3

-- make sure everything runs in linear time
prop_linear : Property
prop_linear = property1 $ nsystems (chain chainSize) === chainSize

prop_isInRing : Property
prop_isInRing =
  property $ Prelude.do
    n <- forAll (nat $ linear 0 20)
    f <- forAll (fin $ linearFin n)
    let (k ** rs) := rsSmiles (chain $ S n)
    map (isInRing rs) (tryNode $ 4 * cast f)     === Just False
    map (isInRing rs) (tryNode $ 1 + 4 * cast f) === Just True
    map (isInRing rs) (tryNode $ 2 + 4 * cast f) === Just True
    map (isInRing rs) (tryNode $ 3 + 4 * cast f) === Just True

prop_inSameRing : Property
prop_inSameRing =
  property $ Prelude.do
    n <- forAll (nat $ linear 0 20)
    x <- forAll (fin $ linearFin n)
    y <- forAll (fin $ linearFin n)
    let (k ** rs) := rsSmiles (chain $ S n)
    [| inSameRing
         (pure rs)
         (tryNode $ 1 + 4 * cast x)
         (tryNode $ 2 + 4 * cast y)
    |] === Just (x == y)

export
props : Group
props =
  MkGroup "Ring.Systems"
    [ ("prop_nsystems", prop_nsystems)
    , ("prop_linear", prop_linear)
    , ("prop_isInRing", prop_isInRing)
    , ("prop_inSameRing", prop_inSameRing)
    ]
