module Ring.Systems

import Data.Graph.Indexed.Ring.Systems
import Data.List
import Hedgehog
import Test.Data.Graph.Indexed.Generators
import Text.Smiles.Simple

%default total

rsSmiles : String -> (k ** RingSystems k Bond Elem)
rsSmiles s = let G k g := readSmilesOrEmpty s in (k ** ringSystems g)

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
prop_linear = property1 $ nsystems (chain 100000) === 100000

prop_isInRing : Property
prop_isInRing =
  property $ Prelude.do
    n <- forAll (nat $ linear 0 20)
    f <- forAll (fin $ linearFin n)
    let (k ** rs) := rsSmiles (chain $ S n)
    map (isInRing rs) (tryNatToFin $ 4 * cast f) === Just False
    map (isInRing rs) (tryNatToFin $ 1 + 4 * cast f) === Just True
    map (isInRing rs) (tryNatToFin $ 2 + 4 * cast f) === Just True
    map (isInRing rs) (tryNatToFin $ 3 + 4 * cast f) === Just True

prop_inSameRing : Property
prop_inSameRing =
  property $ Prelude.do
    n <- forAll (nat $ linear 0 20)
    x <- forAll (fin $ linearFin n)
    y <- forAll (fin $ linearFin n)
    let (k ** rs) := rsSmiles (chain $ S n)
    [| inSameRing
         (pure rs)
         (tryNatToFin $ 1 + 4 * cast x)
         (tryNatToFin $ 2 + 4 * cast y)
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
