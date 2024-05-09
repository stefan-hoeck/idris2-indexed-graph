module RingTest

import Data.Bits
import Text.Smiles
import Data.Graph.Indexed.Types
import Data.Graph.Indexed.Cycles4
import Data.Graph.Indexed.Ring
import Data.Graph.Indexed.Relevant

prettyInteger : Integer -> String
prettyInteger = go [<] 0
  where
    go : SnocList Nat -> Nat -> Integer -> String
    go sn n 0 = show (sn <>> [])
    go sn n x =
      if testBit x 0
         then go (sn :< n) (S n) (shiftR x 1)
         else go sn (S n) (shiftR x 1)

pretty : List (Bool,Integer) -> String
pretty = show . map (map prettyInteger)

testFusedRing : String -> List (Bool,Integer) -> String
testFusedRing str xs =
  case readSmiles' str of
    Left x  => x
    Right x =>
      let ys = map (map value) $ searchAllMA (graph x)
       in if ys == xs then "" else
            "Expected \{pretty xs} but got \{pretty ys}"

fromList : List Nat -> Integer
fromList = foldl (\x,y => setBit x y) 0

testCrCycles : String -> List (List Nat) -> String
testCrCycles str ks =
  case readSmiles' str of
    Left x  => x
    Right x =>
      let cr := map ncycle $ cr $ computeCrAndMCB (graph x)
          cs := map (map finToNat) cr
       in if cs == ks then "" else
         "Expected \{show ks} but got \{show cs}"

testMCBCycles : String -> List (List Nat) -> String
testMCBCycles str ks =
  case readSmiles' str of
    Left x  => x
    Right x =>
      let cr := map ncycle $ mcb $ computeCrAndMCB (graph x)
          cs := map (map finToNat) cr
       in if cs == ks then "" else
         "Expected \{show ks} but got \{show cs}"

testCrSize : String -> Nat -> String
testCrSize str k =
  case readSmiles' str of
    Left x  => x
    Right x =>
      let cr := cr $ computeCrAndMCB (graph x)
          len := length cr
       in if len == k then "" else
         "Expected \{show k} but got \{show len}"

testMCBSize : String -> Nat -> String
testMCBSize str k =
  case readSmiles' str of
    Left x  => x
    Right x =>
      let mcb := mcb $ computeCrAndMCB (graph x)
          len := length mcb
       in if len == k then "" else
         "Expected \{show k} but got \{show len}"

run : String -> IO ()
run ""  = putStrLn "Success!"
run str = putStrLn "Failed with an error: \{str}"

export
main : IO ()
main = do
--- run (testFusedRing "CCCC" [])
--- run (testFusedRing "C1CC1" [(False, fromList [0,1,2])])
--- run (testFusedRing "COCC1CC1" [(False, fromList [3,4,5])])
--- run (testFusedRing "C1CC2CC12" [(True, fromList [0..4])])
--- run (testFusedRing "C1C(CC)C2C(OC)C12" [(True, fromList [0,1,4,5,8])])
--- run (testFusedRing "C1CC2CCCC2CC1" [(True, fromList [0..8])])
--- run (testFusedRing "C1CC2C(CC3CCCCC3)CCC2CC1" [(False, fromList [5..10]), (True, fromList [0,1,2,3,11,12,13,14,15])])
--- run (testFusedRing "C1CCC2(CCCC2)CC1" [(False, fromList [3,4,5,6,7]), (False, fromList [0,1,2,3,8,9])])
  run (testCrCycles "CCCCC" [])
