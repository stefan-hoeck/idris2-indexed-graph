module RingTest

import Data.Bits
import Text.Smiles
import Data.Graph.Indexed.Types
import Data.Graph.Indexed.Cycles4

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
            "Expected \{pretty ys} but got \{pretty xs}"

run : String -> IO ()
run ""  = putStrLn "Success!"
run str = putStrLn "Failed with an error: \{str}"

fromList : List Nat -> Integer
fromList = foldl (\x,y => setBit x y) 0

export
main : IO ()
main = do
  run (testFusedRing "CCC" [])
  run (testFusedRing "C1CC1" [(False, fromList [0,1,2])])
  run (testFusedRing "COCCC1CC1" [(False, fromList [4,5,7])])
  run (testFusedRing "C1CC2CC12" [(True, fromList [0..4])])
  run (testFusedRing "C1C(CC)C2C(OC)C12" [(True, fromList [0,1,4,5,8])])

