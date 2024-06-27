module RingTest

import Data.Vect
import Data.List
import Data.Bits
import Data.Graph.Indexed
import Text.Smiles.Simple
import Data.Graph.Indexed.Types
import Data.Graph.Indexed.Cycles4
import Data.Graph.Indexed.Ring
import Data.Graph.Indexed.Relevant
import System

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

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

fromList : List Nat -> Integer
fromList = foldl (\x,y => setBit x y) 0

natEdge : {n : Nat} -> (x,y : Nat) -> Maybe (Edge n ())
natEdge x y = join [| mkEdge (tryNatToFin x) (tryNatToFin y) (pure ()) |]

toNext : {n : Nat} -> (x : Nat) -> Maybe (Edge n ())
toNext x = natEdge x (S x)

--------------------------------------------------------------------------------
--          Basic Ring Search Tests
--------------------------------------------------------------------------------

testFusedRing : String -> List (Bool,Integer) -> String
testFusedRing str xs =
  case readSmiles str of
    Nothing  => "invalid SMILES"
    Just x =>
      let ys = map (map value) $ searchAllMA (graph x)
       in if ys == xs then "" else
            "Expected \{pretty xs} but got \{pretty ys}"

--------------------------------------------------------------------------------
--          Ring Sets Testfunctionalities
--------------------------------------------------------------------------------

testCyclomaticNr : String -> Nat -> String
testCyclomaticNr str k =
  case readSmiles str of
    Nothing  => "invalid SMILES"
    Just (G o g) =>
      if computeCyclomaticN g == k
         then ""
         else "Expected \{show k} but got \{show $ computeCyclomaticN g}"

testCiSize : String -> Nat -> String
testCiSize str k =
  case readSmiles str of
    Nothing  => "invalid SMILES"
    Just x =>
      let ci := computeCI' (graph x)
          len := length ci
       in if len == k then "" else
         "Expected \{show k} but got \{show len}"

testCrSize : String -> Nat -> String
testCrSize str k =
  case readSmiles str of
    Nothing  => "invalid SMILES"
    Just x =>
      let cr := cr $ computeCrAndMCB (graph x)
          len := length cr
       in if len == k then "" else
         "Expected \{show k} but got \{show len}"

testMCBSize : String -> Nat -> String
testMCBSize str k =
  case readSmiles str of
    Nothing  => "invalid SMILES"
    Just x =>
      let mcb := mcb $ computeCrAndMCB (graph x)
          len := length mcb
       in if len == k then "" else
         "Expected \{show k} but got \{show len}"

testCrCycles : String -> List (List Nat) -> String
testCrCycles str ks =
  case readSmiles str of
    Nothing  => "invalid SMILES"
    Just x =>
      let cr := map (path . ncycle) $ cr $ computeCrAndMCB (graph x)
          cs := map (map finToNat) cr
       in if cs == ks then "" else
         "Expected \{show ks} but got \{show cs}"

testMCBCycles : String -> List (List Nat) -> String
testMCBCycles str ks =
  case readSmiles str of
    Nothing  => "invalid SMILES"
    Just x =>
      let cr := map (path . ncycle) $ mcb $ computeCrAndMCB (graph x)
          cs := map (map finToNat) cr
       in if cs == ks then "" else
         "Expected \{show ks} but got \{show cs}"

--------------------------------------------------------------------------------
--          Specific Testcases
--------------------------------------------------------------------------------

c60 : Either String (Graph () ())
c60 =
  let s := "C12=C3C4=C5C6=C1C7=C8C9=C1C%10=C%11C(=C29)C3=C2C3=C4C4=C5C5=C9C6=C7C6=C7C8=C1C1=C8C%10=C%10C%11=C2C2=C3C3=C4C4=C5C5=C%11C%12=C(C6=C95)C7=C1C1=C%12C5=C%11C4=C3C3=C5C(=C81)C%10=C23"
   in case readSmiles s of
     Nothing => Left "Invalid Smiles \{show s}"
     Just x  => Right $ bimap (const ()) (const ()) x

c70 : Either String (Graph () ())
c70 =
  let s := "C12=C3C4=C5C6=C7C8=C9C%10=C%11C%12=C%13C%10=C%10C8=C5C1=C%10C1=C%13C5=C8C1=C2C1=C3C2=C3C%10=C%13C%14=C3C1=C8C1=C3C5=C%12C5=C8C%11=C%11C9=C7C7=C9C6=C4C2=C2C%10=C4C(=C29)C2=C6C(=C8C8=C9C6=C4C%13=C9C(=C%141)C3=C85)C%11=C27"
   in case readSmiles s of
     Nothing => Left "Invalid Smiles \{show s}"
     Just x  => Right $ bimap (const ()) (const ()) x

----- a chain of `n` fused cyclohexane rings
chain : (n : Nat) -> IGraph (4*n+2) () ()
chain n =
  let tot := 4*n + 2
   in mkGraph
        (replicate _ ())
        (catMaybes $ map toNext [0..tot] ++ map close [0..n])
  where
    close : Nat -> Maybe (Edge (4*n+2) ())
    close x = natEdge (2 * x) ((4*n+1) `minus` (2*x))

-- an `S m x S n` square grid
grid : (m,n : Nat) -> IGraph (S m * S n) () ()
grid m n =
  mkGraph (replicate _ ()) (ho ++ ve)
  where
    ho, ve : List (Edge (S m * S n) ())
    ho = do
      x <- [0..m]
      y <- [0..S n]
      let p := x + S m * y
      toList $ natEdge p (S p)

    ve = do
      x <- [0..S m]
      y <- [0..n]
      let p := x + S m * y
      toList $ natEdge p (p + S m)

-- previous version
-- a bracelet of `n` fused cyclohexane rings
braceletOld : (n : Nat) -> IGraph (4*n+2) () ()
braceletOld n =
  let tot := 4*n + 2
   in mkGraph
        (replicate _ ())
        (catMaybes $ map toNext [0..tot] ++ map close [0..n] ++ [natEdge 0 (2*n), natEdge (2*n+1) (pred tot)])
  where
    close : Nat -> Maybe (Edge (4*n+2) ())
    close x = natEdge (2 * x) ((4*n+1) `minus` (2*x))

-- a sequence of `n` isolate cyclohexane rings
seq : (n : Nat) -> IGraph (6*n) () ()
seq n =
  mkGraph
    (replicate _ ())
    (catMaybes $ ([0.. pred n] >>= ring . (6*)) ++ map link [0.. pred n])
  where
    ring : Nat -> List (Maybe $ Edge (6*n) ())
    ring k = natEdge k (k+5) :: map (\x => natEdge (k+x) (k+x+1)) [0..4]

    link : Nat -> Maybe (Edge (6*n) ())
    link k = natEdge (k*6 + 3) (k*6 + 6)

-- a bracelet of `n` isolate cyclohexane rings
bracelet : (n : Nat) -> IGraph (6*n) () ()
bracelet n =
  insEdges (catMaybes [natEdge 0 ((6 * n) `minus` 3)]) (seq n)

readGraph : List String -> Either String (Graph () ())
readGraph [ "fullerene" ] = c60
readGraph [ "c60" ]       = c60
readGraph [ "c70" ]       = c70
readGraph ["chain", n]    = Right (G _ $ chain (cast n))
readGraph ["bracelet", n] = Right (G _ $ bracelet (cast n))
readGraph ["bracelet_old", n] = Right (G _ $ braceletOld (cast n))
readGraph ["seq", n]      = Right (G _ $ seq (cast n))
readGraph ["grid", m,n]   = Right (G _ $ grid (cast m) (cast n))
readGraph [s]             =
  case readSmiles s of
    Nothing => Left "Invalid Smiles: \{show s}"
    Just x  => Right $ bimap (const ()) (const ()) x
readGraph ss              = Left "Invalid argss: \{show ss}"

testSetsSize : Graph () () -> String
testSetsSize (G o g) =
  let sets := computeCrAndMCB (graph $ G o g)
      mcb  := length $ mcb sets
      cr   := sum $ map (combos . ncycle) (cr sets)
   in "Length MCB: \{show mcb} length CR: \{show cr}, (order: \{show o}, size: \{show $ length $ edges g})"

run : String -> IO ()
run ""  = putStrLn "Success!"
run str = putStrLn "Failed with an error: \{str}"

run' : String -> IO ()
run' str = putStrLn str

export
main : IO ()
main = do
  _::t <- getArgs | _ => die "Invalid # arguments"
  Right g <- pure $ readGraph t | Left err => putStrLn err
  putStrLn $ testSetsSize g

--- run (testFusedRing "CCCC" [])
--- run (testFusedRing "C1CC1" [(False, fromList [0,1,2])])
--- run (testFusedRing "COCC1CC1" [(False, fromList [3,4,5])])
--- run (testFusedRing "C1CC2CC12" [(True, fromList [0..4])])
--- run (testFusedRing "C1C(CC)C2C(OC)C12" [(True, fromList [0,1,4,5,8])])
--- run (testFusedRing "C1CC2CCCC2CC1" [(True, fromList [0..8])])
--- run (testFusedRing "C1CC2C(CC3CCCCC3)CCC2CC1" [(False, fromList [5..10]), (True, fromList [0,1,2,3,11,12,13,14,15])])
--- run (testFusedRing "C1CCC2(CCCC2)CC1" [(False, fromList [3,4,5,6,7]), (False, fromList [0,1,2,3,8,9])])

---  run (testCrCycles "CCCCC" [])
---  run (testMCBCycles "CCCCC" [])
---  run (testCrSize "CCCCC" 0)
---  run (testCrSize "CCCCC" 0)
---
---  run (testCrSize "C1CC1" 1)
---  run (testMCBSize "C1CC1" 1)
---  run (testCrCycles "C1CC1" [[2,1,0,2]])
---  run (testMCBCycles "C1CC1" [[2,1,0,2]])
---
---  run (testMCBSize "C3CCC2CC1CCCCC1CC2C3" 3)
---  run (testCrSize "C3CCC2CC1CCCCC1CC2C3" 3)
---
---  run (testMCBSize "C1CC2CCC1CC2" 2)
---  run (testCrSize "C1CC2CCC1CC2" 3)
---
---  run (testMCBSize "C1CC2CCC1C3CCCCC23" 3)
---  run (testCrSize "C1CC2CCC1C3CCCCC23" 4)
---
---  run' $ testSetsSize [ "chain", "10" ]
---  run' $ testSetsSize [ "bracelet", "10" ]
---  run' $ testSetsSize ["c60"]
