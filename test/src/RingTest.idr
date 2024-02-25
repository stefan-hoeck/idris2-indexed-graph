module RingTest

import Text.Smiles.Parser
import Text.Smiles.Types
import Data.Graph.Indexed.Types
import Data.Graph.Indexed.Cycles4

testFusedRing : String -> List (Bool, Ring k) -> Either String Bool
testFusedRing str xs =
  case readSmiles' str of
    Left x  => Left x
    Right x =>
      let ys = searchAllMA (graph x)
       in ?foo ---Right (ys == xs)

