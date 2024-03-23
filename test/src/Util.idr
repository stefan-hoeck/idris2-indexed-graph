module Util

import Data.AssocList.Indexed
import Test.Data.Graph.Indexed.Generators

%default total

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

smallGraphs : Gen (Graph Bits8 Bits8)
smallGraphs = sparseGraph (linear 0 30) (linear 0 100) anyBits8 anyBits8

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

testEdgesTo : Eq e => IGraph k e n -> Fin k -> Bool
testEdgesTo g n =
  let vs := values $ neighbours (adj g n)
   in vs == map label (edgesTo g n)

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

prop_edgesTo : Property
prop_edgesTo = property $ do
  G o g <- forAll smallGraphs
  assert $ all (testEdgesTo g) (nodes g)

export
props : Group
props =
  MkGroup "Util"
    [ ("prop_edgesTo", prop_edgesTo)
    ]
