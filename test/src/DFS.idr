module DFS

import Data.Graph.Indexed.Query.DFS
import Test.Data.Graph.Indexed.Generators
import Text.Smiles.Simple
import Data.SnocList

%default total


--------------------------------------------------------------------------------
-- Example Graphs
--------------------------------------------------------------------------------

benzylbenzoate : Graph Bond Elem
benzylbenzoate = readSmilesOrEmpty "C1=CC=C(C=C1)COC(=O)C2=CC=CC=C2"

-- create a list with all nodes reachable from the start node and ignoring
-- taboo nodes and their branches
limitedDfsWithTest :
     (taboo : List Nat)
  -> Graph e n
  -> (start : Nat)
  -> List Nat
  -> Bool
limitedDfsWithTest ts g s ns =
  let Just b := tryNode s | Nothing => False
      tsn    := mapMaybe tryNode ts
   in map cast (limitedDfs g tsn b <>> []) == ns

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

prop_benzylbenzoate0_6 : Property
prop_benzylbenzoate0_6 =
  property1 $ assert $
    limitedDfsWithTest [6] benzylbenzoate 0 [0..5]

prop_benzylbenzoate3_6 : Property
prop_benzylbenzoate3_6 =
  property1 $ assert $
    limitedDfsWithTest [3] benzylbenzoate 6 [6..15]

prop_benzylbenzoate3'10_6 : Property
prop_benzylbenzoate3'10_6 =
  property1 $ assert $
    limitedDfsWithTest [3,10] benzylbenzoate 6 [6..9]

export
props : Group
props =
  MkGroup "DFS"
    [ ("prop_benzylbenzoate0_6", prop_benzylbenzoate0_6)
    , ("prop_benzylbenzoate3_6", prop_benzylbenzoate3_6)
    , ("prop_benzylbenzoate3'10_6", prop_benzylbenzoate3'10_6)
    ]
