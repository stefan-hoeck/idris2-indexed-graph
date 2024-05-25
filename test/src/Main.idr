module Main

import AssocList
import BFS
import DFS
import Hedgehog
import Ring.Bonds
import SubgraphIso
import Subgraphs
import Util
import Visited

%default total

main : IO ()
main =
  test
    [ AssocList.props
    , BFS.props
    , DFS.props
    , Ring.Bonds.props
    , SubgraphIso.props
    , Subgraphs.props
    , Util.props
    , Visited.props
    ]
