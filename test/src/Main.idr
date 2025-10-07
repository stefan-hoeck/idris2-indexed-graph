module Main

import AssocList
import BFS
import DFS
import Hedgehog
import Ring.Bonds
import Ring.Util as RU
import ShortestPath
import SubgraphIso
import Subgraphs
import Util as U
import Visited

%default total

main : IO ()
main =
  test
    [ AssocList.props
    , BFS.props
    , DFS.props
    , Ring.Bonds.props
    , RU.props
    , SubgraphIso.props
    , Subgraphs.props
    , U.props
    , Visited.props
    , ShortestPath.props
    ]
