module Main

import AssocList
import BFS
import Hedgehog
import Subgraphs
import Util
import Visited

%default total

main : IO ()
main =
  test
    [ AssocList.props
    , Util.props
    , Visited.props
    , Subgraphs.props
    , BFS.props
    ]
