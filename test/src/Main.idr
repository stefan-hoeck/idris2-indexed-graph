module Main

import AssocList
import BFS
import Hedgehog
import Subgraphs
import Visited

%default total

main : IO ()
main =
  test
    [ AssocList.props
    , Visited.props
    , Subgraphs.props
    , BFS.props
    ]
