module Main

import AssocList
import Graph
import Hedgehog

%default total

main : IO ()
main =
  test
    [ AssocList.props
    , Graph.props
    ]
