module Main

import AssocList
import Hedgehog
import Visited

%default total

main : IO ()
main =
  test
    [ AssocList.props
    , Visited.props
    ]
