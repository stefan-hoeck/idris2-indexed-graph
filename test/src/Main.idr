module Main

import AssocList
import Hedgehog

%default total

main : IO ()
main =
  test
    [ AssocList.props
    ]
