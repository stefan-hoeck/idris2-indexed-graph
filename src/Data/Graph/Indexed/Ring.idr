module Data.Graph.Indexed.Ring

import Data.Bits
import Data.Fin
import Data.Graph.Indexed.Types

public export
record Ring k where
  constructor R
  value : Integer

export
inRing : Fin k -> Ring k -> Bool
inRing v ring = testBit ring.value $ finToNat v

export
{k : _} -> Show (Ring k) where
  show r = show $ filter (`inRing` r) (allFinsFast k)

export
{k : _} -> Eq (Ring k) where
  r1 == r2 = (value r1) == (value r2)

export
Semigroup (Ring k) where
  (<+>) r1 r2 = R (xor r1.value r2.value)

export
Monoid (Ring k) where
  neutral = R 0

