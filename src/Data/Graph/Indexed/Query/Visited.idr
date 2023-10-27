module Data.Graph.Indexed.Query.Visited

import Data.Bits
import Data.Buffer
import public Data.Array.Mutable

%default total

--------------------------------------------------------------------------------
--          FFI
--------------------------------------------------------------------------------

%foreign "scheme:blodwen-buffer-getbyte"
         "node:lambda:(buf,offset)=>buf.readUInt8(Number(offset))"
prim__getByte : Buffer -> (offset : Integer) -> Bits8

%foreign "scheme:blodwen-buffer-setbyte"
         "node:lambda:(buf,offset,value)=>buf.writeUInt8(value, Number(offset))"
prim__setByte : Buffer -> (offset : Integer) -> (val : Bits8) -> PrimIO ()

%foreign "scheme:blodwen-new-buffer"
         "node:lambda:s=>Buffer.alloc(s)"
prim__newBuf : Bits32 -> Buffer

destroy : (1 _ : %World) -> a -> a
destroy %MkWorld x = x

set' : (m : Integer) -> Bits8 -> Buffer -> Buffer
set' m y b =
  let MkIORes () w2 := prim__setByte b m y %MkWorld
   in destroy w2 b

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

-- the first three bits set to 1
%inline mask : Bits8
mask = 7

-- number of bits in 8
%inline bits : Nat
bits = 3

%inline ix : Fin k -> Integer
ix n = cast n `shiftR` bits

%inline bit : Fin k -> Bits8
bit n = cast (finToNat n) .&. mask

%inline setBit : Bits8 -> Fin k -> Bits8
setBit v i = v .|. prim__shl_Bits8 1 (bit i)

testBit : Bits8 -> Fin k -> Bool
testBit x b =
  case x .&. prim__shl_Bits8 1 (bit b) of
    0 => False
    _ => True

--------------------------------------------------------------------------------
--          MVisited
--------------------------------------------------------------------------------

||| Wraps a mutable byte array for keeping track of the visited nodes
||| in a graph.
export
record MVisited (k : Nat) where
  constructor MV
  buf : Buffer

||| Set the current node to "visited".
export
visit : Fin k -> MVisited k -@ MVisited k
visit i (MV b) =
  let o   := ix i
   in MV $ set' o (setBit (prim__getByte b o) i) b

||| Test, if the current node has been visited.
export
visited : Fin k -> MVisited k -@ CRes Bool (MVisited k)
visited i (MV b) = testBit (prim__getByte b $ ix i) i # MV b

||| Discard the linear byte array and return the current result.
export
done : a -> MVisited k -@ Ur a
done x (MV _) = MkBang x

||| Allocate a linear byte array and use it to run the given
||| computation.
export %inline
visiting : (k : Nat) -> (MVisited k -@ Ur a) -> a
visiting k f =
  let i := cast {to = Integer} k `shiftR` bits
   in unrestricted $ f (MV $ prim__newBuf (1 + cast i))
