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

%inline shift : Integer -> Integer
shift = (`shiftR` bits)

%inline bit : Integer -> Bits8
bit n = cast n .&. mask

%inline setBit : Bits8 -> Integer -> Bits8
setBit v i = v .|. prim__shl_Bits8 1 (bit i)

testBit : Bits8 -> Integer -> Bool
testBit x b =
  case x .&. prim__shl_Bits8 x (bit b) of
    0 => False
    _ => True

--------------------------------------------------------------------------------
--          Visited
--------------------------------------------------------------------------------

||| Wraps a mutable byte array for keeping track of the visited nodes
||| in a graph.
export
record Visited (k : Nat) where
  constructor V
  buf : Buffer

visit' : Integer -> Visited k -@ Visited k
visit' i (V b) =
  let o   := shift i
   in V $ set' o (setBit (prim__getByte b o) i) b

visited' : Integer -> Visited k -@ CRes Bool (Visited k)
visited' i (V b) =
  let bit := cast i .&. 7
   in testBit (prim__getByte b $ shift i) i # V b

||| Set the current node to "visited".
export %inline
visit : Fin k -> Visited k -@ Visited k
visit = visit' . cast

||| Test, if the current node has been visited.
export %inline
visited : Fin k -> Visited k -@ CRes Bool (Visited k)
visited = visited' . cast

||| Discard the linear byte array and return the current result.
export
done : a -> Visited k -@ Ur a
done x (V _) = MkBang x

||| Allocate a linear byte array and use it to run the given
||| computation.
export %inline
visiting : (k : Nat) -> (Visited k -@ Ur a) -> a
visiting k f =
  unrestricted $ f (V $ prim__newBuf (1 + cast (Visited.shift $ cast k)))
