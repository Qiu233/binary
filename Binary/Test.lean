import Binary.Deriving
import Binary.Put
import Binary.Get

open Binary Primitive LE

structure T where
  a : Int32
  b : UInt64
-- deriving Encode, Decode

deriving instance Encode for T
deriving instance Decode for T

@[bin_enum 4 [0, 1]]
inductive A where
  | a (x : Int32)
  | b
deriving Repr, Encode, Decode

#eval encode (A.a 20)
#eval encode (A.b)

#eval runGetT (decode (α := A)) (encode (A.a 20)) |>.toExcept
