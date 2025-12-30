module

public import Binary.Basic

public section

namespace Binary

@[inline]
instance : Encode UInt8 where
  put x := modify fun bs => bs.push x

@[inline]
instance : Encode Int8 where
  put x := put x.toUInt8

namespace Primitive

namespace LE

@[inline]
scoped instance : Encode UInt16 where
  put x := put_bytes ⟨#[x.toUInt8, (x >>> 8).toUInt8]⟩

@[inline]
scoped instance : Encode Int16 where
  put x := put x.toUInt16

@[inline]
scoped instance : Encode UInt32 where
  put x := do
    put x.toUInt16
    put (x >>> 16).toUInt16

@[inline]
scoped instance : Encode Int32 where
  put x := put x.toUInt32

@[inline]
scoped instance : Encode UInt64 where
  put x := do
    put x.toUInt32
    put (x >>> 32).toUInt32

@[inline]
scoped instance : Encode Int64 where
  put x := put x.toUInt64

@[inline]
scoped instance : Encode Float32 where
  put x := put x.toBits

@[inline]
scoped instance : Encode Float where
  put x := put x.toBits

end LE

namespace BE

@[inline]
scoped instance : Encode UInt16 where
  put x := put_bytes ⟨#[(x >>> 8).toUInt8, x.toUInt8]⟩

@[inline]
scoped instance : Encode Int16 where
  put x := put x.toUInt16

@[inline]
scoped instance : Encode UInt32 where
  put x := do
    put (x >>> 16).toUInt16
    put x.toUInt16

@[inline]
scoped instance : Encode Int32 where
  put x := put x.toUInt32

@[inline]
scoped instance : Encode UInt64 where
  put x := do
    put (x >>> 32).toUInt32
    put x.toUInt32

@[inline]
scoped instance : Encode Int64 where
  put x := put x.toUInt64

@[inline]
scoped instance : Encode Float32 where
  put x := put x.toBits

@[inline]
scoped instance : Encode Float where
  put x := put x.toBits

end BE

end Primitive
