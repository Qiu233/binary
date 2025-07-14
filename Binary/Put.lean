import Binary.Basic

namespace Binary

@[inline]
instance : Encode UInt8 where
  encode x := ⟨#[x]⟩

@[inline]
instance : Encode Int8 where
  encode x := encode x.toUInt8

namespace Primitive

namespace LE

@[inline]
scoped instance : Encode UInt16 where
  encode x := ⟨#[x.toUInt8, (x >>> 8).toUInt8]⟩

@[inline]
scoped instance : Encode Int16 where
  encode x := encode x.toUInt16

@[inline]
scoped instance : Encode UInt32 where
  encode x :=
    let s : ByteArray := ByteArray.emptyWithCapacity 4
    let s := s.append <| encode x.toUInt16
    let s := s.append <| encode (x >>> 16).toUInt16
    s

@[inline]
scoped instance : Encode Int32 where
  encode x := encode x.toUInt32

@[inline]
scoped instance : Encode UInt64 where
  encode x :=
    let s : ByteArray := ByteArray.emptyWithCapacity 8
    let s := s.append <| encode x.toUInt32
    let s := s.append <| encode (x >>> 32).toUInt32
    s

@[inline]
scoped instance : Encode Int64 where
  encode x := encode x.toUInt64

@[inline]
scoped instance : Encode Float32 where
  encode x := encode x.toBits

@[inline]
scoped instance : Encode Float where
  encode x := encode x.toBits

end LE

namespace BE

@[inline]
scoped instance : Encode UInt16 where
  encode x := ⟨#[(x >>> 8).toUInt8, x.toUInt8]⟩

@[inline]
scoped instance : Encode Int16 where
  encode x := encode x.toUInt16

@[inline]
scoped instance : Encode UInt32 where
  encode x :=
    let s : ByteArray := ByteArray.emptyWithCapacity 4
    let s := s.append <| encode (x >>> 16).toUInt16
    let s := s.append <| encode x.toUInt16
    s

@[inline]
scoped instance : Encode Int32 where
  encode x := encode x.toUInt32

@[inline]
scoped instance : Encode UInt64 where
  encode x :=
    let s : ByteArray := ByteArray.emptyWithCapacity 8
    let s := s.append <| encode (x >>> 32).toUInt32
    let s := s.append <| encode x.toUInt32
    s

@[inline]
scoped instance : Encode Int64 where
  encode x := encode x.toUInt64

@[inline]
scoped instance : Encode Float32 where
  encode x := encode x.toBits

@[inline]
scoped instance : Encode Float where
  encode x := encode x.toBits

end BE

end Primitive
