import Binary.Basic

namespace Binary

@[inline]
instance : Decode UInt8 where
  get d :=
    if h : d.offset < d.data.size then
      DecodeResult.success (d.data.get d.offset) {d with offset := d.offset + 1}
    else
      DecodeResult.mkEOI d

@[inline]
instance : Decode Int8 where
  get d :=
    if h : d.offset < d.data.size then
      DecodeResult.success (d.data.get d.offset).toInt8 {d with offset := d.offset + 1}
    else
      DecodeResult.mkEOI d

namespace Primitive

variable {ω m} [Monad m] [STWorld ω m] [MonadLiftT (ST ω) m]

private def generate_prim (le : Bool) (unsigned : Bool) (type : Lean.TSyntax `ident) (size : Lean.TSyntax `num) : Lean.MacroM Lean.Command := do
  let len := size.getNat
    if len = 0 then
      Lean.Macro.throwErrorAt size "size cannot be 0"
    let newSize := Lean.TSyntax.mk <| size.raw.setArg 0 (size.raw[0].setAtomVal s!"{len - 1}")
    let d ← Lean.mkIdent <$> Lean.Macro.addMacroScope `d
    let d_offset ← `($(Lean.mkIdent `Decoder.offset) $d:ident)
    let d_data ← `($(Lean.mkIdent `Decoder.data) $d:ident)
    let d_data_size ← `($(Lean.mkIdent `ByteArray.size) ($(Lean.mkIdent `Decoder.data) $d:ident))
    let ns := List.range len
    let ts ← ns.mapM fun x => do
      let y ←
        if unsigned then
          `($(Lean.mkIdent `ByteArray.get) $d_data ($d_offset + $(Lean.Syntax.mkNatLit x):num))
        else
          `($(Lean.mkIdent `ByteArray.get) $d_data ($d_offset + $(Lean.Syntax.mkNatLit x):num) |>.toInt8)
      let y ←
        if unsigned then
          `($(Lean.mkIdent (Lean.Name.mkStr2 "UInt8" s!"to{type.getId.getString!}")) $y)
        else
          `($(Lean.mkIdent (Lean.Name.mkStr2 "Int8" s!"to{type.getId.getString!}")) $y)
      let shift := if le then x * 8 else (len - 1 - x) * 8
      `($y <<< $(Lean.Syntax.mkNatLit shift):num)
    let combined ←
      match ts with
      | [] => unreachable!
      | [x] => pure x
      | head :: tail => do
        tail.foldlM (init := head) fun (x : Lean.Term) y => do
          `($x ||| $y)
    let code ← `(command|
      scoped instance : Decode $type where
        get $d:ident :=
          if h : $d_offset + $newSize:num < $d_data_size then
            let val := $combined
            DecodeResult.success val {$d with offset := $d_offset + $(Lean.Syntax.mkNatLit len):num}
          else
            DecodeResult.mkEOI d
      )
    return code

local syntax "prim_unsigned_le " ident num : command
local syntax "prim_unsigned_be " ident num : command
local syntax "prim_signed_le " ident num : command
local syntax "prim_signed_be " ident num : command

local
macro_rules
  | `(command| prim_unsigned_le $type $size) => generate_prim true true type size
  | `(command| prim_unsigned_be $type $size) => generate_prim false true type size
  | `(command| prim_signed_le $type $size) => generate_prim true false type size
  | `(command| prim_signed_be $type $size) => generate_prim false false type size

namespace LE

prim_unsigned_le UInt16 2
prim_unsigned_le UInt32 4
prim_unsigned_le UInt64 8

prim_signed_le Int16 2
prim_signed_le Int32 4
prim_signed_le Int64 8

scoped instance : Decode Float32 where
  get d := get (α := UInt32) d |>.map Float32.ofBits

scoped instance : Decode Float where
  get d := get (α := UInt64) d |>.map Float.ofBits

end LE

namespace BE

prim_unsigned_be UInt16 2
prim_unsigned_be UInt32 4
prim_unsigned_be UInt64 8

prim_signed_be Int16 2
prim_signed_be Int32 4
prim_signed_be Int64 8

scoped instance : Decode Float32 where
  get d := get (α := UInt32) d |>.map Float32.ofBits

scoped instance : Decode Float where
  get d := get (α := UInt64) d |>.map Float.ofBits

end BE

end Primitive
