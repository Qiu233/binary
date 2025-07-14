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
  | a (tag : Literal UInt32 10) (x : Int32)
  | b
deriving Repr, Encode, Decode

#eval encode (A.a ⟨10, by simp⟩ 20)
#eval encode (A.b)

#eval Get.run (decode (α := A)) (encode (A.a ⟨10, by simp⟩ 20)) |>.toExcept

instance {α : Type} [ToString α] : ToString (DecodeResult α) where
  toString
    | .success x _ => s!"success: {x}"
    | .error err _ => s!"error: {err}"
    | .pending _ => s!"pending"

partial def get_byte' : Get UInt8 := pending (Decode.decode (α := UInt8))

-- this function caches partial input
def p : Get UInt32 := do
  let h1 ← UInt8.toUInt32 <$> get_byte'
  let h2 ← UInt8.toUInt32 <$> get_byte'
  let h3 ← UInt8.toUInt32 <$> get_byte'
  let h4 ← UInt8.toUInt32 <$> get_byte'
  return h1 ||| (h2 <<< 8) ||| (h3 <<< 16) ||| (h4 <<< 24)

def f : IO Unit := do
  let t := Get.run p ⟨#[2]⟩
  println! "{t}"
  let t := t.feed ⟨#[0]⟩
  println! "{t}"
  let t := t.feed ⟨#[0]⟩
  println! "{t}"
  let t := t.feed ⟨#[0]⟩
  println! "{t}"

#eval f

-- this function retries completely
def g : IO Unit := do
  let t := Get.run (pending <| Decode.decode (α := UInt32)) ⟨#[2]⟩
  println! "{t}"
  let t := t.feed ⟨#[0]⟩
  println! "{t}"
  let t := t.feed ⟨#[0]⟩
  println! "{t}"
  let t := t.feed ⟨#[0]⟩
  println! "{t}"

#eval g
