import Lean

namespace Binary

class Encode (α : Type) where
  encode : α → ByteArray
export Encode (encode)

attribute [inline] Encode.encode -- TODO: has no effect?

structure Decoder where
  data : ByteArray
  offset : Nat
deriving Inhabited

instance : Repr ByteArray where
  reprPrec x _ := toString x

deriving instance Repr for Decoder

inductive DecodeResult (α) where
  | success (x : α) (cont : Decoder)
  | error (err : String) (cur : Decoder)
  | eoi
deriving Inhabited

def DecodeResult.toExcept : DecodeResult α → Except String α
  | .success x _ => .ok x
  | .error err _ => .error err
  | .eoi => .error "EOI"

-- TODO: make `ByteArray` immutable
def GetT (m : Type → Type) (α : Type) : Type := Decoder → m (DecodeResult α)

@[inline]
instance {m} [Monad m] : Monad (GetT m) where
  pure x := fun d => pure (DecodeResult.success x d)
  bind mx xmy := fun d => do
    let s ← mx d
    match s with
    | .eoi => pure .eoi
    | .error err d => pure <| .error err d
    | .success x cont => xmy x cont

@[inline]
def GetT.failure [Applicative m] : GetT m α := fun d => pure (DecodeResult.eoi)

@[inline]
def GetT.orElse [Monad m] (x : GetT m α) (y : Unit → GetT m α) : GetT m α := fun d => do
  match ← x d with
  | r@(.success ..) => return r
  | .eoi | .error .. => y () d

@[inline]
instance [Monad m] : Alternative (GetT m) where
  failure := GetT.failure
  orElse := GetT.orElse

def GetT.error [Monad m] : String → GetT m α := fun x d => pure (.error x d)

def runGetT {m : Type → Type} [Monad m] (x : GetT m α) (bytes : ByteArray) : m (DecodeResult α) := do
  x {data := bytes, offset := 0}

abbrev Getter (α : Type) : Type := GetT Id α

def Getter.error : String → Getter α := fun x d => .error x d

class Decode (α : Type) where
  decode : Getter α
export Decode (decode)

partial def DecodeResult.map (f : α → β) (x : DecodeResult α) : DecodeResult β :=
  match x with
  | .success x cont => .success (f x) cont
  | .eoi => .eoi
  | .error err d => .error err d

abbrev PutT (m : Type → Type) : Type → Type := StateT ByteArray m

abbrev Put (m : Type → Type) := PutT m Unit

@[inline]
def put_bytes {m} [Monad m] (bytes : ByteArray) : Put m := do
  modify fun s => s.append bytes

private def get_decoder {ω m} [Monad m] [STWorld ω m] [MonadLiftT (ST ω) m] : GetT m Decoder := fun d => pure (DecodeResult.success d d)

@[inline]
protected def Decoder.get_bytes (d : Decoder) (len : Nat) : Option (ByteArray × Decoder) :=
  let start := d.offset
  let end' := start + len
  if end' > d.data.size then none
  else
    some (d.data.extract start end', { d with offset := end' })

@[inline]
def get_bytes [Monad m] (len : Nat) : GetT m ByteArray := fun d => do
  match d.get_bytes len with
  | none => return .eoi
  | some (xs, cont) => return DecodeResult.success xs cont

namespace Primitive

end Primitive

end Binary

def ByteArray.join : Array ByteArray → ByteArray := fun xss => Id.run do
  let length := xss.foldl (init := 0) fun x y => x + y.size
  let mut arr := ByteArray.emptyWithCapacity length
  for xs in xss do
    arr := arr.append xs
  return arr

namespace Binary

instance [Encode α] : Encode (Vector α n) where
  encode x := ByteArray.join <| x.toArray.map Encode.encode

/--
An auxiliary type to embed literal in complex structure.

For example, the following structure has a fixed magic number for sanity check.
```
structure A where
  magic : Literal Int32 123
  x : UInt32
  y : UInt32
```
-/
structure Literal (α : Type) (a : α) where
  val : α
  h : val = a

instance [Encode α] : Encode (Literal α a) where
  encode x := Encode.encode x.val

instance [DecidableEq α] [Decode α] : Decode (Literal α a) where
  decode := do
    let v ← Decode.decode (α := α)
    if h : v = a then
      return ⟨v, h⟩
    else
      Getter.error "failed to decode literal"

end Binary
