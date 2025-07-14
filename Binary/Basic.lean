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
deriving Inhabited

@[inline]
instance : Functor DecodeResult where
  map f
    | .success x k => .success (f x) k
    | .error err cur => .error err cur

def DecodeResult.toExcept : DecodeResult α → Except String α
  | .success x _ => .ok x
  | .error err _ => .error err

def Get (α : Type) : Type := Decoder → (DecodeResult α)

@[inline]
instance : Monad Get where
  pure x := fun d => DecodeResult.success x d
  bind mx xmy := fun d =>
    let s := mx d
    match s with
    | .error err d => .error err d
    | .success x cont => xmy x cont

@[inline]
instance : Alternative Get where
  failure := fun d => DecodeResult.error "failure" d
  orElse x y := fun d => match x d with
  | r@(.success ..) => r
  | .error .. => y () d -- backtracking

@[inline]
instance : MonadExcept String Get where
  throw err := fun d => DecodeResult.error err d
  tryCatch body handler := fun d =>
    let r := body d
    match r with
    | .success .. => r
    | .error err _ => handler err d -- backtracking

/-- We decide to **backtrack** if the `try` block fails. -/
@[inline]
instance : MonadFinally Get where
  tryFinally' x f := fun d =>
    let y := x d
    match y with
    | .success a k =>
      let r := f (some a) k
      match r with
      | .success b k' => .success (a, b) k'
      | .error err k' => .error err k'
    | .error err _ =>
      let r := f none d -- backtracking
      match r with
      | .success _ k' => .error err k' -- caught, we ignore the inner error
      | .error err' k' => .error err' k' -- the finalizer throws an error

def Get.run (x : Get α) (bytes : ByteArray) : (DecodeResult α) := x {data := bytes, offset := 0}

protected def DecodeResult.mkEOI : Decoder → DecodeResult α := .error "EOI"

def throwEOI : Get α := DecodeResult.mkEOI

class Decode (α : Type) where
  decode : Get α
export Decode (decode)

partial def DecodeResult.map (f : α → β) (x : DecodeResult α) : DecodeResult β :=
  match x with
  | .success x cont => .success (f x) cont
  | .error err d => .error err d

abbrev Putter (α) := StateM ByteArray α
abbrev Put := Putter Unit

@[inline]
def put_bytes (bytes : ByteArray) : Put := do
  modify fun s => s.append bytes

@[inline]
protected def Decoder.get_bytes (d : Decoder) (len : Nat) : Option (ByteArray × Decoder) :=
  let start := d.offset
  let end' := start + len
  if end' > d.data.size then none
  else
    some (d.data.extract start end', { d with offset := end' })

@[inline]
def get_bytes [Monad m] (len : Nat) : Get ByteArray := fun d =>
  match d.get_bytes len with
  | none => DecodeResult.error "EOI" d
  | some (xs, k) => DecodeResult.success xs k

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
      throw "failed to decode literal"

end Binary
