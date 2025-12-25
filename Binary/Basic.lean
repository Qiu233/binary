import Lean

namespace Binary

structure Decoder where
  data : ByteArray
  offset : Nat
deriving Inhabited

def Decoder.append (bytes : ByteArray) : Decoder → Decoder := fun d => {d with data := d.data.append bytes}

inductive DecodeResult (α) where
  | success (x : α) (k : Decoder)
  | error (err : String) (cur : Decoder)
  | pending (fn : ByteArray → DecodeResult α)
deriving Inhabited

@[inline]
instance : Functor DecodeResult where
  map f t :=
    let rec @[specialize] go t := match t with
      | .success x k => .success (f x) k
      | .error err cur => .error err cur
      | .pending fn => .pending fun bytes => go <| fn bytes
    go t

def DecodeResult.toExcept : DecodeResult α → Except String α
  | .success x _ => .ok x
  | .error err _ => .error err
  | .pending _ => .error "pending input"

def Get (α : Type) : Type := Decoder → (DecodeResult α)

-- @[inline]
-- def Get.join {α} : Get (Get α) → Get α := fun xx d =>
--   let rec @[specialize] go t :=
--     match t with
--     | .success x k => x k
--     | .error err k => .error err k
--     | .pending fn => .pending fun bytes => go <| fn bytes
--   go (xx d)

def DecodeResult.feed {α} (bytes : ByteArray) : DecodeResult α → DecodeResult α
  | .success x k => .success x (k.append bytes)
  | .error err k => .error err (k.append bytes)
  | .pending fn => fn bytes

@[inline]
instance : Monad Get where
  pure x := fun d => DecodeResult.success x d
  bind mx xmy := fun d =>
    let rec @[specialize] go s :=
      match s with
      | .error err d => .error err d
      | .success x cont => xmy x cont
      | .pending fn => .pending fun bytes =>
        go <| fn bytes -- not yet complete, pending bytes prior to binding
    go <| mx d

@[inline]
instance : Alternative Get where
  failure := fun d => DecodeResult.error "failure" d
  orElse x y := fun d =>
    let rec @[specialize] go s :=
      match s with
      | r@(.success ..) => r
      | .error .. => y () d -- backtracking
      | .pending fn => .pending fun bytes =>
        go <| fn bytes
    go <| x d

@[inline]
instance : MonadExcept String Get where
  throw err := fun d => DecodeResult.error err d
  tryCatch body handler := fun d =>
    let rec @[specialize] go s :=
      match s with
      | .success .. => s
      | .error err _ => handler err d -- backtracking
      | .pending fn => .pending fun bytes => go <| fn bytes
    go <| body d

/-- We decide to **backtrack** if the `try` block fails. -/
@[inline]
instance : MonadFinally Get where
  tryFinally' x f := fun d =>
    let rec go s :=
      match s with
      | .success a k =>
        let r := f (some a) k
        let rec go' r :=
          match r with
          | .success b k' => .success (a, b) k'
          | .error err k' => .error err k'
          | .pending fn => .pending fun bytes => go' <| fn bytes
        go' r
      | .error err _ =>
        let r := f none d -- backtracking
        let rec go'' r :=
          match r with
          | .success _ k' => .error err k' -- caught, we ignore the inner error
          | .error err' k' => .error err' k' -- the finalizer throws an error
          | .pending fn => .pending fun bytes => go'' <| fn bytes
        go'' r
      | .pending fn => .pending fun bytes => go <| fn bytes
    go <| x d

def Get.run (x : Get α) (bytes : ByteArray) : (DecodeResult α) := x {data := bytes, offset := 0}

protected def DecodeResult.mkEOI : Decoder → DecodeResult α := .error "EOI"

def throwEOI : Get α := DecodeResult.mkEOI

class Decode (α : Type) where
  get : Get α
export Decode (get)

def getThe (α : Type) [Decode α] : Get α := Decode.get (α := α)

def DecodeResult.map (f : α → β) (x : DecodeResult α) : DecodeResult β := f <$> x

abbrev Putter (α) := StateM ByteArray α
abbrev Put := Putter Unit

class Encode (α : Type) where
  put : α → Put
export Encode (put)

def Put.run (capacity : Nat := 128) : Put → ByteArray := fun x =>
  Prod.snd <$> x (ByteArray.emptyWithCapacity capacity)

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
def get_bytes (len : Nat) : Get ByteArray := fun d =>
  match d.get_bytes len with
  | none => DecodeResult.mkEOI d
  | some (xs, k) => DecodeResult.success xs k

/--
Catch any `EOI` and recover to a pending state rather than exit with an error.

**This function retry the whole `x` until no `EOI` is caught.** The caller should
* ensure that `x` terminates when enough bytes are fed,
* or define your own pending function to cache intermediate result as much as possible.
-/
@[specialize]
partial def pending (x : Get α) : Get α := do
  try x
  catch err =>
    match err with
    | "EOI" => fun d => .pending fun bytes => pending x (d.append bytes)
    | e => throw e

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
  put x := x.toArray.forM Encode.put

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

instance [Repr α] : Repr (Literal α a) where
  reprPrec x := reprPrec x.val

instance [ToString α] : ToString (Literal α a) where
  toString x := toString x.val

instance [Encode α] : Encode (Literal α a) where
  put x := Encode.put x.val

instance [DecidableEq α] [Decode α] : Decode (Literal α a) where
  get := do
    let v ← Decode.get (α := α)
    if h : v = a then
      return ⟨v, h⟩
    else
      throw "failed to decode literal"

end Binary
