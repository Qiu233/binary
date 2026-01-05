# binary
Lean 4 package for binary data serialization and deserialization, with name `binary` inspired by Haskell's `binary` package.

# Usage
Add to `lakefile.lean`:
```
require binary from git "https://github.com/Lean-zh/binary.git"
```

## Deriving
```lean
import Binary

open Binary Primitive

open LE in
@[bin_enum 4 [0, 2]]
inductive A where
  | a -- 0
  | b (s : Int32) -- 2
deriving Encode, Decode

open BE in
structure B where
  s : Int32
deriving Encode, Decode

#eval Put.run 128 (put (A.b 1234))
```

## Serialization/Deserialization

```lean
import Binary

open Binary Primitive.LE
...
```

Or open `Primitive.BE` when you want to handle data in big endian.

The recommended usage is

```lean
import Binary

open Binary Primitive

open LE in
def serialize_xxx : Put := do
  ...
```

