# binary
Lean 4 package for binary data serialization and deserialization, with name `binary` inspired by Haskell's `binary` package.

# Usage
Add to `lakefile.lean`:
```
require binary from git "https://github.com/Lean-zh/binary.git"
```

In file:

```
import Binary

open Binary Primitive.LE
...
```

Or open `Primitive.BE` when you want to handle data in big endian.

The recommended usage is

```
import Binary

open Binary Primitive

open LE in
def serialize_xxx : Put := do
  ...
```

