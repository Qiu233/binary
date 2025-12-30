import Lake
open Lake DSL

package "binary" where
  version := v!"0.1.0"
  leanOptions := #[ ⟨`experimental.module, true⟩ ]

lean_lib Binary where
