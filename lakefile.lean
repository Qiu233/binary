import Lake
open Lake DSL

package "binary" where
  version := v!"0.1.0"

lean_lib Binary where

@[default_target]
lean_exe "binary" where
  root := `Main
