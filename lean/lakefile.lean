import Lake
open Lake DSL

package «theoria-proto» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib MicroTensor where
  srcDir := "."

lean_lib Rules where
  srcDir := "."

lean_lib Example where
  srcDir := "."

lean_lib Generated where
  srcDir := "."

lean_lib Generated2 where
  srcDir := "."
