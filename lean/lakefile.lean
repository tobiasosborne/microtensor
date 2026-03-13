import Lake
open Lake DSL

package «theoria-proto» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib MicroTensor where
  srcDir := "."

@[default_target]
lean_lib Rules where
  srcDir := "."

@[default_target]
lean_lib Example where
  srcDir := "."

@[default_target]
lean_lib Generated where
  srcDir := "."

@[default_target]
lean_lib Generated2 where
  srcDir := "."
