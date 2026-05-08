import Lake
open Lake DSL

package «reviser» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Reviser» where
  srcDir := "."

lean_exe «smoke» where
  root := `Smoke
