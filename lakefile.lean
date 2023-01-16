import Lake
open Lake DSL

package holfloat

@[default_target]
lean_lib HOLFloat where
  moreLeanArgs := #["-Dpp.unicode.fun=true"]

@[default_target]
lean_exe runLinter where
  root := `scripts.runLinter
  supportInterpreter := true

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"
