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
require aesop from git "https://github.com/JLimperg/aesop" @ "7fe9ecd9339b0e1796e89d243b776849c305c690"
