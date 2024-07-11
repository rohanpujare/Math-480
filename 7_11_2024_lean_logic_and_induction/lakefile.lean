import Lake
open Lake DSL

package «7_11_2024_lean_logic_and_induction» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_exe «7_11_2024_lean_logic_and_induction» where
  root := `Main
