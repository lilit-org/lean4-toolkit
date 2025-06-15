import Lake
open Lake DSL

package «lean-toolkit» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «src» {
  -- add library configuration options here
} 
