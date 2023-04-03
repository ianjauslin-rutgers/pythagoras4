import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

package pythagoras

@[default_target]
lean_lib Pythagoras
