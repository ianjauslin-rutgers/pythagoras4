import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"
require synthetic_euclid_4 from git
  "https://github.com/ah1112/synthetic_euclid_4.git"@"c6c30de"

package pythagoras

@[default_target]
lean_lib Pythagoras
