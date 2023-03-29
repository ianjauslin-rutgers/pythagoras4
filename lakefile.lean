import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

package pythagoras {
  -- add package configuration options here
}

lean_lib Euclid {
  -- add library configuration options here
}
