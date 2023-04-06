import SyntheticEuclid4

/-- ## Tactic permute
A custom experimental tactic for rewriting the order of operands, currently only working for triangle areas.

Usage (partially mimicking the `rw` syntax):
- `permute` tries all possible permutations of the goal
- `permute at h` tries all possible permutations of hypothesis h
- `permute [213]` tries to swap the first two arguments of the goal
- `permute [213] at h` tries to swap the first two arguments of hypothesis h
- `[←213]` can be used instead of `[213]`, invoking the inverse permutation
 -/
syntax "permute" "["? ("←"?num),* "]"? ("at" Lean.Parser.Tactic.locationHyp)?: tactic

macro_rules
-- explicit versions
  | `(tactic| permute [132]) => `(tactic| rw [(area_invariant _ _ _).2])
  | `(tactic| permute [312]) => `(tactic| rw [(area_invariant _ _ _).1])
  | `(tactic| permute [231]) => `(tactic| permute [312]; try permute [312])
  | `(tactic| permute [213]) => `(tactic| permute [231]; try permute [132])
  | `(tactic| permute [321]) => `(tactic| permute [312]; try permute [132])

  | `(tactic| permute [132] at $h) => `(tactic| rw [(area_invariant _ _ _).2] at $h)
  | `(tactic| permute [312] at $h) => `(tactic| rw [(area_invariant _ _ _).1] at $h)
  | `(tactic| permute [231] at $h) => `(tactic| permute [312] at $h; try permute [312] at $h)
  | `(tactic| permute [213] at $h) => `(tactic| permute [231] at $h; try permute [132] at $h)
  | `(tactic| permute [321] at $h) => `(tactic| permute [312] at $h; try permute [132] at $h)

-- implicit versions
  | `(tactic| permute) => `(tactic| try
  {
   try permute [213]
   try permute [132]
   try permute [321]
   try permute [231]
   try permute [312]
  })

  | `(tactic| permute at $h) => `(tactic| try
  {
   try permute [213] at $h
   try permute [132] at $h
   try permute [321] at $h
   try permute [231] at $h
   try permute [312] at $h
  })


-- backwards and iterative versions
  | `(tactic| permute [←$a]) => `(tactic| apply Eq.symm; try permute [$a]; try apply Eq.symm)
  | `(tactic| permute [$a, ←$b]) => `(tactic| permute [$a]; permute [←$b])
  | `(tactic| permute [←$a, $b]) => `(tactic| permute [←$a]; permute [$b])
  | `(tactic| permute [←$a, ←$b]) => `(tactic| permute [←$a]; permute [←$b])
  | `(tactic| permute [$a, $b]) => `(tactic| permute [$a]; permute [$b])
  | `(tactic| permute [$a, $b, $c]) => `(tactic| permute [$a]; permute [$b]; permute [$c])
  -- TODO: backwards rw of hypothesis, perhaps with Lean.TSyntax.symm?
  -- | `(tactic| permute [←$a] at $h) => `(tactic| try permute [$a] at $h.symm)
