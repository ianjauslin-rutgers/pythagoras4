import SyntheticEuclid4
open incidence_geometry

/-- ## Tactic permute
A custom experimental tactic for rewriting the order of operands, currently only working for triangle areas.

Usage (partially mimicking the `rw` syntax):
- `permute` tries all possible permutations of the goal, then tries `simp` and `assumption`
- `permute at h` tries all possible permutations of hypothesis h, then tries `simp at h`
- `permute [213]` tries to swap the first two arguments of the goal, then tries `simp`
- `permute [213] at h` tries to swap the first two arguments of hypothesis h, then tries `simp`
- `[←213]` can be used instead of `[213]`, targetting the other side of equality
- `permute [213] 2` performs the rewrite on the second summand of the goal
- `permute [213] 2 at h` performs the rewrite on the second summand of h
 -/
syntax "permute " "["? ("←"?num),* "]"? (num)? ("at" Lean.Parser.Tactic.locationHyp)? : tactic

macro_rules
-- explicit versions
  | `(tactic| permute [132]) => `(tactic| rw [(area_invariant _ _ _).2])
  | `(tactic| permute [312]) => `(tactic| rw [(area_invariant _ _ _).1])
  | `(tactic| permute [231]) => `(tactic| permute [312]; permute [312])
  | `(tactic| permute [213]) => `(tactic| permute [231]; permute [132])
  | `(tactic| permute [321]) => `(tactic| permute [312]; permute [132])

  | `(tactic| permute [132] at $h) => `(tactic| rw [(area_invariant _ _ _).2] at $h; simp at $h)
  | `(tactic| permute [312] at $h) => `(tactic| rw [(area_invariant _ _ _).1] at $h; simp at $h)
  | `(tactic| permute [231] at $h) => `(tactic| permute [312] at $h; try permute [312] at $h)
  | `(tactic| permute [213] at $h) => `(tactic| permute [231] at $h; try permute [132] at $h)
  | `(tactic| permute [321] at $h) => `(tactic| permute [312] at $h; try permute [132] at $h)

-- implicit versions
  | `(tactic| permute) => `(tactic| try
  {
   try permute [213]; simp; assumption
   try permute [132]; simp; assumption
   try permute [321]; simp; assumption
   try permute [231]; simp; assumption
   try permute [312]; simp; assumption
  })

  | `(tactic| permute at $h) => `(tactic| try
  {
    -- TODO: rw of h, perhaps with Lean.Parser.Tactic.rwRule?
   try permute [213] at $h
   try permute [132] at $h
   try permute [321] at $h
   try permute [231] at $h
   try permute [312] at $h
  })


-- backwards and iterative versions
-- TODO: ← should invoke the backwards rw instead; both should also have a h version
  | `(tactic| permute [←$a]) => `(tactic| apply Eq.symm; try permute [$a]; try apply Eq.symm)
  | `(tactic| permute [$a] 2) => `(tactic| rw [add_comm]; try permute [$a]; try rw [add_comm])
  | `(tactic| permute [$a] 2 at $h) => `(tactic| rw [add_comm] at $h; try permute [$a] at $h; try rw [add_comm] at $h)
  | `(tactic| permute [$a, ←$b]) => `(tactic| permute [$a]; permute [←$b])
  | `(tactic| permute [←$a, $b]) => `(tactic| permute [←$a]; permute [$b])
  | `(tactic| permute [←$a, ←$b]) => `(tactic| permute [←$a]; permute [←$b])
  | `(tactic| permute [$a, $b]) => `(tactic| permute [$a]; permute [$b])
  | `(tactic| permute [$a, $b] at $h) => `(tactic| permute [$a] at $h; permute [$b] at $h)
  | `(tactic| permute [$a, $b, $c] at $h) => `(tactic| permute [$a] at $h; permute [$b] at $h; permute [$c] at $h)
