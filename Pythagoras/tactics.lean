import SyntheticEuclid4
open incidence_geometry
variable [i: incidence_geometry]

lemma ar132 {a b c : point} : area a b c = area a c b
  := by exact (area_invariant a b c).2
lemma ar312 {a b c : point} : area a b c = area c a b
  := by exact (area_invariant a b c).1
lemma ar231 {a b c : point} : area a b c = area b c a
  := by rw [(area_invariant a b c).1]; rw [(area_invariant c a b).1]
lemma ar213 {a b c : point} : area a b c = area b a c
  := by rw [(area_invariant a b c).2]; rw [(area_invariant a c b).1]
lemma ar321 {a b c : point} : area a b c = area c b a
  := by rw [(area_invariant a b c).2]; rw [(area_invariant c b a).1]

/-- ## Tactic permute
A custom experimental tactic for rewriting the order of operands, currently only working for triangle areas.

Usage (partially mimicking the `rw` syntax):
- `permute` tries all possible permutations of the goal with `rwa`
- `permute at h` tries all possible permutations of hypothesis h with `rwa`
- `permute [213]` tries to swap the first two arguments of the goal with `rwa`
- `permute [213] at h` tries to swap the first two arguments of hypothesis h with `rwa`
- `[←213]` can be used instead of `[213]`, targetting the other side of equality
- `permute [213] 2` performs the rewrite on the second summand of the goal
- `permute [213] 2 at h` performs the rewrite on the second summand of h
 -/
syntax "permute " "["? ("←"?num),* "]"? (num)? ("at" Lean.Parser.Tactic.locationHyp)? ("then" Lean.Parser.Tactic.tacticSeq)? : tactic

macro_rules
-- explicit versions
  | `(tactic| permute [132]) => `(tactic| try rw [@ar132 _ _ _]; try assumption)
  | `(tactic| permute [312]) => `(tactic| try rw [@ar312 _ _ _]; try assumption)
  | `(tactic| permute [231]) => `(tactic| try rw [@ar231 _ _ _]; try assumption)
  | `(tactic| permute [213]) => `(tactic| try rw [@ar213 _ _ _]; try assumption)
  | `(tactic| permute [321]) => `(tactic| try rw [@ar321 _ _ _]; try assumption)

-- TODO: generalize the type of h and use exact instead of assumption
  | `(tactic| permute [132] at $h) => `(tactic| try rw [@ar132 _ _ _] at $h; try assumption)
  | `(tactic| permute [312] at $h) => `(tactic| try rw [@ar312 _ _ _] at $h; try assumption)
  | `(tactic| permute [231] at $h) => `(tactic| try rw [@ar231 _ _ _] at $h; try assumption)
  | `(tactic| permute [213] at $h) => `(tactic| try rw [@ar213 _ _ _] at $h; try assumption)
  | `(tactic| permute [321] at $h) => `(tactic| try rw [@ar321 _ _ _] at $h; try assumption)

-- implicit versions
  | `(tactic| permute) => `(tactic|
  {
   permute [132]
   permute [312]
   permute [231]
   permute [213]
   permute [321]
  })

  | `(tactic| permute then $t) => `(tactic|
  {
   permute [132]; try $t
   permute [312]; try $t
   permute [231]; try $t
   permute [213]; try $t
   permute [321]; try $t
  })

  | `(tactic| permute at $h) => `(tactic|
  {
    -- TODO: rw of h, perhaps with Lean.Parser.Tactic.rwRule?
   permute [132] at $h
   permute [312] at $h
   permute [231] at $h
   permute [213] at $h
   permute [321] at $h
  })

  | `(tactic| permute at $h then $t) => `(tactic|
  {
    -- TODO: rw of h, perhaps with Lean.Parser.Tactic.rwRule?
   permute [132] at $h; try $t
   permute [312] at $h; try $t
   permute [231] at $h; try $t
   permute [213] at $h; try $t
   permute [321] at $h; try $t
  })

-- backwards and iterative versions
-- TODO: ← should invoke the backwards rw instead; both should also have a h version
  | `(tactic| permute [←$a]) => `(tactic| apply Eq.symm; permute [$a]; try apply Eq.symm)
  | `(tactic| permute [$a] 2) => `(tactic| rw [add_comm]; permute [$a]; try rw [add_comm])
  | `(tactic| permute [$a] 2 at $h) => `(tactic| rw [add_comm] at $h; permute [$a] at $h; try rw [add_comm] at $h)
  | `(tactic| permute [$a, ←$b]) => `(tactic| permute [$a]; permute [←$b])
  | `(tactic| permute [←$a, $b]) => `(tactic| permute [←$a]; permute [$b])
  | `(tactic| permute [←$a, ←$b]) => `(tactic| permute [←$a]; permute [←$b])
  | `(tactic| permute [$a, $b]) => `(tactic| permute [$a]; permute [$b])
  | `(tactic| permute [$a, $b] at $h) => `(tactic| permute [$a] at $h; permute [$b] at $h)
  | `(tactic| permute [$a, $b, $c] at $h) => `(tactic| permute [$a] at $h; permute [$b] at $h; permute [$c] at $h)
