import Pythagoras.euclid_VI
open incidence_geometry
variable [i: incidence_geometry]

/-- Aux lemma -/
lemma aux {a b c : point} (Tabc : ¬ colinear a b c) (ang_a : rightangle ≤ angle b a c) :
    ∃ d, B b d c ∧ angle b d a = rightangle := by
  obtain ⟨L, bL, cL⟩ := line_of_pts b c
  have aL : ¬ online a L := by exact fun h => Tabc ⟨L, h, bL, cL⟩
  obtain ⟨d, -, hd₂, hd₃⟩ := pythlem (neq_23_of_not_colinear Tabc).symm cL bL aL ang_a
  exact ⟨d, B_symm hd₃, (by perma)⟩

/-- *** Euclid VI.31 *** -/
theorem pythagorean_proof_two {a b c : point} (Tabc : triangle a b c)
    (ang_a : angle b a c = rightangle) : 
    (length a b)^2 + (length a c)^2 = (length b c)^2 := by 
  have ba : length b a ≠ 0 := length_eq_zero_iff.not.mpr (neq_12_of_not_colinear Tabc).symm
  have bc : length b c ≠ 0 := length_eq_zero_iff.not.mpr (neq_23_of_not_colinear Tabc)
  have ca : length c a ≠ 0 := length_eq_zero_iff.not.mpr (neq_13_of_not_colinear Tabc).symm
  have cb : length c b ≠ 0 := fun h => bc ((length_symm b c).trans h)
  obtain ⟨d, Bbdc, ang_d⟩ := aux Tabc ang_a.symm.le
  have Tdba : triangle d b a :=
    fun ⟨L, dL, bL, aL⟩ => Tabc ⟨L, aL, bL, online_3_of_B Bbdc bL dL⟩
  dsimp [triangle] at Tabc Tdba
  have abc_dba : angle a b c = angle d b a := by
    linperm [angle_extension_of_B (length_eq_zero_iff.not.mp ba) Bbdc]
  have Tbda : triangle b d a := fun C => by perm at *; exact Tdba C
  have Tbac : triangle b a c := fun C => by perm at *; exact Tabc C
  have := similar_of_AA Tbda Tbac abc_dba.symm (by linarith)
  have rat1 := (proportion_len_iff _ _ _ _ _ _ _ _ ba bc).mpr this; field_simp at rat1
  have Tdca : triangle d c a := fun ⟨L, dL, cL, aL⟩ =>
   Tabc ⟨L, aL, (online_3_of_B (B_symm Bbdc) cL dL), cL⟩
  have acb_dca : angle a c b = angle d c a := by
    linperm [angle_extension_of_B (length_eq_zero_iff.not.mp ca) (B_symm Bbdc)]
  have ang_d : angle c d a = rightangle := by
    obtain ⟨L, bL, cL⟩ := line_of_pts b c
    linperm [(angle_eq_iff_rightangle bL cL (fun aL => Tabc ⟨L, aL, bL, cL⟩) Bbdc).mpr ang_d]
  have Tcda : triangle c d a := fun C => by perm at *; exact Tdca C
  have Tcab : triangle c a b := fun C => by perm at *; exact Tbac C
  have := similar_of_AA Tcda Tcab acb_dca.symm (by linperm)
  have rat2 := (proportion_len_iff _ _ _ _ _ _ _ _ ca cb).mpr this; field_simp at rat2
  perm [length_sum_of_B Bbdc]
  conv in (occs := *) length _ _ ^ 2 => all_goals rw [sq]
  perm at rat1, rat2; rw [← rat1, ← rat2, ← right_distrib, this]
