import Pythagoras.euclid_VI
open incidence_geometry
variable [i: incidence_geometry]

/-- Aux lemmata -/

lemma aux_1 {a b c : point} (tri_abc : ¬ colinear a b c) (ang_a : rightangle ≤ angle b a c) : 
    ∃ d, B b d c ∧ angle b d a = rightangle := by
  obtain ⟨L, bL, cL⟩ := line_of_pts b c
  have naL : ¬ online a L := by exact fun h => tri_abc ⟨L, h, bL, cL⟩
  obtain ⟨d, -, hd₂, hd₃⟩ := pythlem (neq_23_of_not_colinear tri_abc).symm cL bL naL ang_a
  exact ⟨d, B_symm hd₃, (by perma)⟩

lemma aux_2 {a b c d : point} (a_ne_b : a ≠ b) (Bbdc : B b d c) : angle a b d = angle a b c := by 
  perma [angle_extension_of_B a_ne_b.symm Bbdc]

/-- *** Euclid VI.31 *** -/
theorem pythagorean_proof_two {a b c : point} (tri_abc : triangle a b c)
    (ang_a : angle b a c = rightangle) : 
    (length a b)^2 + (length a c)^2 = (length b c)^2 := by 
  have ba : length b a ≠ 0 := length_eq_zero_iff.not.mpr (neq_12_of_not_colinear tri_abc).symm
  have bc : length b c ≠ 0 := length_eq_zero_iff.not.mpr (neq_23_of_not_colinear tri_abc)
  have ca : length c a ≠ 0 := length_eq_zero_iff.not.mpr (neq_13_of_not_colinear tri_abc).symm
  have cb : length c b ≠ 0 := fun h => bc ((length_symm b c).trans h)
  obtain ⟨d, Bbdc, ang_d⟩ := aux_1 tri_abc ang_a.symm.le
  have tri_dba : triangle d b a :=
    fun ⟨L, dL, bL, aL⟩ => tri_abc ⟨L, aL, bL, online_3_of_B Bbdc bL dL⟩
  dsimp [triangle] at tri_abc tri_dba
  have ang_b : angle a b c = angle d b a := by
    linperm [aux_2 (neq_12_of_not_colinear tri_abc) Bbdc]
  have tri_bda : triangle b d a := fun C => by perm at *; exact tri_dba C
  have tri_bac : triangle b a c := fun C => by perm at *; exact tri_abc C
  have := similar_of_AA tri_bda tri_bac ang_b.symm (by linarith)
  have xcca := (proportion_len_iff _ _ _ _ _ _ _ _ ba bc).mpr this; field_simp at xcca
  have tri_dca : triangle d c a := fun ⟨L, dL, cL, aL⟩ =>
   tri_abc ⟨L, aL, (online_3_of_B (B_symm Bbdc) cL dL), cL⟩
  have ang_c : angle a c b = angle d c a := by
    linperm [aux_2 (neq_13_of_not_colinear tri_abc) (B_symm Bbdc)]
  have ang_d : angle c d a = rightangle := by
    obtain ⟨L, bL, cL⟩ := line_of_pts b c
    linperm [(angle_eq_iff_rightangle bL cL (fun aL => tri_abc ⟨L, aL, bL, cL⟩) Bbdc).mpr ang_d]
  have tri_cda : triangle c d a := fun C => by perm at *; exact tri_dca C
  have tri_cab : triangle c a b := fun C => by perm at *; exact tri_bac C
  have := similar_of_AA tri_cda tri_cab ang_c.symm (by linperm)
  have ybba := (proportion_len_iff _ _ _ _ _ _ _ _ ca cb).mpr this; field_simp at ybba
  perm [length_sum_of_B Bbdc]
  conv in (occs := *) length _ _ ^ 2 => all_goals rw [sq]
  perm at xcca, ybba; rw [← xcca, ← ybba, ← right_distrib, this]
