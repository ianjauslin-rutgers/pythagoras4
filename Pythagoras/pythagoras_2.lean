import Pythagoras.euclid_VI
open incidence_geometry
variable [i: incidence_geometry]

/-- colinear API -/

lemma ne_13_of_not_colinear {a b c : point} (tri_abc : ¬ colinear a b c) : a ≠ c := fun ac => by
  obtain ⟨L, bL, cL⟩ := line_of_pts b c
  exact tri_abc ⟨L, (by rwa [← ac] at cL), bL, cL⟩

lemma ne_12_of_not_colinear {a b c : point} (tri_abc : ¬ colinear a b c) : a ≠ b := fun ab => by
  obtain ⟨L, bL, cL⟩ := line_of_pts b c
  refine' tri_abc ⟨L, (by rwa [← ab] at bL), bL, cL⟩

lemma ne_23_of_not_colinear {a b c : point} (tri_abc : ¬ colinear a b c) : b ≠ c := fun bc => by
  obtain ⟨L, aL, bL⟩ := line_of_pts a b
  exact tri_abc ⟨L, aL, bL, (by rwa [bc] at bL)⟩ 

lemma not_colinear_T {a b c : point} (tri_abc : ¬ colinear a b c) : ¬ colinear b c a :=
 fun ⟨L, bL, cL, aL⟩ => tri_abc ⟨L, aL, bL, cL⟩

lemma not_colinear_R {a b c : point} (tri_abc : ¬ colinear a b c) : ¬ colinear b a c :=
  fun ⟨L, aL, bL, cL⟩ => tri_abc ⟨L, bL, aL, cL⟩

/-- Aux lemmata -/

lemma aux_1 {a b c : point} (tri_abc : ¬ colinear a b c) (ang_a : rightangle ≤ angle b a c) : 
    ∃ d, B b d c ∧ angle b d a = rightangle := by
  obtain ⟨L, bL, cL⟩ := line_of_pts b c
  have naL : ¬ online a L := by exact fun h => tri_abc ⟨L, h, bL, cL⟩
  obtain ⟨d, -, hd₂, hd₃⟩ := pythlem (ne_23_of_not_colinear tri_abc).symm cL bL naL ang_a
  exact ⟨d, B_symm hd₃, (by perma)⟩

lemma aux_2 {a b c d : point} (a_ne_b : a ≠ b) (Bbdc : B b d c) : angle a b d = angle a b c := by 
  perma [angle_extension_of_B a_ne_b.symm Bbdc]

/-- *** Euclid VI.31 *** -/
theorem pythagorean_proof_two {a b c : point} (tri_abc : ¬ colinear a b c) 
    (ang_a : angle b a c = rightangle) : 
    (length a b)^2 + (length a c)^2 = (length b c)^2 := by 
  have ba : length b a ≠ 0 := length_eq_zero_iff.not.mpr (ne_12_of_not_colinear tri_abc).symm
  have bc : length b c ≠ 0 := length_eq_zero_iff.not.mpr (ne_23_of_not_colinear tri_abc)
  have cb : length c b ≠ 0 := fun h => bc ((length_symm b c).trans h)
  have ca : length c a ≠ 0 := length_eq_zero_iff.not.mpr (ne_13_of_not_colinear tri_abc).symm
  obtain ⟨d, Bbdc, ang_d⟩ := aux_1 tri_abc ang_a.symm.le
  have tri_dba : ¬ colinear d b a := 
    fun ⟨L, dL, bL, aL⟩ => tri_abc ⟨L, aL, bL, online_3_of_B Bbdc bL dL⟩
  have ang_b : angle a b c = angle d b a := by
    linperm [aux_2 (ne_12_of_not_colinear tri_abc) Bbdc]
  have xcca := (proportion_iff (length_nonneg _ _) (length_nonneg _ _) (length_nonneg _ _) 
    (length_nonneg _ _) ba bc).mpr (similar_of_AA (not_colinear_R tri_dba) (not_colinear_R tri_abc)
    ang_b.symm (ang_d.trans ang_a.symm))
  field_simp at xcca
  have tri_dca : ¬ colinear d c a := fun ⟨L, dL, cL, aL⟩ =>
   tri_abc ⟨L, aL, (online_3_of_B (B_symm Bbdc) cL dL), cL⟩
  have ang_c : angle a c b = angle d c a := by
    linperm [aux_2 (ne_13_of_not_colinear tri_abc) (B_symm Bbdc)]
  have ang_d : angle c d a = rightangle := by
    obtain ⟨L, bL, cL⟩ := line_of_pts b c
    linperm [(angle_eq_iff_rightangle bL cL (fun aL => tri_abc ⟨L, aL, bL, cL⟩) Bbdc).mpr ang_d]
  have ybba := (proportion_iff (length_nonneg _ _) (length_nonneg _ _) (length_nonneg _ _) 
    (length_nonneg _ _) ca cb).mpr (similar_of_AA (not_colinear_R tri_dca) 
    (not_colinear_T (not_colinear_T tri_abc)) ang_c.symm ((ang_d.trans ang_a.symm).trans (by perm)))
  field_simp at ybba; perm [length_sum_of_B Bbdc]
  conv in (occs := *) length _ _ ^ 2 => all_goals rw [sq]
  perm at xcca, ybba; rw [← xcca, ← ybba, ← right_distrib, this]
