import Euclid.euclid_VI

open incidence_geometry

variables [i: incidence_geometry] {a b c d e f g h j k l m n: i.point} {L M N O P Q: i.line}

/-- colinear API -/

lemma ne_13_of_not_colinear {a b c : point} (tri_abc : ¬ colinear a b c) : a ≠ c := by
  intro ac
  obtain ⟨L, bL, cL⟩ := line_of_pts b c
  have aL : online a L := by rwa [ac.symm] at cL
  exact tri_abc ⟨L, aL, bL, cL⟩ 

lemma ne_12_of_not_colinear {a b c : point} (tri_abc : ¬ colinear a b c) : a ≠ b := by
  intro ab
  obtain ⟨L, bL, cL⟩ := line_of_pts b c
  have aL : online a L := by rwa [ab.symm] at bL
  exact tri_abc ⟨L, aL, bL, cL⟩ 

lemma ne_23_of_not_colinear {a b c : point} (tri_abc : ¬ colinear a b c) : b ≠ c := by
  intro bc
  obtain ⟨L, aL, bL⟩ := line_of_pts a b
  have cL : online c L := by rwa [bc] at bL
  exact tri_abc ⟨L, aL, bL, cL⟩ 

lemma not_colinear_T {a b c : point} (tri_abc : ¬ colinear a b c) : ¬ colinear b c a := by
  exact fun ⟨L, bL, cL, aL⟩ => tri_abc ⟨L, aL, bL, cL⟩

lemma not_colinear_R {a b c : point} (tri_abc : ¬ colinear a b c) : ¬ colinear b a c := by 
  exact fun ⟨L, aL, bL, cL⟩ => tri_abc ⟨L, bL, aL, cL⟩

/-- Aux lemmata -/

lemma aux_1 {a b c : point} (tri_abc : ¬ colinear a b c) (ang_a : rightangle ≤ angle b a c) : 
  ∃ d, B b d c ∧ angle b d a = rightangle := by
  obtain ⟨L, bL, cL⟩ := line_of_pts b c
  have naL : ¬ online a L := by exact fun h => tri_abc ⟨L, h, bL, cL⟩
  obtain ⟨d, hd₁, hd₂, hd₃⟩ := pythlem (ne_23_of_not_colinear tri_abc).symm cL bL naL ang_a
  use d
  rw [angle_symm]
  exact ⟨B_symm hd₃, hd₂⟩ 

lemma aux_2 {a b c d : point} (a_ne_b : a ≠ b) (Bbdc : B b d c) : angle a b d = angle a b c := by 
  have := angle_extension_of_B a_ne_b.symm Bbdc
  rwa [angle_symm a b d, angle_symm a b c]

/-- *** Euclid VI.31 *** -/
theorem pythagorean_proof_two {a b c : point} (tri_abc : ¬ colinear a b c) 
  (ang_a : angle b a c = rightangle) : 
    (length a b)^2 + (length a c)^2 = (length b c)^2 := by 
  have ba : length b a ≠ 0 := length_eq_zero_iff.not.mpr (ne_12_of_not_colinear tri_abc).symm
  sorry
 --
/-begin
  have ba : length b a ≠ 0 := length_eq_zero_iff.not.mpr (ne_12_of_not_colinear tri_abc).symm,
  have bc : length b c ≠ 0 := length_eq_zero_iff.not.mpr (ne_23_of_not_colinear tri_abc),
  have cb : length c b ≠ 0 := λ h, bc ((length_symm b c).trans h),
  have ca : length c a ≠ 0 := length_eq_zero_iff.not.mpr (ne_13_of_not_colinear tri_abc).symm,
  obtain ⟨d, Bbdc, ang_d⟩ := aux_1 tri_abc ang_a.symm.le,
  have tri_dba : ¬ colinear d b a,
  { rintros ⟨L, dL, bL, aL⟩,
    refine tri_abc ⟨L, aL, bL, online_3_of_B Bbdc bL dL⟩, },
  have ang_b : angle a b c = angle d b a,
  { convert (aux_2 (ne_12_of_not_colinear tri_abc) Bbdc).symm using 1,
    exact angle_symm _ _ _, },
  have xcca := (proportion_iff (length_nonneg _ _) (length_nonneg _ _) (length_nonneg _ _) 
    (length_nonneg _ _) ba bc).mpr (similar_of_AA (not_colinear_R tri_dba) (not_colinear_R tri_abc)
    ang_b.symm (ang_d.trans ang_a.symm)),
  field_simp at xcca,

  have tri_dca : ¬ colinear d c a,
  { rintros ⟨L, dL, cL, aL⟩,
    exact tri_abc ⟨L, aL, (online_3_of_B (B_symm Bbdc) cL dL), cL⟩, },
  have ang_c : angle a c b = angle d c a,
  { convert (aux_2 (ne_13_of_not_colinear tri_abc) (B_symm Bbdc)).symm using 1,
    exact angle_symm _ _ _, },
  have ang_d : angle c d a = rightangle,
  { obtain ⟨L, bL, cL⟩ := line_of_pts b c,
    convert ((angle_eq_iff_rightangle bL cL (λ aL, tri_abc ⟨L, aL, bL, cL⟩) Bbdc).mpr 
      ang_d).symm.trans ang_d using 1,
    exact angle_symm _ _ _, },
  have ybba := (proportion_iff (length_nonneg _ _) (length_nonneg _ _) (length_nonneg _ _) 
    (length_nonneg _ _) ca cb).mpr (similar_of_AA (not_colinear_R tri_dca) 
    (not_colinear_T (not_colinear_T tri_abc)) ang_c.symm ((ang_d.trans ang_a.symm).trans 
    (angle_symm b a c))),
  field_simp at ybba,
  rw ← sq at ybba xcca,
  rw [length_symm a c, length_symm a b, ← xcca, ← ybba, length_symm b c, ← right_distrib],
  have : length b d + length c d = length c b,
  { convert length_sum_of_B Bbdc using 1,
    congr' 1,
    exact length_symm _ _,
    exact length_symm _ _, },
  rw [this, sq],  end-/

