import Pythagoras.euclid_VI
open incidence_geometry
variable [i: incidence_geometry]

/-- Aux lemmata -/

lemma aux {a b c : point} (Tabc : ¬ colinear a b c) (ang_a : rightangle ≤ angle b a c) :
    ∃ d, B b d c ∧ angle b d a = rightangle ∧ angle c d a = rightangle := by
  obtain ⟨_, bL, cL⟩ := line_of_pts b c; have aL := online_1_of_triangle bL cL Tabc
  obtain ⟨d, adc, adb, Bcdb⟩ := pythlem (ne_23_of_tri Tabc).symm cL bL aL ang_a
  exact ⟨d, B_symm Bcdb, (by perma), (by perma)⟩

lemma aux2 {a b c : point} (Tabc: triangle a b c) :
    length b a ≠ 0 ∧ length c a ≠ 0 ∧ length b c ≠ 0 ∧ length c b ≠ 0 := by
  have ba := length_eq_zero_iff.not.mpr $ ne_21_of_tri Tabc
  have ca := length_eq_zero_iff.not.mpr $ ne_31_of_tri Tabc
  have bc := length_eq_zero_iff.not.mpr $ ne_23_of_tri Tabc
  have cb := fun h => bc ((length_symm b c).trans h)
  exact ⟨ ba, ca, bc, cb ⟩

lemma aux3 {a b c d : point} (Tabc: triangle a b c) (Bbdc: B b d c) :
    triangle d b a ∧ triangle d c a :=
  ⟨ fun ⟨L, dL, bL, aL⟩ => Tabc ⟨L, aL, bL, online_3_of_B Bbdc bL dL⟩,
    fun ⟨L, dL, cL, aL⟩ => Tabc ⟨L, aL, (online_3_of_B (B_symm Bbdc) cL dL), cL⟩⟩

lemma aux4 {a b c d: point} (ba: length b a ≠ 0) (Bbdc: B b d c) :
    angle d b a = angle c b a :=
  angle_extension_of_B (length_eq_zero_iff.not.mp ba) Bbdc

/-- *** Euclid VI.31 *** -/
theorem pythagorean_proof_two {a b c : point} (Tabc : triangle a b c)
    (ang_a : angle b a c = rightangle) :
    (length a b)^2 + (length a c)^2 = (length b c)^2 := by
  obtain ⟨ d, Bbdc, ang_bda, ang_cda ⟩ := aux Tabc ang_a.symm.le
  obtain ⟨ ba, ca, bc, cb ⟩ := aux2 Tabc
  obtain ⟨ Tdba, Tdca ⟩ := aux3 Tabc Bbdc
  have abc_dba : angle a b c = angle d b a := by linperm [aux4 ba Bbdc]
  have acb_dca : angle a c b = angle d c a := by linperm [aux4 ca $ B_symm Bbdc]
  have prop1 := similar_of_AA (tri213 Tdba) (tri213 Tabc) abc_dba.symm (by linarith)
  have rat1 := (proportion_len_iff _ _ _ _ _ _ _ _ ba bc).mpr prop1; field_simp at rat1
  have prop2 := similar_of_AA (tri213 Tdca) (tri312 Tabc) acb_dca.symm (by linperm)
  have rat2 := (proportion_len_iff _ _ _ _ _ _ _ _ ca cb).mpr prop2; field_simp at rat2
  perm [length_sum_of_B Bbdc]; conv in (occs := *) length _ _ ^ 2 => all_goals rw [sq]
  perm at rat1, rat2; rw [← rat1, ← rat2, ← right_distrib, this]

/-- Euclid I.11, Obtaining a perpendicular angle from a point on a line -/
theorem perpendicular_of_online'' (ab : a ≠ b) (aL : online a L) (bL : online b L)
    (fL : ¬online f L) : ∃ c, diffside c f L ∧ angle a b c = rightangle := by
  rcases length_eq_B_of_ne ab ab.symm with ⟨d, Babd, _⟩
  rcases diffside_of_not_online fL with ⟨f', f'L, ff'L⟩
  rcases perpendicular_of_online Babd aL bL f'L with ⟨c, cf'L, right, _⟩
  exact ⟨c, diffside_of_sameside_diffside (sameside_symm cf'L) ⟨f'L, fL, not_sameside_symm ff'L⟩ , by perma[right]⟩

/-- Euclid I.48, the converse to the Pythagorean theorem-/
theorem pythagoras_converse (tri_abc : triangle a b c)
  (sq_sum : (length a b)^2 + (length a c)^2 = (length b c)^2) : angle b a c = rightangle := by
rcases line_of_pts a c with ⟨L, aL, cL⟩; rcases line_of_pts a b with ⟨N, aN, bN⟩
rcases length_eq_B_of_ne_four (ne_21_of_tri tri_abc) (ne_21_of_tri tri_abc) with ⟨e, Bbae, ba_ae⟩
rcases perpendicular_of_online'' (ne_31_of_tri tri_abc) cL aL (offline_of_B_offline (B_symm Bbae)
  (online_3_of_B Bbae bN aN) aN aL cL (online_3_of_triangle aN bN tri_abc)) with ⟨d', d'eL, cad'_ra⟩
rcases length_eq_B_of_ne_four (ne_of_online aL d'eL.1).symm (ne_21_of_tri tri_abc)
  with ⟨d, Bd'ad, ba_ad⟩
rcases line_of_pts a d' with ⟨M, aM, d'M⟩
have cM := online_2_of_triangle aM d'M $ triangle_of_ne_online (ne_13_of_tri tri_abc) aL cL d'eL.1
have ang_split := two_right_of_flat_angle Bd'ad d'M aM cM
have pyth_2 := pythagorean_proof_two (triangle_of_ne_online (ne_23_of_B Bd'ad) aM
  (online_3_of_B Bd'ad d'M aM) cM) (by linperm); rw[←ba_ad] at pyth_2
have sq_eq : (length c d)^2 = (length b c)^2 := by linperm
rw[sq_eq_sq_iff_abs_eq_abs] at sq_eq; have sq_eq' : (length c d) = (length b c) :=
  by linperm[abs_of_nonneg (length_nonneg b c), abs_of_nonneg (length_nonneg c d)]
linperm[(sss (by linperm : length a d = length a b) (by linperm : length d c = length b c) rfl).2.1]
