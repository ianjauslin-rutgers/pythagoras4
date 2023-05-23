import SyntheticEuclid4
import Pythagoras.proportion
import Pythagoras.euclid_I_extras
import Std.Tactic.ShowTerm
import Mathlib.Tactic.WLOG

open incidence_geometry
variable [i: incidence_geometry]

/-- technical lemma that really shouldn't be here, but hey... -/
lemma mul_mul_lt (a b c : ℝ) (hc: 0 < c):
    a<b → a*c<b*c := (mul_lt_mul_right hc).mpr
/-- technical lemma that really shouldn't be here, but hey... -/
lemma ge2_of_n1_n0 {n : ℕ}
    (h0: n ≠ 0) (h1: n ≠ 1) :
    n ≥ 2 := ge_iff_le.mpr ((Nat.two_le_iff n).mpr ⟨ h0, h1 ⟩)
/-- technical lemma that really shouldn't be here, but hey... -/
lemma gt1_of_n1_n0 {n : ℕ}
    (h0: n ≠ 0) (h1: n ≠ 1) :
    n > 1 := gt_iff_lt.mpr (lt_of_lt_of_le one_lt_two (ge_iff_le.mp (ge2_of_n1_n0 h0 h1)))

/-- from segment of length l, construct a new segment of length n*l
    based on I.3 -/
lemma rescale_length {a b : point} {L : line} (n : ℕ)
    (haL: online a L)
    (hbL: online b L) :
    ∃ (c : point), (online c L) ∧ (length a c = n*(length a b)) ∧ (n ≥ 2 ∧ a ≠ b → B a b c) := by
  -- trivial case
  by_cases h_a_ne_b: a = b
  · use a
    rw [h_a_ne_b.symm]
    rw [length_eq_zero_iff.mpr,mul_zero]
    simp [eq_self_iff_true, Ne.def, not_true, and_false, IsEmpty.forall_iff, and_true]
    exact haL
    simp [eq_self_iff_true]

  induction n with
  | zero =>
    use a
    rw [length_eq_zero_iff.mpr]
    simp [Nat.zero_eq, Nat.cast_zero, zero_mul, ne_eq, false_and, IsEmpty.forall_iff, and_self, and_true]
    exact haL
    simp [eq_self_iff_true]

  | succ n hn =>
    -- trivial case: n=0
    by_cases hnz:(n=0)
    · use b
      constructor
      exact hbL
      rw [hnz]
      simp [Nat.cast_succ, Nat.cast_zero, zero_add, one_mul, ne_eq, false_and, IsEmpty.forall_iff, and_self]

    -- separate case n=1
    by_cases h_n_ne_1 : n=1
    · obtain ⟨ e, he ⟩ := length_eq_B_of_ne_four h_a_ne_b h_a_ne_b
      use e
      simp [Nat.cast_succ, ge_iff_le, ne_eq, and_imp]
      rw [(length_sum_of_B he.1).symm,he.2, h_n_ne_1]
      ring_nf
      simp [forall_true_left, true_and]

      constructor
      exact online_3_of_B he.1 haL hbL
      intro
      exact he.1

    -- extract point from hn
    obtain ⟨ d, hd ⟩ := hn
    have h_a_ne_d : a ≠ d := by
      convert nq_of_len_pos _
      rw [hd.2.1]
      simp [Nat.pos_of_ne_zero hnz, zero_lt_mul_left, Nat.cast_pos]
      exact len_pos_of_nq h_a_ne_b
    obtain ⟨ e, he ⟩ := length_eq_B_of_ne_four h_a_ne_d h_a_ne_b
    use e
    rw [(length_sum_of_B he.1).symm, hd.2.1, he.2]
    simp [Nat.cast_succ, ge_iff_le, Ne.def, and_imp]
    ring_nf
    simp [eq_self_iff_true, true_and]

    constructor
    exact online_3_of_B he.1 haL hd.1

    have : n ≥ 2 ∧ a ≠ b := ⟨ ge2_of_n1_n0 hnz h_n_ne_1, h_a_ne_b ⟩
    have := hd.2.2 this

    intros
    exact B124_of_B134_B123 he.1 this


/-- rescale base of triangle -/
-- workhorse: version for use in inductive case
lemma rescale_triangle_of_base__inductive (a : point) {b c : point} {L : line} {n : ℕ}
    (hbL: online b L)
    (hcL: online c L)
    (h_a_nonline_L: ¬ online a L) :
    ∀ d:point, (online d L) → (length b d = n*(length b c)) → B b c d → area a b d = n * (area a b c) := by
  induction n with
  | zero =>
    intros d _ hlen _
    simp [Nat.zero_eq, Nat.cast_zero, zero_mul]
    simp [Nat.zero_eq, Nat.cast_zero, zero_mul] at hlen
    rw [length_eq_zero_iff.mp hlen, area_of_eq a d d _]
    tauto

  | succ n hn =>
    intros d hdL hlen hB

    have h_b_ne_c := ne_12_of_B hB
    have h_b_ne_d := ne_13_of_B hB
    have h_c_ne_d := ne_23_of_B hB

    -- trivial case: n=0
    by_cases h_n_ne_0 : n = 0
    · exfalso
      rw [h_n_ne_0] at hlen
      simp [Nat.cast_succ, Nat.cast_zero, zero_add, one_mul] at hlen
      rw [Eq.symm (length_sum_of_B hB)] at hlen
      simp [add_right_eq_self] at hlen
      exact h_c_ne_d (length_eq_zero_iff.mp hlen)

    -- special case: n=1
    by_cases h_n_ne_1 : n = 1
    · rw [h_n_ne_1]
      simp [Nat.cast_succ, Nat.cast_one]
      ring_nf

      rw [((area_add_iff_B h_b_ne_c h_c_ne_d h_b_ne_d.symm hbL hcL hdL h_a_nonline_L).mp hB).symm]
      simp [mul_two]; perm
      apply (eq_area_of_eq_base_samevertex a hbL hcL hcL hdL _).symm

      rw [h_n_ne_1, (length_sum_of_B hB).symm] at hlen
      simp [Nat.cast_succ, Nat.cast_one] at hlen
      linarith

    -- split off n+1'st bit
    simp [Nat.cast_succ]; rw [add_mul]; simp [one_mul]

    -- construct n-triangle
    obtain ⟨ e, he ⟩ := rescale_length n hbL hcL
    have h_B_bce := he.2.2 ⟨ ge2_of_n1_n0 h_n_ne_0 h_n_ne_1, h_b_ne_c ⟩
    rw [Eq.symm (hn e he.1 he.2.1 h_B_bce)]

    have h_b_ne_e := ne_13_of_B h_B_bce
    have h_e_ne_d : e ≠ d := by
      by_contra contra
      have := he.2.1
      rw [contra] at this
      have := Eq.trans this.symm hlen
      simp [Nat.cast_succ, mul_eq_mul_right_iff, self_eq_add_right, one_ne_zero, false_or] at this
      exact h_b_ne_c (length_eq_zero_iff.mp this)

    -- split abd
    have h_B_bed : B b e d := by
      have' := B_of_three_online_ne_short _ h_b_ne_e h_b_ne_d h_e_ne_d hbL he.1 hdL
      
      cases this with
      | inl h => exact h
      | inr h =>
        exfalso
        apply not_B324_of_B123_B124 h_B_bce hB
        exact B124_of_B134_B123 h (B_symm h_B_bce)

      rw [he.2.1, hlen]
      simp [Nat.cast_succ]
      have : ↑n < ↑n+1 := by simp
      linarith [len_pos_of_nq h_b_ne_c]
    
    rw [((area_add_iff_B h_b_ne_e h_e_ne_d h_b_ne_d.symm hbL he.1 hdL h_a_nonline_L).mp h_B_bed).symm]

    have' := eq_area_of_eq_base_samevertex a hbL hcL he.1 hdL _
    perm at *; rw [this]

    have := length_sum_of_B h_B_bed
    rw [hlen, he.2.1] at this
    simp [one_mul] at this
    linarith

-- lemma with B b c d as a hypothesis
lemma rescale_triangle_of_base__B (a : point) {b c d : point} {L : line} {n : ℕ}
    (hbL: online b L)
    (hcL: online c L)
    (hdL: online d L)
    (hlen: length b d = n * (length b c))
    (hB: B b c d)
    (h_a_nonline_L: ¬ online a L) :
    area a b d = n * (area a b c) := by
  exact rescale_triangle_of_base__inductive a hbL hcL h_a_nonline_L d hdL hlen hB

-- not B c b d
lemma rescale_triangle_of_base__notcbd (a : point) {b c d : point} {L : line} {n : ℕ}
    (hbL: online b L)
    (hcL: online c L)
    (hdL: online d L)
    (hlen: length b d = n*(length b c))
    (hB: ¬ B c b d)
    (h_b_ne_c: b ≠ c)
    (h_n_ne_0: n ≠ 0)
    (h_b_ne_d: b ≠ d)
    (h_a_nonline_L: ¬ online a L) :
    area a b d = n*(area a b c) := by
  -- trivial case: n=1
  by_cases h_n_ne_1 : n=1
  · rw [h_n_ne_1] at hlen; rw [h_n_ne_1]
    simp [Nat.cast_one] at hlen; simp [Nat.cast_one]
    exact Eq.symm (eq_area_of_eq_base_samevertex a hbL hcL hbL hdL hlen.symm)

  have h_c_ne_d: c ≠ d := by
    by_contra contra
    rw [contra] at hlen
    have hnz :=(not_iff_not.mpr length_eq_zero_iff).mpr h_b_ne_d
    have := (mul_left_inj' hnz).mp (Eq.trans (one_mul (length b d)) hlen)
    norm_cast at this
    exact h_n_ne_1 this.symm

  have' hBs := B_of_three_online_ne_short _ h_b_ne_c h_b_ne_d h_c_ne_d hbL hcL hdL
  cases hBs with
  | inl hBs =>
    exact rescale_triangle_of_base__B a hbL hcL hdL hlen hBs h_a_nonline_L
  | inr hBs =>
    exfalso
    exact hB hBs

  rw [hlen]
  have := len_pos_of_nq h_b_ne_c
  have n_ge1 := gt1_of_n1_n0 h_n_ne_0 h_n_ne_1
  rw [gt_iff_lt] at n_ge1
  simp [*]

-- full version
lemma rescale_triangle_of_base (a : point) {b c d : point} {L : line} {n : ℕ}
    (hbL: online b L)
    (hcL: online c L)
    (hdL: online d L)
    (hlen: length b d = n*(length b c)) :
    area a b d = n*(area a b c) := by
  -- trivial case: b=c
  by_cases h_b_ne_c : b = c
  · rw [length_eq_zero_iff.mpr h_b_ne_c] at hlen
    simp [mul_zero] at hlen
    have := length_eq_zero_iff.mp hlen
    rw [(area_of_eq a b d _)]
    rw [(area_of_eq a b c _)]
    simp [mul_zero]
    repeat tauto

  -- trivial case: n = 0
  by_cases h_n_ne_0 : n = 0
  · rw [h_n_ne_0]
    simp [Nat.cast_zero]
    rw [area_of_eq a b d _]
    rw [h_n_ne_0] at hlen
    simp [Nat.cast_zero] at hlen
    have := length_eq_zero_iff.mp hlen
    tauto

  have h_b_ne_d: b ≠ d := by
    by_contra contra
    have := length_eq_zero_iff.mpr contra
    rw [this] at hlen
    simp [zero_eq_mul, Nat.cast_eq_zero] at hlen
    cases hlen with
    | inl hlen => exact h_n_ne_0 hlen
    | inr hlen => exact h_b_ne_c (length_eq_zero_iff.mp hlen)

  -- trivial case: online a L
  by_cases h_a_nonline_L : online a L
  · perm [(area_zero_iff_online h_b_ne_c hbL hcL).mpr h_a_nonline_L]; rw [this]
    perm [(area_zero_iff_online h_b_ne_d hbL hdL).mpr h_a_nonline_L]; rw [this]
    simp [mul_zero]

  by_cases h_B_cbd : B c b d
    -- reflect c about b
  · obtain ⟨ e, he ⟩ := rescale_length 2 hcL hbL
    have h_B_cbe : B c b e := by
      have : 2 ≥ 2 ∧ c ≠ b := by
        constructor
        simp [ge_iff_le]
        rw [(Ne.def b c).symm] at h_b_ne_c
        exact h_b_ne_c.symm
      exact  he.2.2 this

    have lbe : length b e = length b c := by
      have := length_sum_of_B h_B_cbe
      rw [he.2.1, length_symm c b] at this
      norm_cast at this
      linarith

    rw [lbe.symm] at hlen

    have := not_B324_of_B123_B124 h_B_cbe h_B_cbd

    rw [rescale_triangle_of_base__notcbd a hbL he.1 hdL hlen this (ne_23_of_B h_B_cbe) h_n_ne_0 h_b_ne_d h_a_nonline_L]
    rw [eq_area_of_eq_base_samevertex a hbL he.1 hbL hcL lbe]

  exact rescale_triangle_of_base__notcbd a hbL hcL hdL hlen h_B_cbd h_b_ne_c h_n_ne_0 h_b_ne_d h_a_nonline_L


/-- triangles between parallels with smaller base have smaller area -/
-- case where they share a side and have the right betweeneness
lemma lt_area_of_lt_base__sameedge_Bbfc (a : point) {b c f: point} {L: line}
    (hbL: online b L)
    (hcL: online c L)
    (hfL: online f L)
    (hB: B b f c)
    (h_b_ne_c: b ≠ c)
    (h_b_ne_f: b ≠ f)
    (h_c_ne_f: c ≠ f)
    (h_a_nonline_L: ¬ online a L) :
    (length b c) > (length b f) → (area a b c) > (area a b f) := by
  intro
  have := (area_add_iff_B h_b_ne_f h_c_ne_f.symm h_b_ne_c.symm hbL hfL hcL h_a_nonline_L).mp hB
  rw [← this]; simp [gt_iff_lt, lt_add_iff_pos_right]

  have : area a c f ≠ 0 := by
    by_contra contra
    apply h_a_nonline_L
    apply (area_zero_iff_online h_c_ne_f hcL hfL).mp (by perma only [area] at *)
  exact (Ne.symm this).lt_of_le (area_nonneg a c f)

-- case where they share a side and not B f b c
lemma lt_area_of_lt_base__sameedge_nBfbc (a : point) {b c f: point} {L: line}
    (hbL: online b L)
    (hcL: online c L)
    (hfL: online f L)
    (h_b_ne_c: b ≠ c)
    (h_b_ne_f: b ≠ f)
    (h_a_nonline_L: ¬ online a L)
    (hB: ¬ B f b c) :
    (length b c) > (length b f) → (area a b c) > (area a b f) := by
  intro hlen
  simp [gt_iff_lt] at hlen

  have h_c_ne_f: c ≠ f := by
    by_contra contra
    rw [contra] at hlen
    simp [lt_self_iff_false] at hlen

  have := B_of_three_online_ne_short hlen h_b_ne_f h_b_ne_c h_c_ne_f.symm hbL hfL hcL

  cases this with
  | inl h =>
    exact lt_area_of_lt_base__sameedge_Bbfc a hbL hcL hfL h h_b_ne_c h_b_ne_f h_c_ne_f h_a_nonline_L hlen
  | inr h =>
    exfalso
    exact hB h

-- case where they share a side
lemma lt_area_of_lt_base__sameedge (a : point) {b c f: point} {L: line}
    (hbL: online b L)
    (hcL: online c L)
    (hfL: online f L)
    (h_b_ne_c: b ≠ c)
    (h_b_ne_f: b ≠ f)
    (h_a_nonline_L: ¬ online a L) :
    (length b c) > (length b f) → (area a b c) > (area a b f) := by
  intro hlen

  by_cases hB: B f b c
    -- reflect f about b
  · obtain ⟨ e, he ⟩ := rescale_length 2 hfL hbL
    have : 2 ≥ 2 := by simp [ge_iff_le]
    have h_B_fbe := he.2.2 ⟨ this, h_b_ne_f.symm ⟩
    have lbe : length b e = length b f := by
      have := length_sum_of_B h_B_fbe
      rw [he.2.1, length_symm f b] at this
      norm_cast at this
      linarith
    rw [lbe.symm] at hlen

    rw [(eq_area_of_eq_base_samevertex a hbL he.1 hbL hfL lbe).symm]

    have := not_B324_of_B123_B124 h_B_fbe hB
    exact lt_area_of_lt_base__sameedge_nBfbc a hbL hcL he.1 h_b_ne_c (ne_23_of_B h_B_fbe) h_a_nonline_L this hlen
  
  exact lt_area_of_lt_base__sameedge_nBfbc a hbL hcL hfL h_b_ne_c h_b_ne_f h_a_nonline_L hB hlen

-- general case
lemma lt_area_of_lt_base {a b c d e f: point} {L M: line}
    (haM: online a M)
    (hbL: online b L)
    (hcL: online c L)
    (hdM: online d M)
    (heL: online e L)
    (hfL: online f L)
    (hpar: para L M) :
    (length b c) > (length e f) → (area a b c) > (area d e f) := by

  intro hlen

  have h_b_ne_c: b ≠ c := by
    by_contra contra
    rw [(length_eq_zero_iff.mpr contra)] at hlen
    exact (not_le_of_gt hlen) (length_nonneg e f)

  have h_a_nonline_L := offline_of_para haM (para_symm hpar)
  have h_d_nonline_L := offline_of_para hdM (para_symm hpar)

  -- trivial case: e=f
  by_cases h_e_ne_f: e=f
  · simp [gt_iff_lt]
    rw [area_of_eq d e f _]
    perm [(area_zero_iff_online h_b_ne_c hbL hcL).not.mpr h_a_nonline_L]
    exact (Ne.symm this).lt_of_le (area_nonneg a b c)
    tauto

  -- construct parallelogram from d e f
  obtain ⟨ O, hdO, heO ⟩ := line_of_pts d e
  have := not_online_of_triangle hdO heO heL hfL h_d_nonline_L h_e_ne_f
  obtain ⟨ g, N, hgM, hgN, hfN, pON ⟩ := parallel_projection hfL hpar (not_para_of_online_online heO heL) this

  have pg : paragram e f g d L N M O := by splitAll <;> perma only [para] at *

  have hlen_ef_dg := (len_ang_area_eq_of_parallelogram pg ).1
  rw [length_symm g d] at hlen_ef_dg

  have h_d_ne_g : d ≠ g := by
    have := length_eq_zero_iff.not.mpr h_e_ne_f
    rw [hlen_ef_dg] at this
    exact length_eq_zero_iff.not.mp this

  -- construct parallelogram from b d g
  obtain ⟨ P, hbP, hdP ⟩ := line_of_pts b d
  have := not_online_of_triangle hbP hdP hdM hgM (offline_of_para hbL hpar) h_d_ne_g
  obtain ⟨ h, R, hhL, hhR, hGR, pPR ⟩ := parallel_projection hgM (para_symm hpar) (not_para_of_online_online hdP hdM) this

  have pg2 : paragram b h g d L R M P := by splitAll <;> perma only [para]

  have hlen_ef_bh : length e f = length b h := by
    linperm [(len_ang_area_eq_of_parallelogram pg2).1]

  have h_b_ne_h : b ≠ h := by
    have := length_eq_zero_iff.not.mpr h_e_ne_f
    rw [hlen_ef_bh] at this
    exact length_eq_zero_iff.not.mp this

  have : length b c > length b h := by
    rw [hlen_ef_bh.symm]
    exact hlen

  rw [eq_area_of_eq_base hdM heL hfL haM hbL hhL hpar hlen_ef_bh]

  exact lt_area_of_lt_base__sameedge a hbL hcL hhL h_b_ne_c h_b_ne_h h_a_nonline_L this
  

/-- ## Euclid VI.1
two triangles in between parallel lines have their area in proportion with the length of their base
 https://mathcs.clarku.edu/~djoyce/java/elements/bookVI/propVI1.html -/
theorem proportion_area_of_proportion_base {a b c d e f: point} {L M : line}
    (haM: online a M)
    (hbL: online b L)
    (hcL: online c L)
    (hdM: online d M)
    (heL: online e L)
    (hfL: online f L)
    (hpar: para L M) :
    proportion (length b c) (length e f) (area a b c) (area d e f) := by

  refine' ⟨ length_nonneg b c, length_nonneg e f, area_nonneg a b c, area_nonneg d e f, _ ⟩
  intros n m

  obtain ⟨ h, hh ⟩ := rescale_length n hbL hcL
  obtain ⟨ l, hl ⟩ := rescale_length m heL hfL

  rw [(rescale_triangle_of_base a hbL hcL hh.1 hh.2.1).symm, hh.2.1.symm]
  rw [(rescale_triangle_of_base d heL hfL hl.1 hl.2.1).symm, hl.2.1.symm]

  exact ⟨ eq_area_of_eq_base haM hbL hh.1 hdM heL hl.1 hpar,
          lt_area_of_lt_base hdM heL hl.1 haM hbL hh.1 hpar,
          lt_area_of_lt_base haM hbL hh.1 hdM heL hl.1 hpar ⟩
  

/-- version where the vertex is the same for both triangles -/
theorem proportion_area_of_proportion_base_samevertex (a : point) {b c e f: point} {L : line}
    (hbL: online b L)
    (hcL: online c L)
    (heL: online e L)
    (hfL: online f L)
    (h_a_nonline_L: ¬ online a L) :
    proportion (length b c) (length e f) (area a b c) (area a e f) := by
  obtain ⟨ M, hM ⟩ := parallel_of_line_pt h_a_nonline_L
  exact proportion_area_of_proportion_base hM.1 hbL hcL hM.1 heL hfL hM.2


/-- ## Euclid VI.2
a line cuts the sides of the triangle proportionally iff it is parallel to one of the sides of a triangle (version BD:AD = CE:AE)
 https://mathcs.clarku.edu/~djoyce/java/elements/bookVI/propVI2.html -/
theorem proportional_iff_para {a b c d e: point} {L M N: line}
    (hdL: online d L) (heL: online e L)
    (hbM: online b M) (hcM: online c M)
    (haN: online a N) (hdN: online d N)
    (hneN: ¬ online e N)
    (Badb : B a d b) (Baec : B a e c) :
    proportion (length b d) (length a d) (length c e) (length a e) ↔ para L M := by
  have hbN := online_3_of_B Badb haN hdN
  obtain ⟨O, haO, heO⟩ := line_of_pts a e
  have hcO := online_3_of_B Baec haO heO
  obtain ⟨P, hcP, hdP⟩ := line_of_pts c d

  -- non-degeneracy
  have ab : a ≠ b := ne_13_of_B Badb
  have ae : a ≠ e := ne_12_of_B Baec
  have ad : a ≠ d := ne_12_of_B Badb
  have bd : b ≠ d := ne_12_of_B (B_symm Badb)
  have ce : c ≠ e := ne_12_of_B (B_symm Baec)
  have NO : N ≠ O := by
    by_contra contra
    exact hneN (by rwa [← contra] at heO)
  have PO : P ≠ O := by
    by_contra contra
    exact NO (line_unique_of_pts ad haO (by rwa [contra] at hdP) haN hdN).symm
  have hndO: ¬ online d O := by
    by_contra contra
    exact NO (line_unique_of_pts ad haN hdN haO contra)
  have hnaL := fun haL => hneN (by rwa [line_unique_of_pts ad haL hdL haN hdN] at heL)
  have hnbL := fun hbL => hneN (by rwa [line_unique_of_pts bd hbL hdL hbN hdN] at heL)
  have hncL:= fun hcL => (by rwa [← line_unique_of_pts ce hcO heO hcL heL] at hnaL : ¬ online a O) haO
  have bc : b ≠ c := by
    by_contra contra
    exact NO (line_unique_of_pts ab haN hbN haO (by rwa [contra.symm] at hcO))
  have cd : c ≠ d := by
    by_contra contra
    rw [contra.symm] at hndO
    exact hndO hcO
  have hneP : ¬ online e P := by
    by_contra contra
    exact PO (line_unique_of_pts ce hcP contra hcO heO)

  have hbdad : proportion (length b d) (length a d) (area e b d) (area e a d) := by
    exact proportion_area_of_proportion_base_samevertex e hbN hdN haN hdN hneN
  have hceae : proportion (length c e) (length a e) (area d c e) (area d a e) := by
   exact proportion_area_of_proportion_base_samevertex d hcO heO haO heO hndO
  have len_ad_neq_0 : length a d ≠ 0 := by
    by_contra contra
    exact ad (length_eq_zero_iff.1 contra)
  have len_ae_neq_0 : length a e ≠ 0 := by
    by_contra contra
    exact ae (length_eq_zero_iff.1 contra)
  have area_ade_neq_0 : area a d e ≠ 0 := by
    by_contra contra
    exact hneN ((area_zero_iff_online ad haN hdN).1 contra)
  
  have ratio_iff : length b d / length a d = length c e / length a e ↔ area e b d / area e a d = area d c e / area d a e := by
    perm at *
    rw [eq_ratio_of_proportion len_ad_neq_0 area_ade_neq_0 hbdad,
       eq_ratio_of_proportion len_ae_neq_0 area_ade_neq_0 hceae]

  have proportion_lhs : proportion (length b d) (length a d) (length c e) (length a e) ↔ area e b d / area e a d = area d c e / area d a e := by
    rwa [← proportion_iff (length_nonneg b d) (length_nonneg a d) (length_nonneg c e) (length_nonneg a e) (len_ad_neq_0) (len_ae_neq_0)]
  have area_bde_eq_cde : proportion (length b d) (length a d) (length c e) (length a e) ↔ area b d e = area c d e := by
    rw [proportion_lhs]; perm; field_simp
  
  -- apply I.39
  constructor
  intro harea
  rw [area_bde_eq_cde] at harea
  have nsabL:= not_sameside13_of_B123_online2 Badb hdL
  have nsacL:= not_sameside13_of_B123_online2 Baec heL
  have ssbcL := sameside_of_diffside_diffside ⟨hnaL, hnbL, nsabL⟩ ⟨hnaL, hncL, nsacL⟩
  exact eq_area_of_same_base_implies_para hdL heL hnbL hbM hcM hdP hcP hneP bc cd.symm ssbcL harea

  -- apply I.37
  intro pLM
  rw [area_bde_eq_cde]
  exact para_implies_eq_area_of_same_base hbM hcM hdL heL pLM


/-- ## Euclid VI.2'
a line cuts the sides of the triangle proportionally iff it is parallel to one of the sides of a triangle (version AB:AD = AC:AE)
 https://mathcs.clarku.edu/~djoyce/java/elements/bookVI/propVI2.html -/
theorem proportional_iff_para' {a b c d e: point} {L M N: line}
    (hdL: online d L) (heL: online e L)
    (hbM: online b M) (hcM: online c M)
    (haN: online a N) (hdN: online d N)
    (hneN: ¬ online e N)
    (Badb : B a d b) (Baec : B a e c) :
    proportion (length a b) (length a d) (length a c) (length a e) ↔ para L M := by
  have ad : length a d ≠ 0 := length_eq_zero_iff.not.mpr (ne_12_of_B Badb)
  have ae : length a e ≠ 0 := length_eq_zero_iff.not.mpr (ne_12_of_B Baec)

  have := proportional_iff_para hdL heL hbM hcM haN hdN hneN Badb Baec

  rw [(proportion_iff (length_nonneg a b) (length_nonneg a d) (length_nonneg a c) (length_nonneg a e) ad ae).symm]
  rw [(proportion_iff (length_nonneg b d) (length_nonneg a d) (length_nonneg c e) (length_nonneg a e) ad ae).symm] at this
  rw [(length_sum_of_B Badb).symm, (length_sum_of_B Baec).symm]
  field_simp [*]; rw [← this]; perm; field_simp; ring_nf; simp [*]

/-- equal points are colinear -/
lemma colinear_of_eq_23 (a b : point) :
    colinear a b b := by
  dsimp [colinear]
  simp [and_self]
  exact line_of_pts a b

/-- equal points are colinear -/
lemma colinear_of_eq_12 (a b : point) :
    colinear a a b := by
  rw [col321]
  exact colinear_of_eq_23 b a

/-- equal points are colinear -/
lemma colinear_of_eq_13 (a b : point) :
    colinear a b a := by perma [colinear_of_eq_12 a b]

/-- not colinear implies different -/
lemma neq_12_of_not_colinear {a b c : point} (h: ¬ colinear a b c) :
    a ≠ b := by
  by_contra contra
  rw [contra] at h
  exact h (colinear_of_eq_12 b c)
/-- not colinear implies different -/
lemma neq_13_of_not_colinear {a b c : point} (h: ¬ colinear a b c) :
    a ≠ c := by
  by_contra contra
  rw [contra] at h
  exact h (colinear_of_eq_13 c b)
/-- not colinear implies different -/
lemma neq_23_of_not_colinear {a b c : point} (h: ¬ colinear a b c) :
    b ≠ c := by
  by_contra contra
  rw [contra] at h
  exact h (colinear_of_eq_23 a c)

/-- not colinear implies one of the points is not aligned -/
lemma not_online_of_not_colinear {a b c : point} {L : line} (haL: online a L) (hbL : online b L) (h: ¬ colinear a b c) :
    ¬ online c L := by
  dsimp [colinear] at h
  simp [not_exists, not_and] at h
  exact h L haL hbL
    
/-- technical lemma: can always find a point beyond two points -/
lemma pt_extension_of_ne {b c : point} :
    b ≠ c → ∃ a : point, B b c a := by
  intro hbc
  obtain ⟨ a, ha ⟩ := length_eq_B_of_ne hbc hbc.symm
  use a
  exact ha.1

/-- similar triangles (should follow from Euclid VI.2) -/
-- show resulting lines are parallel
lemma parallel_of_similar {a b c g h : point} {AB AC BC HG: line}
    (haAB: online a AB) (hbAB: online b AB) (hhAB: online h AB)
    (haAC: online a AC) (hgAC: online g AC)
    (hbBC: online b BC) (hcBC: online c BC)
    (hhHG: online h HG) (hgHG: online g HG)
    (b_ne_h: b ≠ h)
    (a_ne_b: a ≠ b)
    (b_ne_c: b ≠ c)
    (h_ne_g: h ≠ g)
    (a_ne_g: a ≠ g)
    (b_nonline_AC: ¬ online b AC)
    (an: angle a h g = angle a b c)
    (hB: B a h b)
    (hss: sameside g c AB) :
    para BC HG := by

  have hbc_abc : angle h b c = angle a b c := by
    refine' angle_extension b_ne_h.symm a_ne_b b_ne_c.symm b_ne_c.symm hbAB hhAB haAB hbBC hcBC hcBC (not_B_of_B (B_symm hB)) _
    by_contra contra
    apply ne_13_of_B contra
    rfl

  have AB_ne_HG: AB ≠ HG := by
    by_contra AB_HG
    rw [AB_HG] at haAB
    have : a = g := by
      by_contra contra
      have := line_unique_of_pts contra haAC hgAC haAB hgHG
      rw [AB_HG.symm] at this
      rw [this.symm] at hbAB
      exact b_nonline_AC hbAB
    exact a_ne_g this

  -- point on other side of h on line hg
  obtain ⟨t, ht, -⟩ := length_eq_B_of_ne h_ne_g.symm h_ne_g
  have htHG := online_3_of_B ht hgHG hhHG

  have hntAB : ¬ online t AB := by
    by_contra contra
    have AB_HG := line_unique_of_pts (ne_23_of_B ht).symm contra hhAB htHG hhHG
    exact AB_ne_HG AB_HG

  have hngAB : ¬ online g AB := by
    by_contra contra
    have AB_HG := line_unique_of_pts (ne_12_of_B ht) contra hhAB hgHG hhHG
    exact AB_ne_HG AB_HG

  apply para_of_ang_eq b_ne_h hcBC hbBC hbAB hhAB hhHG htHG _ _

  have nss := not_sameside13_of_B123_online2 ht hhAB
  exact diffside_of_sameside_diffside hss ⟨hngAB, hntAB, nss⟩ 

  have ahg_thb := vertical_angle hB ht haAB hhAB hngAB
  rw [hbc_abc, ← an, ahg_thb]

/-- two similar triangles that share an edge are equal -/
lemma length_eq_of_length_eq {a b c d e f : point}
    (tri_abc : ¬ colinear a b c) (tri_def : ¬ colinear d e f) 
    (ang_a_eq_d : angle b a c = angle e d f) (ang_b_eq_e : angle a b c = angle d e f)
    (leq: length d f = length a c) :
    length d e = length a b := by
  have d_ne_f := neq_13_of_not_colinear tri_def
  have a_ne_c := neq_13_of_not_colinear tri_abc
  have d_ne_e := neq_12_of_not_colinear tri_def
  have a_ne_b := neq_12_of_not_colinear tri_abc
  have b_ne_c := neq_23_of_not_colinear tri_abc
  have e_ne_f := neq_23_of_not_colinear tri_def

  obtain ⟨AC, hAC⟩ := line_of_pts a c
  obtain ⟨AB, hAB⟩ := line_of_pts a b
  obtain ⟨BC, hBC⟩ := line_of_pts b c
  have c_nonline_AB := not_online_of_not_colinear hAB.1 hAB.2 tri_abc

  have b_nonline_AC : ¬online b AC := not_online_of_not_colinear hAC.1 hAC.2 (by perma)

  by_contra contra
  rw [(Ne.def (length d e) (length a b)).symm] at contra
  simp_rw [ne_iff_lt_or_gt] at contra

  wlog lineq : length a b < length d e
  swap

  obtain ⟨h, hh⟩ := same_length_B_of_ne_ge a_ne_b lineq
  obtain ⟨HC, hHC⟩ := line_of_pts h c

  have h_online_AB := online_3_of_B hh.1 hAB.1 hAB.2
  have h_ne_c : h ≠ c := by
    by_contra contra
    exact c_nonline_AB (by rwa [contra] at h_online_AB)

  have h_nonline_AC : ¬ online h AC := by
    by_contra contra
    have := line_unique_of_pts (ne_13_of_B hh.1).symm contra hAC.1 h_online_AB hAB.1
    rw [this] at b_nonline_AC
    exact b_nonline_AC hAB.2

  have hac_bac := (angle_extension_of_B a_ne_c hh.1).symm
  rw [hac_bac.symm] at ang_a_eq_d
  have ang_b_eq_h := sas leq.symm hh.2 (by perma only [angle] at *)
  rw [ang_b_eq_e.symm] at ang_b_eq_h

  have := parallel_of_similar hAB.1 h_online_AB hAB.2 hAC.1 hAC.2 hHC.1 hHC.2 hBC.1 hBC.2 (ne_23_of_B hh.1).symm (ne_13_of_B hh.1) h_ne_c b_ne_c a_ne_c h_nonline_AC ang_b_eq_h.2.2.symm hh.1 (sameside_rfl_of_not_online c_nonline_AB)

  exact neq_of_para hHC.2 hBC.2 this rfl

  obtain ⟨DF, hDF⟩ := line_of_pts d f
  obtain ⟨DE, hDE⟩ := line_of_pts d e
  obtain ⟨EF, hEF⟩ := line_of_pts e f
  have f_nonline_DE := not_online_of_not_colinear hDE.1 hDE.2 tri_def
  have e_nonline_DF: ¬online e DF := not_online_of_not_colinear hDF.1 hDF.2 (by perma)

  refine' this tri_def tri_abc ang_a_eq_d.symm ang_b_eq_e.symm leq.symm a_ne_c d_ne_f a_ne_b d_ne_e e_ne_f b_ne_c DF hDF DE hDE EF hEF f_nonline_DE e_nonline_DF _ _
  exact Or.symm contra
  cases contra with
  | inl contra => exact contra
  | inr contra => exfalso; linarith

/-- Given two similar triangles, if the side of one triangle is smaller than that of the second,
then the remaining sides are also smaller -/
lemma length_lt_of_length_lt {a b c d e f : point}
    (tri_abc : ¬ colinear a b c) (tri_def : ¬ colinear d e f) 
    (ang_a_eq_d : angle b a c = angle e d f) (ang_b_eq_e : angle a b c = angle d e f)
    (lineq: length d f < length a c) :
    length d e < length a b := by
  have d_ne_f := neq_13_of_not_colinear tri_def
  have a_ne_c := neq_13_of_not_colinear tri_abc
  have a_ne_b := neq_12_of_not_colinear tri_abc
  have b_ne_c := neq_23_of_not_colinear tri_abc

  obtain ⟨AC, hAC⟩ := line_of_pts a c
  obtain ⟨AB, hAB⟩ := line_of_pts a b
  obtain ⟨BC, hBC⟩ := line_of_pts b c

  have b_nonline_AC : ¬online b AC := not_online_of_not_colinear hAC.1 hAC.2 (by perma)

  obtain ⟨g, hg⟩ := B_length_eq_of_ne_lt d_ne_f lineq
  have g_online_AC := online_2_of_B hg.1 hAC.1 hAC.2
  have g_nonline_BC : ¬ online g BC := by
    by_contra contra
    have := line_unique_of_pts (ne_23_of_B hg.1) contra hBC.2 g_online_AC hAC.2
    rw [this] at hBC
    exact b_nonline_AC hBC.1
  have g_nonline_AB : ¬ online g AB := by
    by_contra contra
    have := line_unique_of_pts (ne_12_of_B hg.1).symm contra hAB.1 g_online_AC hAC.1
    rw [this] at hAB
    exact b_nonline_AC hAB.2

  by_contra contra
  rw [not_lt, le_iff_lt_or_eq] at contra

  cases contra with

  | inl contra =>
    obtain ⟨h, hh⟩ := same_length_B_of_ne_ge a_ne_b contra
    obtain ⟨HG, hHG⟩ := line_of_pts h g

    have h_online_AB := online_3_of_B hh.1 hAB.1 hAB.2
    have h_ne_g : h ≠ g := by
      by_contra contra
      rw [contra] at hh
      have := online_2_of_B hh.1 hAC.1 (online_2_of_B hg.1 hAC.1 hAC.2)
      exact (not_online_of_not_colinear hAC.1 hAC.2 (by perma)) this

    have h_nonline_AC : ¬ online h AC := by
      by_contra contra
      have := line_unique_of_pts (ne_13_of_B hh.1).symm contra hAC.1 h_online_AB hAB.1
      rw [this] at b_nonline_AC
      exact b_nonline_AC hAB.2

    have hag_bac : angle h a g = angle b a c := by
      rw [angle_extension_of_B a_ne_c hh.1]
      have := angle_extension_of_B (ne_13_of_B hh.1) hg.1
      perm; rw [this]
    rw [← hag_bac] at ang_a_eq_d
    have' ang_b_eq_h := sas hg.2 hh.2 (by perma only [angle] at *)
    rw [ang_b_eq_e.symm] at ang_b_eq_h

    have' := parallel_of_similar hAB.1 h_online_AB hAB.2 hAC.1 hAC.2 hHG.1 hHG.2 hBC.1 hBC.2 (ne_23_of_B hh.1).symm (ne_13_of_B hh.1) h_ne_g b_ne_c a_ne_c h_nonline_AC ang_b_eq_h.2.2.symm hh.1 _

    have ss1 := sameside_of_para_online hHG.1 hHG.2 this
    have ss2 := sameside_of_B_not_online_2 (B_symm hg.1) hBC.2 g_nonline_BC
    have := sameside_trans (sameside_symm ss1) ss2
    exact (not_sameside13_of_B123_online2 hh.1 hBC.1) (sameside_symm this)

    exact sameside_symm (sameside_of_B_not_online_2 hg.1 hAB.1 g_nonline_AB)

  | inr contra =>
    have: length d f = length a c := length_eq_of_length_eq (by perma) (by perma) (by perma) (asa tri_abc contra (by perma) (by perma)).2.2 contra.symm
    linarith


/-- Two triangles are similar if they have two angles equal -/
theorem similar_of_AA {a b c d e f : point} (tri_abc : ¬ colinear a b c) (tri_def : ¬ colinear d e f) 
    (ang_a_eq_d : angle b a c = angle e d f) (ang_b_eq_e : angle a b c = angle d e f) : 
    proportion (length a b) (length d e) (length a c) (length d f) := by
  have d_ne_f := neq_13_of_not_colinear tri_def
  have a_ne_c := neq_13_of_not_colinear tri_abc
  have d_ne_e := neq_12_of_not_colinear tri_def
  have a_ne_b := neq_12_of_not_colinear tri_abc
  have b_ne_c := neq_23_of_not_colinear tri_abc
  have e_ne_f := neq_23_of_not_colinear tri_def

  by_cases dfde_ne_acab : length d f = length a c ∨ length d e = length a b
  . wlog df_ne_ac : length d f = length a c
    swap
    have := length_eq_of_length_eq tri_abc tri_def ang_a_eq_d ang_b_eq_e df_ne_ac
    rw [this, df_ne_ac.symm]
    exact proportion_eq (length_nonneg a b) (length_nonneg d f) (length_eq_zero_iff.not.mpr a_ne_b) (length_eq_zero_iff.not.mpr d_ne_f)

    rw [proportion_symm_iff]

    have leq : length d e = length a b := by
      cases dfde_ne_acab with
      | inl dfde_ne_acab => exfalso; exact df_ne_ac dfde_ne_acab
      | inr dfde_ne_acab => exact dfde_ne_acab

    refine' this (by perma) (by perma) (by perma) _ d_ne_e a_ne_b d_ne_f a_ne_c b_ne_c.symm e_ne_f.symm (Or.symm dfde_ne_acab) leq
    exact (asa tri_abc leq.symm ang_a_eq_d (by perma [ang_b_eq_e])).2.2

  conv at dfde_ne_acab => 
    rw [not_or]
    rw [(Ne.def _ _).symm]; rhs; rw [(Ne.def _ _).symm]

  wlog lineq : length d f < length a c
  refine' proportion_inv (this tri_def tri_abc ang_a_eq_d.symm ang_b_eq_e.symm a_ne_c d_ne_f a_ne_b d_ne_e e_ne_f b_ne_c ⟨dfde_ne_acab.1.symm,dfde_ne_acab.2.symm⟩ _)
  simp [not_lt] at lineq
  exact (Ne.symm dfde_ne_acab.1).lt_of_le lineq

  obtain ⟨AC, hAC⟩ := line_of_pts a c
  obtain ⟨AB, hAB⟩ := line_of_pts a b
  obtain ⟨BC, hBC⟩ := line_of_pts b c

  have lineq2 := length_lt_of_length_lt tri_abc tri_def ang_a_eq_d ang_b_eq_e lineq

  have b_nonline_AC : ¬ online b AC:= not_online_of_not_colinear hAC.1 hAC.2 (by perma)

  obtain ⟨g, hg⟩ := B_length_eq_of_ne_lt d_ne_f lineq
  obtain ⟨h, hh⟩ := B_length_eq_of_ne_lt d_ne_e lineq2
  obtain ⟨HG, hHG⟩ := line_of_pts h g

  have g_online_AC := online_2_of_B hg.1 hAC.1 hAC.2
  have h_online_AB := online_2_of_B hh.1 hAB.1 hAB.2

  rw [hg.2.symm, hh.2.symm]

  refine' (proportional_iff_para' hHG.1 hHG.2 hBC.1 hBC.2 hAB.1 h_online_AB _ hh.1 hg.1).mpr _

  by_contra contra
  rw [line_unique_of_pts (ne_12_of_B hg.1).symm g_online_AC hAC.1 contra hAB.1] at b_nonline_AC
  exact b_nonline_AC hAB.2

  have h_ne_g : h ≠ g := by
    by_contra contra
    rw [contra] at hh
    have := online_3_of_B hh.1 hAC.1 (online_2_of_B hg.1 hAC.1 hAC.2)
    exact (not_online_of_not_colinear hAC.1 hAC.2 (by perma)) this

  refine' para_symm (parallel_of_similar hAB.1 hAB.2 h_online_AB hAC.1 g_online_AC hBC.1 hBC.2 hHG.1 hHG.2 (ne_23_of_B hh.1).symm a_ne_b b_ne_c h_ne_g (ne_12_of_B hg.1) b_nonline_AC _ hh.1 _)

  have hag_bac : angle h a g = angle b a c := by
    linperm [angle_extension_of_B a_ne_c hh.1, angle_extension_of_B (ne_12_of_B hh.1) hg.1]
  linperm [(sas hg.2 hh.2 (by linperm)).2.2]

  refine' sameside_of_B_not_online_2 hg.1 hAB.1 _
  by_contra contra
  have := line_unique_of_pts (ne_12_of_B hg.1) hAB.1 contra hAC.1 g_online_AC
  rw [this] at hAB
  exact b_nonline_AC hAB.2
