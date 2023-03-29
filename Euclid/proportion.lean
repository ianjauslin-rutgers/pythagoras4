import Mathlib.Data.Real.NNReal

--open_locale nnreal 

def proportion (r s t u : ℝ) : Prop := 
  0 ≤ r ∧ 0 ≤ s ∧ 0 ≤ t ∧ 0 ≤ u ∧ 
  ∀ (n m : ℕ), 
  ((n : ℝ) * r = m * s → (n : ℝ) * t = m * u) ∧
  ((n : ℝ) * r < m * s → (n : ℝ) * t < m * u) ∧ 
  ((m : ℝ) * s < n * r → (m : ℝ) * u < n * t)

lemma proportion_of_eq_ratio {r s t u : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) (s_ne : s ≠ 0) (u_ne : u ≠ 0) 
  (rstu : r / s = t / u) : 
  proportion r s t u :=
 by sorry
 --
/-begin
  refine ⟨hr, hs, ht, hu, _⟩,
  intros n m,
  field_simp at rstu,
  split,
  { intros h,
    suffices hh : (n : ℝ) * t * s = m * u * s,
    { convert (congr_arg (λ x, x / s) hh) using 1; field_simp, },
    { convert (congr_arg (λ x, x * u) h) using 1,
      { rw [mul_assoc, ← rstu],
        ring, },
      { ring, }, }, },
  { split,
    { intros h,
      suffices hh : (n : ℝ) * t * s < m * u * s,
      { convert mul_lt_mul hh (by simp : (1:ℝ)/s ≤ 1/s) (by positivity) (by positivity) using 1;
        field_simp, },
      { rw [mul_assoc, ← rstu, ← mul_assoc],
        convert mul_lt_mul h (by simp : u ≤ u) (by positivity) (by positivity) using 1;
        ring, }, },
    { intros h,
      suffices hh : (m : ℝ) * u * s < n * t * s,
      { convert mul_lt_mul hh (by simp : (1:ℝ)/s ≤ 1/s) (by positivity) (by positivity) using 1;
        field_simp, },
      { rw [(by ring : (n : ℝ) * t * s = n * (t * s)), ← rstu],
        convert mul_lt_mul h (by simp : u ≤ u) (by positivity) (by positivity) using 1; 
        ring, }, }, },  end-/

lemma eq_ratio_of_proportion {r s t u : ℝ} (s_ne : s ≠ 0) (u_ne : u ≠ 0) 
  (h : proportion r s t u) : 
  r / s = t / u :=
 by sorry
 --
/-begin
  have hr := h.1,
  have hs := h.2.1,
  have ht := h.2.2.1,
  have hu := h.2.2.2.1,
  have h := h.2.2.2.2,
  by_contra hh,
  change r / s ≠ t / u at hh,
  by_cases rstu : r / s < t / u,
  { have : ∃ n m : ℕ, r / s < n / m ∧ (n:ℝ) / m < t / u ∧ n ≠ 0 ∧ m ≠ 0,
    { obtain ⟨q, hq⟩ := exists_rat_btwn rstu,
      let m := q.denom,
      have m_ne : m ≠ 0 := rat.denom_ne_zero q,
      have m_ne_ℝ : (m:ℝ) ≠ 0 := by exact_mod_cast m_ne, 
      have q_gt : (0:ℚ) < q := by exact_mod_cast
        calc (0:ℝ) ≤ r/s : by positivity
        ... < q : hq.1, 
      let nn := q.num,
      have nn_gt : 0 < nn := rat.num_pos_iff_pos.mpr q_gt,
      let n := nn.to_nat,
      have n_nn : (n:ℤ) = nn := int.to_nat_of_nonneg (le_of_lt nn_gt),
      use n, -- use n m doesn't work???
      use m,
      have : (n : ℝ) / m = q,
      { have : (nn : ℝ) / m = q := by exact_mod_cast (rat.num_div_denom q),
        convert this using 2,
        exact_mod_cast int.to_nat_of_nonneg (le_of_lt nn_gt), },
      rw this,
      exact ⟨hq.1, hq.2, by linarith, m_ne⟩, },
    obtain ⟨n, m, hrs_le_nm, hnm_le_tu, n_ne, m_ne⟩ := this, 
    have m_ne_ℝ : (m:ℝ) ≠ 0 := by exact_mod_cast m_ne, 
    have mrns : (m:ℝ)*r < n*s → (m:ℝ) * t < n * u := by exact_mod_cast (h m n).2.1,
    have := mrns _,
    { suffices hh : (n:ℝ) * u < m * t,
      { linarith, },
      convert mul_lt_mul hnm_le_tu (by simp : u * m ≤ u * m) (by positivity) (by positivity) using 1,
      { field_simp,
        ring, },
      { field_simp,
        ring, }, },
    convert mul_lt_mul hrs_le_nm (by simp : s * m ≤ s * m) (by positivity) (by positivity) using 1,
    { field_simp,
      ring, },
    { field_simp,
      ring, }, },
  { have turs : t / u < r / s := (or_iff_right rstu).mp (lt_or_lt_iff_ne.mpr hh),
    have : ∃ n m : ℕ, t / u < n / m ∧ (n:ℝ) / m < r / s ∧ n ≠ 0 ∧ m ≠ 0,
    { obtain ⟨q, hq⟩ := exists_rat_btwn turs,
      let m := q.denom,
      have m_ne : m ≠ 0 := rat.denom_ne_zero q,
      have m_ne_ℝ : (m:ℝ) ≠ 0 := by exact_mod_cast m_ne, 
      have q_gt : (0:ℚ) < q := by exact_mod_cast
        calc (0:ℝ) ≤ t/u : by positivity
        ... < q : hq.1, 
      let nn := q.num,
      have nn_gt : 0 < nn := rat.num_pos_iff_pos.mpr q_gt,
      let n := nn.to_nat,
      have n_nn : (n:ℤ) = nn := int.to_nat_of_nonneg (le_of_lt nn_gt),
      use n, -- use n m doesn't work???
      use m,
      have : (n : ℝ) / m = q,
      { have : (nn : ℝ) / m = q := by exact_mod_cast (rat.num_div_denom q),
        convert this using 2,
        exact_mod_cast int.to_nat_of_nonneg (le_of_lt nn_gt), },
      rw this,
      exact ⟨hq.1, hq.2, by linarith, m_ne⟩, },
    obtain ⟨n, m, hrs_le_nm, hnm_le_tu, n_ne, m_ne⟩ := this, 
    have m_ne_ℝ : (m:ℝ) ≠ 0 := by exact_mod_cast m_ne, 
    have n_ne_ℝ : (n:ℝ) ≠ 0 := by exact_mod_cast n_ne, 
    have mrns : (n:ℝ) * s < m * r → (n:ℝ) * u < m * t := by exact_mod_cast (h m n).2.2,
    have : (n:ℝ) * s < m * r,
    { convert mul_lt_mul hnm_le_tu (by simp : s * m ≤ s * m) (by positivity) (by positivity) using 1;
      { field_simp,
        ring, }, },
    have := mrns this,
    have : t * m < n * u,
    { convert mul_lt_mul hrs_le_nm (by simp : u * m ≤ u * m) (by positivity) (by positivity) using 1;
      { field_simp,
        ring, }, },
    linarith, },  end-/

lemma proportion_iff {r s t u : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) (s_ne : s ≠ 0) (u_ne : u ≠ 0) :
  r / s = t / u ↔ proportion r s t u := 
 by sorry
 -- ⟨λ h, proportion_of_eq_ratio hr hs ht hu s_ne u_ne h, λ h, eq_ratio_of_proportion s_ne u_ne h⟩ 


lemma proportion_inv {r s t u : ℝ} (h : proportion r s t u) :
  proportion s r u t :=
   by sorry
 --
/-begin
    dsimp [proportion] at ⊢ h,
    refine ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, _⟩,
    intros n m,
    have := h.2.2.2.2 m n,
    split,
    intro h,
    exact (this.1 h.symm).symm,
    split,
    intro h,
    exact (this.2.2 h),
    intro h,
    exact (this.2.1 h),
   end-/

lemma proportion_inv_iff {r s t u : ℝ} :
  proportion r s t u ↔ proportion s r u t :=
   by sorry
 --
/-begin
    split,
    all_goals
    { intro h,
      exact proportion_inv h, },
   end-/


lemma zero_of_proportion_iff { r s t u : ℝ } (h : proportion r s t u) :
  s = 0 ↔ u = 0 :=
   by sorry
 --
/-begin
    dsimp [proportion] at h,
    split,
    { intro s_ne,
      have := (h.2.2.2.2 0 1).1,
      rw s_ne at this,
      simp only [algebra_map.coe_zero, zero_mul, algebra_map.coe_one, eq_self_iff_true, one_mul, forall_true_left] at this,
      exact this.symm, },
    { intro u_ne,
      have := (h.2.2.2.2 0 1).2.1,
      rw u_ne at this,
      simp only [algebra_map.coe_zero, zero_mul, algebra_map.coe_one, one_mul, lt_self_iff_false] at this,
      by_contradiction contra,
      rw (ne.def s 0).symm at contra,
      exact this (lt_of_le_of_ne h.2.1 contra.symm), },
   end-/

lemma proportion_of_zero : proportion 0 0 0 0 :=
   by sorry
 --
/-begin
    dsimp [proportion],
    simp only [le_refl, mul_zero, eq_self_iff_true, lt_self_iff_false, is_empty.forall_iff, and_self, forall_const],
   end-/


lemma proportion_symm {r s t u : ℝ} (s_ne : s ≠ 0) (u_ne : u ≠ 0) (h : proportion r s t u) :
  proportion t u r s 
 :=  by sorry
 -- (proportion_iff h.2.2.1 h.2.2.2.1 h.1 h.2.1 u_ne s_ne).mp(((proportion_iff h.1 h.2.1 h.2.2.1 h.2.2.2.1 s_ne u_ne).mpr) h).symm

lemma proportion_symm' {r s t u : ℝ} (h : proportion r s t u) :
  proportion t u r s :=
   by sorry
 --
/-begin
    by_cases s_ne : s = 0,
    { have u_ne := (zero_of_proportion_iff h).mp s_ne,
      -- invert the proportionality relation
      have inv := proportion_inv h,
      by_cases r_ne : r = 0,
      { have t_ne := (zero_of_proportion_iff inv).mp r_ne,
        rw [s_ne,r_ne,t_ne,u_ne],
        exact proportion_of_zero,
      },

      have t_ne := (zero_of_proportion_iff inv).not.mp r_ne,
      rw proportion_inv_iff,
      exact proportion_symm r_ne t_ne inv,
    },

    have u_ne := (zero_of_proportion_iff h).not.mp s_ne,
    exact proportion_symm s_ne u_ne h,
   end-/

lemma proportion_symm_iff {r s t u : ℝ}
  : proportion r s t u ↔ proportion t u r s :=
   by sorry
 --
/-begin
    split,
    all_goals
    { intro h,
      exact proportion_symm' h, },
   end-/

lemma proportion_eq {r s : ℝ} (hr: 0 ≤ r) (hs: 0 ≤ s) (r_ne: r ≠ 0) (s_ne: s ≠ 0) : proportion r r s s :=
   by sorry
 --
/-begin
    rw (proportion_iff hr hr hs hs r_ne s_ne).symm,
    field_simp,
   end-/

