import Mathlib.Data.Real.Basic

def proportion (r s t u : ℝ) : Prop := 
  0 ≤ r ∧ 0 ≤ s ∧ 0 ≤ t ∧ 0 ≤ u ∧ 
  ∀ (n m : ℕ), 
  ((n : ℝ) * r = m * s → (n : ℝ) * t = m * u) ∧
  ((n : ℝ) * r < m * s → (n : ℝ) * t < m * u) ∧ 
  ((m : ℝ) * s < n * r → (m : ℝ) * u < n * t)

lemma proportion_of_eq_ratio {r s t u : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) 
    (s_ne : s ≠ 0) (u_ne : u ≠ 0) (rstu : r / s = t / u) : 
    proportion r s t u := by 
  refine' ⟨hr, hs, ht, hu, _⟩
  intro n m; field_simp at rstu
  constructor
  · intro h; suffices hh : (n : ℝ) * t * s = m * u * s
    · convert (congr_arg (fun x => x / s) hh) using 1; all_goals field_simp
    · convert (congr_arg (fun x => x * u) h) using 1 
      · rw [mul_assoc, ← rstu]; ring
      · ring
  · constructor
    · intro h; suffices hh : (n : ℝ) * t * s < m * u * s
      · convert mul_lt_mul hh (by simp : (1:ℝ)/s ≤ 1/s) (by positivity)  (by positivity) using 1
        all_goals field_simp
      · rw [mul_assoc, ← rstu, ← mul_assoc]
        convert mul_lt_mul h (by simp : u ≤ u) (by positivity) (by positivity) using 1; ring
    · intros h; suffices hh : (m : ℝ) * u * s < n * t * s
      · convert mul_lt_mul hh (by simp : (1:ℝ)/s ≤ 1/s) (by positivity) (by positivity) using 1
        all_goals field_simp
      · rw [(by ring : (n : ℝ) * t * s = n * (t * s)), ← rstu]
        convert mul_lt_mul h (by simp : u ≤ u) (by positivity) (by positivity) using 1
        all_goals ring

lemma eq_ratio_of_proportion {r s t u : ℝ} (s_ne : s ≠ 0) (u_ne : u ≠ 0) (h : proportion r s t u) : 
    r / s = t / u := by
  obtain ⟨ hr, hs, ht, hu, h⟩ := h
  by_contra hh
  change r / s ≠ t / u at hh
  by_cases rstu : r / s < t / u
  · have : ∃ n m : ℕ, r / s < n / m ∧ (n:ℝ) / m < t / u ∧ n ≠ 0 ∧ m ≠ 0
    · obtain ⟨q, hq⟩ := exists_rat_btwn rstu
      have q_gt : (0:ℚ) < q := by
        exact_mod_cast
        calc (0:ℝ) ≤ r / s := by positivity
                 r / s < q := hq.1
      let m := q.den; have m_ne : m ≠ 0 := q.den_nz
      let nn := q.num; have nn_gt : 0 < nn := Rat.num_pos_iff_pos.mpr q_gt
      let n := nn.toNat
      have n_nn : (n:ℤ) = nn := Int.toNat_of_nonneg (le_of_lt nn_gt)
      use n, m
      have : (n : ℝ) / m = q := by
        have : (nn : ℝ) / m = q := by exact_mod_cast (q.num_den)
        convert this using 2
        exact_mod_cast Int.toNat_of_nonneg (le_of_lt nn_gt)
      rw [this]; exact ⟨hq.1, hq.2, by linarith, m_ne⟩
    obtain ⟨n, m, hrs_le_nm, hnm_le_tu, n_ne, m_ne⟩ := this
    have m_ne_ℝ : (m:ℝ) ≠ 0 := by exact_mod_cast m_ne
    have mrns : (m:ℝ)*r < n*s → (m:ℝ) * t < n * u := by exact_mod_cast (h m n).2.1
    have' := mrns _
    · suffices hh : (n:ℝ) * u < m * t
      · exact (lt_self_iff_false ((m : ℝ) * t)).mp (this.trans hh)         
      · convert mul_lt_mul hnm_le_tu (by simp : u * m ≤ u * m) (by positivity) (by positivity) using 1
        all_goals (field_simp; ring)
    convert mul_lt_mul hrs_le_nm (by simp : s * m ≤ s * m) (by positivity) (by positivity) using 1
    all_goals (field_simp; ring)
  · have turs : t / u < r / s := (or_iff_right rstu).mp (lt_or_lt_iff_ne.mpr hh)
    have : ∃ n m : ℕ, t / u < n / m ∧ (n:ℝ) / m < r / s ∧ n ≠ 0 ∧ m ≠ 0
    · obtain ⟨q, hq⟩ := exists_rat_btwn turs
      have q_gt : (0:ℚ) < q := by exact_mod_cast
        calc (0 : ℝ) ≤ t / u := by positivity
               t / u < q := hq.1
      let m := q.den; have m_ne : m ≠ 0 := q.den_nz
      let nn := q.num; have nn_gt : 0 < nn := Rat.num_pos_iff_pos.mpr q_gt
      let n := nn.toNat; have n_nn : (n:ℤ) = nn := Int.toNat_of_nonneg (le_of_lt nn_gt)
      use n, m
      have : (n : ℝ) / m = q := by
        have : (nn : ℝ) / m = q := by exact_mod_cast (q.num_den)
        convert this using 2
        exact_mod_cast Int.toNat_of_nonneg (le_of_lt nn_gt)
      rw [this]; exact ⟨hq.1, hq.2, by linarith, m_ne⟩
    obtain ⟨n, m, hrs_le_nm, hnm_le_tu, n_ne, m_ne⟩ := this
    have m_ne_ℝ : (m : ℝ) ≠ 0 := by exact_mod_cast m_ne
    have mrns : (n : ℝ) * s < m * r → (n : ℝ) * u < m * t := by exact_mod_cast (h m n).2.2
    have : (n : ℝ) * s < m * r := by
      convert mul_lt_mul hnm_le_tu (by simp : s * m ≤ s * m) (by positivity) (by positivity) using 1
      all_goals (field_simp; ring)
    have := mrns this
    have : t * m < n * u := by
      convert mul_lt_mul hrs_le_nm (by simp : u * m ≤ u * m) (by positivity) (by positivity) using 1;
      all_goals (field_simp; ring)
    linarith

lemma proportion_iff {r s t u : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (s_ne : s ≠ 0) (u_ne : u ≠ 0) :
    r / s = t / u ↔ proportion r s t u := 
  ⟨fun h => proportion_of_eq_ratio hr hs ht hu s_ne u_ne h, 
    fun h => eq_ratio_of_proportion s_ne u_ne h⟩ 


lemma proportion_inv {r s t u : ℝ} (h : proportion r s t u) :
    proportion s r u t := by
  dsimp [proportion] at *
  refine ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, ?_⟩
  intro n m
  have := h.2.2.2.2 m n
  exact ⟨fun h => (this.1 h.symm).symm, ⟨fun h => (this.2.2 h), fun h => (this.2.1 h)⟩⟩ 


lemma proportion_inv_iff {r s t u : ℝ} : proportion r s t u ↔ proportion s r u t := by
  constructor; all_goals exact fun h => proportion_inv h


lemma zero_of_proportion_iff { r s t u : ℝ } (h : proportion r s t u) :
    s = 0 ↔ u = 0 := by
  constructor
  · intro s_ne
    have := (h.2.2.2.2 0 1).1; simp at this
    exact (this s_ne.symm).symm
  · intro u_ne
    have hh := (h.2.2.2.2 0 1).2.1; simp at hh
    by_contra s_ne
    have : 0 < s := Ne.lt_of_le (fun ss => s_ne ss.symm) h.2.1
    have := hh this
    linarith

lemma proportion_of_zero : proportion 0 0 0 0 := by simp [proportion]

lemma proportion_symm {r s t u : ℝ} (s_ne : s ≠ 0) (u_ne : u ≠ 0) (h : proportion r s t u) :
    proportion t u r s := 
  (proportion_iff h.2.2.1 h.2.2.2.1 h.1 h.2.1 u_ne s_ne).mp 
    (((proportion_iff h.1 h.2.1 h.2.2.1 h.2.2.2.1 s_ne u_ne).mpr) h).symm

lemma proportion_symm' {r s t u : ℝ} (h : proportion r s t u) :
    proportion t u r s := by
  by_cases s_ne : s = 0
  · have u_ne := (zero_of_proportion_iff h).mp s_ne
      -- invert the proportionality relation
    have inv := proportion_inv h
    by_cases r_ne : r = 0
    · have t_ne := (zero_of_proportion_iff inv).mp r_ne
      rw [s_ne, r_ne, t_ne, u_ne]; exact proportion_of_zero
    · have t_ne := (zero_of_proportion_iff inv).not.mp r_ne
      rw [proportion_inv_iff]; exact proportion_symm r_ne t_ne inv
  · have u_ne := (zero_of_proportion_iff h).not.mp s_ne
    exact proportion_symm s_ne u_ne h
  
lemma proportion_symm_iff {r s t u : ℝ} : proportion r s t u ↔ proportion t u r s := 
⟨fun h => proportion_symm' h, fun h => proportion_symm' h⟩

lemma proportion_eq {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (r_ne : r ≠ 0) (s_ne : s ≠ 0) : proportion r r s s := by
  rw [(proportion_iff hr hr hs hs r_ne s_ne).symm]; field_simp
