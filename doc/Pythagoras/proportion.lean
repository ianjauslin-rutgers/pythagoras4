def proportion (r s t u : ℝ) : Prop := 
  0 ≤ r ∧ 0 ≤ s ∧ 0 ≤ t ∧ 0 ≤ u ∧ 
  ∀ (n m : ℕ), 
  ((n : ℝ) * r = m * s → (n : ℝ) * t = m * u) ∧
  ((n : ℝ) * r < m * s → (n : ℝ) * t < m * u) ∧ 
  ((m : ℝ) * s < n * r → (m : ℝ) * u < n * t)

lemma proportion_of_eq_ratio {r s t u : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) 
    (s_ne : s ≠ 0) (u_ne : u ≠ 0) (rstu : r / s = t / u) : 
    proportion r s t u 

lemma eq_ratio_of_proportion {r s t u : ℝ} (s_ne : s ≠ 0) (u_ne : u ≠ 0) (h : proportion r s t u) : 
    r / s = t / u 

lemma proportion_iff {r s t u : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) 
    (s_ne : s ≠ 0) (u_ne : u ≠ 0) :
    r / s = t / u ↔ proportion r s t u 

lemma proportion_inv {r s t u : ℝ} (h : proportion r s t u) :
    proportion s r u t 

lemma proportion_inv_iff {r s t u : ℝ} : proportion r s t u ↔ proportion s r u t 

lemma zero_of_proportion_iff { r s t u : ℝ } (h : proportion r s t u) :
    s = 0 ↔ u = 0 

lemma proportion_of_zero : proportion 0 0 0 0 

lemma proportion_symm {r s t u : ℝ} (s_ne : s ≠ 0) (u_ne : u ≠ 0) (h : proportion r s t u) :
    proportion t u r s 

lemma proportion_symm' {r s t u : ℝ} (h : proportion r s t u) :
    proportion t u r s 

lemma proportion_symm_iff {r s t u : ℝ} : proportion r s t u ↔ proportion t u r s 


