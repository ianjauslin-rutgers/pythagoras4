import SyntheticEuclid4
import Pythagoras.euclid_I_extras
import Mathlib.Tactic.WLOG

open incidence_geometry
variable [i: incidence_geometry]

/-- technical lemma that really shouldn't be here, but hey... -/
lemma mul_mul_lt (a b c : ℝ) (hc: 0 < c):
    a < b → a * c < b * c := (mul_lt_mul_right hc).mpr
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
    (aL: online a L)
    (bL: online b L) :
    ∃ (c : point), (online c L) ∧ (length a c = n * length a b) ∧ (n ≥ 2 ∧ a ≠ b → B a b c) := by

  -- trivial case
  by_cases ab: a = b
  · use a; rw [← ab, length_eq_zero_iff.mpr rfl]; simp; exact aL

  induction n with
  | zero => use a; rw [length_eq_zero_iff.mpr rfl]; simp; exact aL
  | succ n hn =>
    -- trivial case: n = 0
    by_cases n0: n = 0
    · exact ⟨ b, bL, (by rw [n0]; simp) ⟩

    -- separate case n = 1
    by_cases n1 : n = 1
    · obtain ⟨ e, He ⟩ := length_eq_B_of_ne_four ab ab; use e
      simp_rw [(length_sum_of_B He.1).symm, He.2, n1]; simp; ring_nf
      refine' ⟨ online_3_of_B He.1 aL bL, (by tauto), fun _ => He.1 ⟩

    -- extract point from hn
    obtain ⟨ d, Hd ⟩ := hn
    have ad : a ≠ d := by
      apply nq_of_len_pos
      rw [Hd.2.1]; simp [Nat.pos_of_ne_zero n0, zero_lt_mul_left, Nat.cast_pos]
      exact len_pos_of_nq ab

    obtain ⟨ e, He ⟩ := length_eq_B_of_ne_four ad ab
    use e; rw [← length_sum_of_B He.1, Hd.2.1, He.2]; simp; ring_nf
    have := Hd.2.2 ⟨ ge2_of_n1_n0 n0 n1, ab ⟩
    refine' ⟨ online_3_of_B He.1 aL Hd.1, (by tauto), fun _ _ => B124_of_B134_B123 He.1 this⟩

/-- rescale base of triangle -/
-- workhorse: version for use in inductive case
lemma rescale_triangle_of_base_inductive (a : point) {b c : point} {L : line} {n : ℕ}
    (bL: online b L)
    (cL: online c L)
    (aL: ¬ online a L) :
    ∀ d : point, (online d L) → (length b d = n * length b c) → B b c d → area a b d = n * area a b c := by
  induction n with
  | zero =>
    simp; intros d _ hlen _
    rw [length_eq_zero_iff.mp hlen, area_of_eq a d d (by tauto)]

  | succ n hn =>
    intros d dL hlen Bbcd
    have bc := ne_12_of_B Bbcd
    have bd := ne_13_of_B Bbcd
    have cd := ne_23_of_B Bbcd

    -- trivial case: n=0
    by_cases n0 : n = 0
    · rw [← length_sum_of_B Bbcd, n0] at hlen; simp at hlen
      exfalso; exact cd (length_eq_zero_iff.mp hlen)

    -- special case: n=1
    by_cases n1 : n = 1
    · rw [← length_sum_of_B Bbcd, n1,] at hlen; simp at hlen
      rw [← (area_add_iff_B bc cd bd.symm bL cL dL aL).mp Bbcd, n1]
      perm; simp; ring_nf; simp [mul_two]
      apply (eq_area_of_eq_base_samevertex a bL cL cL dL (by linarith)).symm

    -- split off n+1'st bit
    simp [Nat.cast_succ]; rw [add_mul]; simp [one_mul]

    -- construct n-triangle
    obtain ⟨ e, He ⟩ := rescale_length n bL cL
    have Bbce := He.2.2 ⟨ ge2_of_n1_n0 n0 n1, bc ⟩
    rw [← hn e He.1 He.2.1 Bbce]
    have be := ne_13_of_B Bbce
    have ed : e ≠ d := fun ed => by
      have := He.2.1; rw [ed, hlen] at this; simp at this
      exact bc (length_eq_zero_iff.mp this)

    -- split abd
    have Bbed : B b e d := by
      have: length b e < length b d := by rw [He.2.1, hlen]; simp; linarith [len_pos_of_nq bc]
      have := B_of_three_online_ne_short this be bd ed bL He.1 dL
      
      cases this with
      | inl h => exact h
      | inr h =>
        exfalso
        apply not_B324_of_B123_B124 Bbce Bbcd
        exact B124_of_B134_B123 h (B_symm Bbce)
    
    rw [((area_add_iff_B be ed bd.symm bL He.1 dL aL).mp Bbed).symm]

    have: length b c = length e d := by
      have := length_sum_of_B Bbed
      rw [hlen, He.2.1] at this; simp [one_mul] at this; linarith
    perm [eq_area_of_eq_base_samevertex a bL cL He.1 dL this]; rw [this]

-- lemma with B b c d as a hypothesis
lemma rescale_triangle_of_base_B (a : point) {b c d : point} {L : line} {n : ℕ}
    (bL: online b L)
    (cL: online c L)
    (dL: online d L)
    (hlen: length b d = n * length b c)
    (Bbcd: B b c d)
    (aL: ¬ online a L) :
    area a b d = n * area a b c := by
  exact rescale_triangle_of_base_inductive a bL cL aL d dL hlen Bbcd

-- not B c b d
lemma rescale_triangle_of_base_notcbd (a : point) {b c d : point} {L : line} {n : ℕ}
    (bL: online b L)
    (cL: online c L)
    (dL: online d L)
    (hlen: length b d = n * length b c)
    (hB: ¬ B c b d)
    (bc: b ≠ c)
    (n0: n ≠ 0)
    (bd: b ≠ d)
    (aL: ¬ online a L) :
    area a b d = n * area a b c := by

  -- trivial case: n = 1
  by_cases n1 : n =1
  · rw [n1] at hlen; rw [n1]; simp [Nat.cast_one] at hlen; simp [Nat.cast_one]
    exact (eq_area_of_eq_base_samevertex a bL cL bL dL hlen.symm).symm

  have cd: c ≠ d := fun cd => by
    have n0 := length_eq_zero_iff.not.mpr bd
    rw [cd] at hlen; field_simp at hlen
    exact n1 hlen

  have: length b c < length b d := by
    have := len_pos_of_nq bc
    have n_ge1 := gt1_of_n1_n0 n0 n1
    simp [*]

  have hBs := B_of_three_online_ne_short this bc bd cd bL cL dL
  cases hBs with
  | inl hBs => exact rescale_triangle_of_base_B a bL cL dL hlen hBs aL
  | inr hBs => exfalso; exact hB hBs

-- full version
lemma rescale_triangle_of_base (a : point) {b c d : point} {L : line} {n : ℕ}
    (bL: online b L)
    (cL: online c L)
    (dL: online d L)
    (hlen: length b d = n * length b c) :
    area a b d = n * area a b c := by

  -- trivial case: b = c
  by_cases bc : b = c
  · rw [length_eq_zero_iff.mpr bc, mul_zero] at hlen
    have := length_eq_zero_iff.mp hlen
    rw [area_of_eq a b d (by tauto), area_of_eq a b c (by tauto)]; simp [mul_zero]

  -- trivial case: n = 0
  by_cases n0 : n = 0
  · rw [n0] at hlen; simp [Nat.cast_zero] at hlen
    have := length_eq_zero_iff.mp hlen
    rw [n0, area_of_eq a b d (by tauto)]; simp [Nat.cast_zero]

  have bd: b ≠ d := fun bd => by
    rw [length_eq_zero_iff.mpr bd, zero_eq_mul, Nat.cast_eq_zero] at hlen
    cases hlen with
    | inl hlen => exact n0 hlen
    | inr hlen => exact bc (length_eq_zero_iff.mp hlen)

  -- trivial case: online a L
  by_cases aL : online a L
  · perm [(area_zero_iff_online bc bL cL).mpr aL]; rw [this]
    perm [(area_zero_iff_online bd bL dL).mpr aL]; rw [this]
    simp [mul_zero]

  by_cases h_B_cbd : B c b d
    -- reflect c about b
  · obtain ⟨ e, He ⟩ := rescale_length 2 cL bL
    have Bcbe := He.2.2 ⟨ by simp [ge_iff_le], fun cb => bc cb.symm⟩
    have lbe : length b e = length b c := by
      perm [length_sum_of_B Bcbe]
      rw [He.2.1] at this; norm_cast at this; linperm
    rw [← lbe] at hlen

    have := not_B324_of_B123_B124 Bcbe h_B_cbd

    rw [rescale_triangle_of_base_notcbd a bL He.1 dL hlen this (ne_23_of_B Bcbe) n0 bd aL]
    rw [eq_area_of_eq_base_samevertex a bL He.1 bL cL lbe]

  exact rescale_triangle_of_base_notcbd a bL cL dL hlen h_B_cbd bc n0 bd aL

/-- triangles between parallels with smaller base have smaller area -/
-- case where they share a side and have the right betweeneness
lemma lt_area_of_lt_base_sameedge_Bbfc (a : point) {b c f: point} {L: line}
    (bL: online b L)
    (cL: online c L)
    (fL: online f L)
    (hB: B b f c)
    (bc: b ≠ c)
    (bf: b ≠ f)
    (cf: c ≠ f)
    (aL: ¬ online a L) :
    (length b c) > (length b f) → (area a b c) > (area a b f) := by
  have := (area_add_iff_B bf cf.symm bc.symm bL fL cL aL).mp hB
  intro; rw [← this]; simp [gt_iff_lt, lt_add_iff_pos_right]
  have : area a c f ≠ 0 :=
    fun _ => aL ((area_zero_iff_online cf cL fL).mp (by perma only [area] at *))
  exact (Ne.symm this).lt_of_le (area_nonneg a c f)

-- case where they share a side and not B f b c
lemma lt_area_of_lt_base_sameedge_nBfbc (a : point) {b c f: point} {L: line}
    (bL: online b L)
    (cL: online c L)
    (fL: online f L)
    (bc: b ≠ c)
    (bf: b ≠ f)
    (aL: ¬ online a L)
    (hB: ¬ B f b c) :
    (length b c) > (length b f) → (area a b c) > (area a b f) := by
  intro hlen; simp [gt_iff_lt] at hlen
  have cf: c ≠ f := fun cf => by rw [cf, lt_self_iff_false] at hlen; exact hlen
  have := B_of_three_online_ne_short hlen bf bc cf.symm bL fL cL

  cases this with
  | inl h => exact lt_area_of_lt_base_sameedge_Bbfc a bL cL fL h bc bf cf aL hlen
  | inr h => exfalso; exact hB h

-- case where they share a side
lemma lt_area_of_lt_base_sameedge (a : point) {b c f: point} {L: line}
    (bL: online b L)
    (cL: online c L)
    (fL: online f L)
    (bc: b ≠ c)
    (bf: b ≠ f)
    (aL: ¬ online a L) :
    (length b c) > (length b f) → (area a b c) > (area a b f) := by
  intro hlen

  by_cases Bfbc: B f b c
    -- reflect f about b
  · obtain ⟨ e, He ⟩ := rescale_length 2 fL bL
    have Bfbe := He.2.2 ⟨ by simp [ge_iff_le], bf.symm ⟩
    have lbe : length b e = length b f := by
      perm [length_sum_of_B Bfbe]; perm at He; norm_cast at this He; linarith
    rw [← lbe] at hlen
    rw [← eq_area_of_eq_base_samevertex a bL He.1 bL fL lbe]
    exact lt_area_of_lt_base_sameedge_nBfbc a bL cL He.1 bc (ne_23_of_B Bfbe) aL (not_B324_of_B123_B124 Bfbe Bfbc) hlen
  
  exact lt_area_of_lt_base_sameedge_nBfbc a bL cL fL bc bf aL Bfbc hlen

-- general case
lemma lt_area_of_lt_base {a b c d e f: point} {L M: line}
    (aM: online a M)
    (bL: online b L)
    (cL: online c L)
    (dM: online d M)
    (eL: online e L)
    (fL: online f L)
    (pLM: para L M) :
    (length b c) > (length e f) → (area a b c) > (area d e f) := by
  intro hlen

  have bc : b ≠ c := fun bc => by
    rw [length_eq_zero_iff.mpr bc] at hlen
    exact (not_le_of_gt hlen) (length_nonneg e f)

  have aL := offline_of_para aM (para_symm pLM)
  have dL := offline_of_para dM (para_symm pLM)

  -- trivial case: e = f
  by_cases ef: e = f
  · perm [(area_zero_iff_online bc bL cL).not.mpr aL]
    rw [area_of_eq d e f (by tauto)]
    exact (Ne.symm this).lt_of_le (area_nonneg a b c)

  -- construct parallelogram from d e f
  obtain ⟨ O, dO, eO ⟩ := line_of_pts d e
  have := not_online_of_triangle dO eO eL fL dL ef
  obtain ⟨ g, N, gM, gN, fN, pON ⟩ := parallel_projection fL pLM (not_para_of_online_online eO eL) this
  have efgd : paragram e f g d L N M O := by splitAll <;> perma only [para] at *
  perm [(len_ang_area_eq_of_parallelogram efgd).1]
  have dg : d ≠ g := ne_of_ne_len ef this

  -- construct parallelogram from b d g
  obtain ⟨ P, bP, dP ⟩ := line_of_pts b d
  have := not_online_of_triangle bP dP dM gM (offline_of_para bL pLM) dg
  obtain ⟨ h, R, hL, hR, gR, pPR ⟩ := parallel_projection gM (para_symm pLM) (not_para_of_online_online dP dM) this
  have bhgd : paragram b h g d L R M P := by splitAll <;> perma only [para]
  have ef_bh : length e f = length b h := by
    linperm [(len_ang_area_eq_of_parallelogram bhgd).1]

  have bh : b ≠ h := ne_of_ne_len ef ef_bh

  rw [eq_area_of_eq_base dM eL fL aM bL hL pLM ef_bh]
  have : length b c > length b h := by rw [← ef_bh]; exact hlen
  exact lt_area_of_lt_base_sameedge a bL cL hL bc bh aL this
  

/-- ## Euclid VI.1
two triangles in between parallel lines have their area in proportion with the length of their base
 https://mathcs.clarku.edu/~djoyce/java/elements/bookVI/propVI1.html -/
theorem proportion_area_of_proportion_base {a b c d e f: point} {L M : line}
    (aM: online a M)
    (bL: online b L)
    (cL: online c L)
    (dM: online d M)
    (eL: online e L)
    (fL: online f L)
    (pLM: para L M) :
    proportion (length b c) (length e f) (area a b c) (area d e f) := by

  refine' ⟨ length_nonneg b c, length_nonneg e f, area_nonneg a b c, area_nonneg d e f, _ ⟩
  intros n m

  obtain ⟨ h, Hh ⟩ := rescale_length n bL cL
  obtain ⟨ l, Hl ⟩ := rescale_length m eL fL

  rw [(rescale_triangle_of_base a bL cL Hh.1 Hh.2.1).symm, Hh.2.1.symm]
  rw [(rescale_triangle_of_base d eL fL Hl.1 Hl.2.1).symm, Hl.2.1.symm]

  exact ⟨ eq_area_of_eq_base aM bL Hh.1 dM eL Hl.1 pLM,
          lt_area_of_lt_base dM eL Hl.1 aM bL Hh.1 pLM,
          lt_area_of_lt_base aM bL Hh.1 dM eL Hl.1 pLM ⟩
  

/-- version where the vertex is the same for both triangles -/
theorem proportion_area_of_proportion_base_samevertex (a : point) {b c e f: point} {L : line}
    (bL: online b L)
    (cL: online c L)
    (eL: online e L)
    (fL: online f L)
    (aL: ¬ online a L) :
    proportion (length b c) (length e f) (area a b c) (area a e f) := by
  obtain ⟨ M, aM, pLM ⟩ := parallel_of_line_pt aL
  exact proportion_area_of_proportion_base aM bL cL aM eL fL pLM


/-- ## Euclid VI.2
a line cuts the sides of the triangle proportionally iff it is parallel to one of the sides of a triangle (version BD:AD = CE:AE)
 https://mathcs.clarku.edu/~djoyce/java/elements/bookVI/propVI2.html -/
theorem proportional_iff_para {a b c d e: point} {L M N: line}
    (dL: online d L) (eL: online e L)
    (bM: online b M) (cM: online c M)
    (aN: online a N) (dN: online d N)
    (eN: ¬ online e N)
    (Badb : B a d b) (Baec : B a e c) :
    proportion (length b d) (length a d) (length c e) (length a e) ↔ para L M := by
  have bN := online_3_of_B Badb aN dN
  obtain ⟨O, aO, eO⟩ := line_of_pts a e
  have cO := online_3_of_B Baec aO eO
  obtain ⟨P, cP, dP⟩ := line_of_pts c d

  -- non-degeneracy
  have ab : a ≠ b := ne_13_of_B Badb
  have ae : a ≠ e := ne_12_of_B Baec
  have ad : a ≠ d := ne_12_of_B Badb
  have bd : b ≠ d := ne_12_of_B (B_symm Badb)
  have ce : c ≠ e := ne_12_of_B (B_symm Baec)
  have NO : N ≠ O := fun NO => eN (by rwa [← NO] at eO)
  have PO : P ≠ O := fun PO => NO (line_unique_of_pts ad aO (by rwa [PO] at dP) aN dN).symm
  have dO := fun dO => NO (line_unique_of_pts ad aN dN aO dO)
  have eP := fun eP => PO (line_unique_of_pts ce cP eP cO eO)
  have aL := fun aL => eN (by rwa [line_unique_of_pts ad aL dL aN dN] at eL)
  have bL := fun bL => eN (by rwa [line_unique_of_pts bd bL dL bN dN] at eL)
  have cL := fun cL => (by rwa [← line_unique_of_pts ce cO eO cL eL] at aL : ¬ online a O) aO
  have bc : b ≠ c := fun bc => NO (line_unique_of_pts ab aN bN aO (by rwa [← bc] at cO))
  have cd : c ≠ d := fun cd => by rw [← cd] at dO; exact dO cO

  have bd_ad : proportion (length b d) (length a d) (area e b d) (area e a d) :=  proportion_area_of_proportion_base_samevertex e bN dN aN dN eN
  have ce_ae : proportion (length c e) (length a e) (area d c e) (area d a e) := proportion_area_of_proportion_base_samevertex d cO eO aO eO dO
  have Lad : length a d ≠ 0 := length_eq_zero_iff.not.mpr ad
  have Lae : length a e ≠ 0 := length_eq_zero_iff.not.mpr ae
  have ade : area a d e ≠ 0 := (area_zero_iff_online ad aN dN).not.mpr eN
  
  have ratio_iff : length b d / length a d = length c e / length a e ↔ area e b d / area e a d = area d c e / area d a e := by
    perm at *
    rw [eq_ratio_of_proportion Lad ade bd_ad, eq_ratio_of_proportion Lae ade ce_ae]

  have prop_iff : proportion (length b d) (length a d) (length c e) (length a e) ↔ area e b d / area e a d = area d c e / area d a e := by
    rwa [← proportion_len_iff b d a d c e a e Lad Lae]
  have bde_cde : proportion (length b d) (length a d) (length c e) (length a e) ↔ area b d e = area c d e := by
    rw [prop_iff]; perm; field_simp
  
  -- apply I.39
  constructor
  intro ar; rw [bde_cde] at ar
  have nsabL:= not_sameside13_of_B123_online2 Badb dL
  have nsacL:= not_sameside13_of_B123_online2 Baec eL
  have ssbcL := sameside_of_diffside_diffside ⟨aL, bL, nsabL⟩ ⟨aL, cL, nsacL⟩
  exact eq_area_of_same_base_implies_para dL eL bL bM cM dP cP eP bc cd.symm ssbcL ar

  -- apply I.37
  intro pLM; rw [bde_cde]
  exact para_implies_eq_area_of_same_base bM cM dL eL pLM


/-- ## Euclid VI.2'
a line cuts the sides of the triangle proportionally iff it is parallel to one of the sides of a triangle (version AB:AD = AC:AE)
 https://mathcs.clarku.edu/~djoyce/java/elements/bookVI/propVI2.html -/
theorem proportional_iff_para' {a b c d e: point} {L M N: line}
    (dL: online d L) (eL: online e L)
    (bM: online b M) (cM: online c M)
    (aN: online a N) (dN: online d N)
    (eN: ¬ online e N)
    (Badb : B a d b) (Baec : B a e c) :
    proportion (length a b) (length a d) (length a c) (length a e) ↔ para L M := by
  have ad : length a d ≠ 0 := length_eq_zero_iff.not.mpr (ne_12_of_B Badb)
  have ae : length a e ≠ 0 := length_eq_zero_iff.not.mpr (ne_12_of_B Baec)

  have := proportional_iff_para dL eL bM cM aN dN eN Badb Baec
  rw [← proportion_len_iff a b a d a c a e ad ae]
  rw [← proportion_len_iff b d a d c e a e ad ae] at this
  rw [← length_sum_of_B Badb, ← length_sum_of_B Baec, ← this]
  perm; field_simp; ring_nf; simp

/-- equal points are colinear -/
lemma colinear_of_eq_23 (a b : point) : colinear a b b := by
  simp [colinear, and_self]; exact line_of_pts a b
/-- equal points are colinear -/
lemma colinear_of_eq_12 (a b : point) : colinear a a b := by
  rw [col321]; exact colinear_of_eq_23 b a
/-- equal points are colinear -/
lemma colinear_of_eq_13 (a b : point) : colinear a b a := by
  perma [colinear_of_eq_12 a b]

/-- not colinear implies different -/
lemma neq_12_of_not_colinear {a b c : point} (h: ¬ colinear a b c) : a ≠ b :=
  fun ab => by rw [ab] at h; exact h (colinear_of_eq_12 b c)
/-- not colinear implies different -/
lemma neq_13_of_not_colinear {a b c : point} (h: ¬ colinear a b c) : a ≠ c :=
  fun ac => by rw [ac] at h; exact h (colinear_of_eq_13 c b)
/-- not colinear implies different -/
lemma neq_23_of_not_colinear {a b c : point} (h: ¬ colinear a b c) : b ≠ c :=
  fun bc => by rw [bc] at h; exact h (colinear_of_eq_23 a c)

/-- not colinear implies one of the points is not aligned -/
lemma not_online_of_not_colinear {a b c : point} {L : line} (aL: online a L) (bL : online b L) (h: ¬ colinear a b c) :
    ¬ online c L := by
  simp [colinear, not_exists, not_and] at h; exact h L aL bL
    
/-- technical lemma: can always find a point beyond two points -/
lemma pt_extension_of_ne {b c : point} :
    b ≠ c → ∃ a : point, B b c a :=
  fun bc => by obtain ⟨ a, Ha ⟩ := length_eq_B_of_ne bc bc.symm; exact ⟨ a, Ha.1⟩

/-- similar triangles (should follow from Euclid VI.2) -/
-- show resulting lines are parallel
lemma parallel_of_similar {a b c g h : point} {AB AC BC HG: line}
    (aAB: online a AB) (bAB: online b AB) (hAB: online h AB)
    (aAC: online a AC) (gAC: online g AC)
    (bBC: online b BC) (cBC: online c BC)
    (hHG: online h HG) (gHG: online g HG)
    (bh: b ≠ h)
    (ab: a ≠ b)
    (bc: b ≠ c)
    (hg: h ≠ g)
    (ag: a ≠ g)
    (bAC: ¬ online b AC)
    (an: angle a h g = angle a b c)
    (Bahb: B a h b)
    (hss: sameside g c AB) :
    para BC HG := by

  have hbc_abc : angle h b c = angle a b c := by
    have Bcbc : ¬ B c b c:= fun Bcbc => by apply ne_13_of_B Bcbc; rfl
    exact angle_extension bh.symm ab bc.symm bc.symm bAB hAB aAB bBC cBC cBC (not_B_of_B (B_symm Bahb)) Bcbc

  have AB_HG: AB ≠ HG := by
    by_contra AB_HG
    rw [AB_HG] at aAB
    have : a = g := by
      by_contra contra
      have := line_unique_of_pts contra aAC gAC aAB gHG
      rw [← AB_HG] at this; rw [← this] at bAB
      exact bAC bAB
    exact ag this

  -- point on other side of h on line hg
  obtain ⟨t, Bght, -⟩ := length_eq_B_of_ne hg.symm hg
  have tHG := online_3_of_B Bght gHG hHG

  have tAB : ¬ online t AB := fun tAB =>
    AB_HG (line_unique_of_pts (ne_23_of_B Bght).symm tAB hAB tHG hHG)

  have gAB : ¬ online g AB := fun gAB =>
    AB_HG (line_unique_of_pts (ne_12_of_B Bght) gAB hAB gHG hHG)

  have nss := not_sameside13_of_B123_online2 Bght hAB
  have := diffside_of_sameside_diffside hss ⟨gAB, tAB, nss⟩
  apply para_of_ang_eq bh cBC bBC bAB hAB hHG tHG this _
  rw [hbc_abc, ← an, vertical_angle Bahb Bght aAB hAB gAB]

/-- two similar triangles that share an edge are equal -/
lemma length_eq_of_length_eq {a b c d e f : point}
    (Tabc : ¬ colinear a b c) (Tdef : ¬ colinear d e f) 
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f)
    (hlen: length d f = length a c) :
    length d e = length a b := by
  have df := neq_13_of_not_colinear Tdef
  have ac := neq_13_of_not_colinear Tabc
  have de := neq_12_of_not_colinear Tdef
  have ab := neq_12_of_not_colinear Tabc
  have bc := neq_23_of_not_colinear Tabc
  have ef := neq_23_of_not_colinear Tdef

  obtain ⟨AC, aAC, cAC⟩ := line_of_pts a c
  obtain ⟨AB, aAB, bAB⟩ := line_of_pts a b
  obtain ⟨BC, bBC, cBC⟩ := line_of_pts b c
  have cAB := not_online_of_not_colinear aAB bAB Tabc

  have bAC : ¬online b AC := not_online_of_not_colinear aAC cAC (by perma)

  by_contra contra
  simp_rw [← Ne.def, ne_iff_lt_or_gt] at contra

  wlog lineq : length a b < length d e
  swap

  obtain ⟨h, Hh⟩ := same_length_B_of_ne_ge ab lineq
  obtain ⟨HC, hHC, cHC⟩ := line_of_pts h c

  have hAB := online_3_of_B Hh.1 aAB bAB
  have hc : h ≠ c := fun hc => cAB (by rwa [hc] at hAB)
  have hAC : ¬ online h AC := fun hAC => by
    have := line_unique_of_pts (ne_13_of_B Hh.1).symm hAC aAC hAB aAB
    rw [this] at bAC
    exact bAC bAB

  have hac_bac := (angle_extension_of_B ac Hh.1).symm
  rw [← hac_bac] at bac_edf
  have SAS := sas hlen.symm Hh.2 (by perma only [angle] at *)
  rw [← abc_def] at SAS

  have := parallel_of_similar aAB hAB bAB aAC cAC hHC cHC bBC cBC (ne_23_of_B Hh.1).symm (ne_13_of_B Hh.1) hc bc ac hAC SAS.2.2.symm Hh.1 (sameside_rfl_of_not_online cAB)

  exact neq_of_para cHC cBC this rfl

  obtain ⟨DF, dDF, fDF⟩ := line_of_pts d f
  obtain ⟨DE, dDE, eDE⟩ := line_of_pts d e
  obtain ⟨EF, eEF, fEF⟩ := line_of_pts e f
  have fDE := not_online_of_not_colinear dDE eDE Tdef
  have eDF: ¬online e DF := not_online_of_not_colinear dDF fDF (by perma)

  refine' this Tdef Tabc bac_edf.symm abc_def.symm hlen.symm ac df ab de ef bc DF dDF fDF DE dDE eDE EF eEF fEF fDE eDF (Or.symm contra) _
  cases contra with
  | inl contra => exact contra
  | inr contra => exfalso; linarith

/-- Given two similar triangles, if the side of one triangle is smaller than that of the second,
then the remaining sides are also smaller -/
lemma length_lt_of_length_lt {a b c d e f : point}
    (Tabc : ¬ colinear a b c) (Tdef : ¬ colinear d e f) 
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f)
    (lineq: length d f < length a c) :
    length d e < length a b := by
  have df := neq_13_of_not_colinear Tdef
  have ac := neq_13_of_not_colinear Tabc
  have ab := neq_12_of_not_colinear Tabc
  have bc := neq_23_of_not_colinear Tabc

  obtain ⟨AC, aAC, cAC⟩ := line_of_pts a c
  obtain ⟨AB, aAB, bAB⟩ := line_of_pts a b
  obtain ⟨BC, bBC, cBC⟩ := line_of_pts b c

  have bAC : ¬online b AC := not_online_of_not_colinear aAC cAC (by perma)

  obtain ⟨g, Hg⟩ := B_length_eq_of_ne_lt df lineq
  have gAC := online_2_of_B Hg.1 aAC cAC
  have gBC : ¬ online g BC := fun gBC => by
    rw [line_unique_of_pts (ne_23_of_B Hg.1) gBC cBC gAC cAC] at bBC cBC
    exact bAC bBC
  have gAB : ¬ online g AB := fun gAB => by
    rw [line_unique_of_pts (ne_12_of_B Hg.1).symm gAB aAB gAC aAC] at bAB aAB
    exact bAC bAB

  by_contra contra; rw [not_lt, le_iff_lt_or_eq] at contra
  cases contra with

  | inl contra =>
    obtain ⟨h, Hh⟩ := same_length_B_of_ne_ge ab contra
    obtain ⟨HG, hHG, gHG⟩ := line_of_pts h g

    have hAB := online_3_of_B Hh.1 aAB bAB
    have hg : h ≠ g := fun hg => by
      rw [hg] at Hh
      have := online_2_of_B Hh.1 aAC (online_2_of_B Hg.1 aAC cAC)
      exact (not_online_of_not_colinear aAC cAC (by perma)) this

    have hAC : ¬ online h AC := fun hAC => by
      have := line_unique_of_pts (ne_13_of_B Hh.1).symm hAC aAC hAB aAB
      rw [this] at bAC; exact bAC bAB

    have hag_bac : angle h a g = angle b a c := by
      rw [angle_extension_of_B ac Hh.1]; perm
      rw [angle_extension_of_B (ne_13_of_B Hh.1) Hg.1]
    rw [← hag_bac] at bac_edf
    have ang := sas Hg.2 Hh.2 (by perma only [angle] at *)
    rw [← abc_def] at ang

    have' := parallel_of_similar aAB hAB bAB aAC cAC hHG gHG bBC cBC (ne_23_of_B Hh.1).symm (ne_13_of_B Hh.1) hg bc ac hAC ang.2.2.symm Hh.1 _

    have ss1 := sameside_of_para_online hHG gHG this
    have ss2 := sameside_of_B_not_online_2 (B_symm Hg.1) cBC gBC
    perm [sameside_trans (by perma at ss1) ss2]
    exact (not_sameside13_of_B123_online2 Hh.1 bBC) this
    perma [sameside_of_B_not_online_2 Hg.1 aAB gAB]

  | inr contra =>
    have: length d f = length a c := length_eq_of_length_eq (by perma) (by perma) (by perma) (asa Tabc contra (by perma) (by perma)).2.2 contra.symm
    linarith

/-- Two triangles are similar if they have two angles equal -/
theorem similar_of_AA {a b c d e f : point} (Tabc : ¬ colinear a b c) (Tdef : ¬ colinear d e f) 
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) : 
    proportion (length a b) (length d e) (length a c) (length d f) := by
  have df := neq_13_of_not_colinear Tdef
  have ac := neq_13_of_not_colinear Tabc
  have de := neq_12_of_not_colinear Tdef
  have ab := neq_12_of_not_colinear Tabc
  have bc := neq_23_of_not_colinear Tabc
  have ef := neq_23_of_not_colinear Tdef

  by_cases hlen : length d f = length a c ∨ length d e = length a b
  . wlog df_ac : length d f = length a c
    swap
    have := length_eq_of_length_eq Tabc Tdef bac_edf abc_def df_ac
    rw [this, ← df_ac]
    exact proportion_eq (length_nonneg a b) (length_nonneg d f) (length_eq_zero_iff.not.mpr ab) (length_eq_zero_iff.not.mpr df)

    rw [proportion_symm_iff]

    have leq : length d e = length a b := by
      cases hlen with
      | inl hlen => exfalso; exact df_ac hlen
      | inr hlen => exact hlen

    refine' this (by perma) (by perma) (by perma) _ de ab df ac bc.symm ef.symm (Or.symm hlen) leq
    exact (asa Tabc leq.symm bac_edf (by perma [abc_def])).2.2

  conv at hlen => rw [not_or, ← Ne.def _ _]; rhs; rw [← Ne.def _ _]

  wlog lineq : length d f < length a c
  refine' proportion_inv (this Tdef Tabc bac_edf.symm abc_def.symm ac df ab de ef bc ⟨hlen.1.symm,hlen.2.symm⟩ _)
  simp [not_lt] at lineq
  exact (Ne.symm hlen.1).lt_of_le (lineq)

  obtain ⟨AC, aAC, cAC⟩ := line_of_pts a c
  obtain ⟨AB, aAB, bAB⟩ := line_of_pts a b
  obtain ⟨BC, bBC, cBC⟩ := line_of_pts b c

  have lineq2 := length_lt_of_length_lt Tabc Tdef bac_edf abc_def lineq

  have bAC : ¬ online b AC:= not_online_of_not_colinear aAC cAC (by perma)

  obtain ⟨g, Hg⟩ := B_length_eq_of_ne_lt df lineq
  obtain ⟨h, Hh⟩ := B_length_eq_of_ne_lt de lineq2
  obtain ⟨HG, hHG, gHG⟩ := line_of_pts h g

  have gAC := online_2_of_B Hg.1 aAC cAC
  have hAB := online_2_of_B Hh.1 aAB bAB

  rw [Hg.2.symm, Hh.2.symm]

  refine' (proportional_iff_para' hHG gHG bBC cBC aAB hAB _ Hh.1 Hg.1).mpr _

  by_contra contra
  rw [line_unique_of_pts (ne_12_of_B Hg.1).symm gAC aAC contra aAB] at bAC; exact bAC bAB

  have hg : h ≠ g := fun hg => by
    rw [hg] at Hh; have := online_3_of_B Hh.1 aAC (online_2_of_B Hg.1 aAC cAC)
    exact (not_online_of_not_colinear aAC cAC (by perma)) this

  refine' para_symm (parallel_of_similar aAB bAB hAB aAC gAC bBC cBC hHG gHG (ne_23_of_B Hh.1).symm ab bc hg (ne_12_of_B Hg.1) bAC _ Hh.1 _)

  have hag_bac : angle h a g = angle b a c := by
    linperm [angle_extension_of_B ac Hh.1, angle_extension_of_B (ne_12_of_B Hh.1) Hg.1]
  linperm [(sas Hg.2 Hh.2 (by linperm)).2.2]

  exact sameside_of_B_not_online_2 Hg.1 aAB fun gAB => by
    rw [line_unique_of_pts (ne_12_of_B Hg.1) aAB gAB aAC gAC] at bAB; exact bAC bAB
