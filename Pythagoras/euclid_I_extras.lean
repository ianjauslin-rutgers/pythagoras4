import SyntheticEuclid4
import Pythagoras.proportion
import Pythagoras.tactics
import Mathlib.Tactic.SwapVar
import Mathlib.Tactic.LibrarySearch

open incidence_geometry
variable [i: incidence_geometry]


/-- find second point on line -/
lemma pt_of_line_ne_pt (a : point) (L : line):
    ∃ b : point, (b ≠ a) ∧ (online b L) := by
  obtain ⟨ b, c, hbc ⟩ := online_ne_of_line L
  by_cases b = a
  · use c
    rw [h] at hbc
    exact ⟨ hbc.1.symm, hbc.2.2 ⟩
  · use b
    exact ⟨ h, hbc.2.1 ⟩


/-- intersection of non_parallel lines -/
lemma pt_of_line_line {L M : line} (hp: ¬ para L M) :
    ∃ a:point, (online a L)∧(online a M) := by
  dsimp [para] at hp
  rw [not_forall] at hp
  obtain ⟨ e, he ⟩ := hp
  use e
  rw [not_or,not_not,not_not] at he
  exact he


/-- parallel lines don't intersect -/
lemma neq_of_para {a b : point} {L M : line}
    (haL: online a L)
    (hbM: online b M)
    (hpar: para L M) :
    a ≠ b := by
  by_contra contra
  have := online_of_online_para haL hpar
  rw [contra] at this
  exact this hbM


/-- ## Euclid I.30
parallel is (almost) transitive (almost because parallel means not equal) -/
theorem para_trans {L M N : line}
    (pLM: para L M)
    (pLN: para L N) :
    M=N ∨ (para M N) := by
  by_cases MN : M = N
  · tauto

  -- assume that M, N intersect at c; drop a line from it perpendicular to L
  by_contra npMN
  simp only [not_or] at npMN
  rcases pt_of_line_line npMN.2 with ⟨c, hcM, hcN⟩
  have hncL := online_of_online_para hcN (para_symm pLN)
  rcases perppointnon hncL with ⟨-, d, -, -, hdL, -, -, -, -⟩
  obtain ⟨O, hcO, hdO⟩ := line_of_pts c d
  have cd : c ≠ d := neq_of_para hcM hdL (para_symm pLM)
  have hLO : L ≠ O := fun LO => hncL (by rwa [← LO] at hcO)

  -- draw a circle α with center c and radius d; find its intersections with M,N
  obtain ⟨α, hα⟩ := circle_of_ne cd
  have cα := inside_circle_of_center hα.1
  have αM := line_circle_inter_of_inside_online hcM cα
  have αN := line_circle_inter_of_inside_online hcN cα
  obtain ⟨a, a', aa', haM, ha'M, aα⟩ := pts_of_line_circle_inter αM
  obtain ⟨b, b', bb', hbN, hb'N, bα⟩ := pts_of_line_circle_inter αN
  have Baca' := B_of_line_circle_inter aa' hcM haM ha'M aα.1 aα.2 cα
  have Bbcb' := B_of_line_circle_inter bb' hcN hbN hb'N bα.1 bα.2 cα
  have ac := ne_12_of_B Baca'
  have bc := ne_12_of_B Bbcb'
  have b'c := (ne_23_of_B Bbcb').symm
  have hnaO: ¬ online a O := fun haO => neq_of_para hdL hdO (by rwa [← line_unique_of_pts ac haO hcO haM hcM] at pLM) (by rfl)
  have hnbO : ¬ online b O := fun hbO => neq_of_para hdL hdO (by rwa [← line_unique_of_pts bc hbO hcO hbN hcN] at pLN) (by rfl)
  have hnb'O : ¬ online b' O := fun hb'O => neq_of_para hdL hdO (by rwa [← line_unique_of_pts b'c hb'O hcO hb'N hcN] at pLN) (by rfl)
  have hnaN: ¬ online a N := fun haN => MN (line_unique_of_pts ac haM hcM haN hcN)
  have hnbM: ¬ online b M := fun hbM => MN (line_unique_of_pts bc hbM hcM hbN hcN)
  have hnb'M: ¬ online b' M := fun hb'M => MN (line_unique_of_pts b'c hb'M hcM hb'N hcN)
  have hNO : N ≠ O := fun NO => hnbO (by rwa [NO] at hbN)
  have hMO : M ≠ O := fun MO => hnaO (by rwa [MO] at haM)

  -- choose b so that a, b that lie on the same side of O by symmetry
  by_cases ssbaO: sameside b a O
  have ssabO := sameside_symm ssbaO
  swap
  have nsbb'O := not_sameside13_of_B123_online2 Bbcb' hcO
  have ssabO := sameside_of_diffside_diffside ⟨hnbO, hnaO, ssbaO⟩ ⟨hnbO, hnb'O, nsbb'O⟩
  swap_var b ↔ b'
  swap_var hbN ↔ hb'N
  swap_var hnbM ↔ hnb'M
  swap_var hnbO ↔ hnb'O
  swap_var bc ↔ b'c
  all_goals {
    have ss1 := sameside_of_sameside_not_sameside cd hcO hcN hcM hdO hbN haM hnaN (sameside_symm ssabO)
    have ss2 := not_sameside_of_sameside_sameside hcO hcM hcN hdO haM hbN ssabO
    have ss: sameside d a N ∨ sameside d b M := by tauto

    -- choose e on L so that it lies on the opposite side w.r.t. to O than a, b
    obtain ⟨e0, e0d, -⟩ := pt_of_line_ne_pt d L
    obtain ⟨β, hβ⟩ := circle_of_ne e0d.symm
    have dβ := inside_circle_of_center hβ.1
    have βL := line_circle_inter_of_inside_online hdL dβ
    obtain ⟨e, e', ee', heL, he'L, eβ⟩ := pts_of_line_circle_inter βL
    have Bede' := B_of_line_circle_inter ee' hdL heL he'L eβ.1 eβ.2 dβ
    have ed := ne_12_of_B Bede'
    have e'd := (ne_23_of_B Bede').symm
    have hneO : ¬ online e O := fun heO => hLO (line_unique_of_pts ed heL hdL heO hdO)
    have hne'O : ¬ online e' O := fun he'O => hLO (line_unique_of_pts e'd he'L hdL he'O hdO)
    by_cases nsaeO: sameside a e' O
    have nse'eO := not_sameside13_of_B123_online2 (B_symm Bede') hdO
    have dsaeO := difsamedif (sameside_symm nsaeO) ⟨hne'O, hneO, nse'eO⟩
    swap
    swap_var e ↔ e'
    swap_var heL ↔ he'L
    swap_var ed ↔ e'd
    swap_var hneO ↔ hne'O
    have dsaeO: diffside a e O := ⟨hnaO, hneO, nsaeO⟩
    all_goals {
      have dsbeO := difsamedif ssabO dsaeO
      have acd := parapostcor ed haM hcM hdL heL hdO hcO (para_symm pLM) dsaeO
      have bcd := parapostcor ed hbN hcN hdL heL hdO hcO (para_symm pLN) dsbeO

      -- argue about angles given by parallel assumptions in two symmetric cases
      cases ss with
      | inl ssdaN =>
        have sum := (angle_add_iff_sameside bc.symm cd hcN hbN hcO hdO hnaO hnaN hNO).2 ⟨sameside_symm ssabO, ssdaN⟩
        rw [acd, bcd] at sum
        simp at sum
        exact hnaN ((angle_zero_iff_online bc.symm ac.symm hcN hbN).2 sum).1

      | inr ssdbM =>
      -- sameside d b M
        have sum := (angle_add_iff_sameside ac.symm cd hcM haM hcO hdO hnbO hnbM hMO).2 ⟨ssabO, ssdbM⟩
        rw [acd, bcd] at sum
        simp at sum
        exact hnbM ((angle_zero_iff_online ac.symm bc.symm hcM haM).2 sum).1
    }
  }


/-- degenerate area: more general statement -/
lemma area_of_eq (a b c : point)
    (h: a=b ∨ a=c ∨ b=c) :
    area a b c =0 := by
  cases h with
  | inl ab =>
    rw [ab]
    exact degenerate_area b c
  | inr h =>
    cases h with
    | inl ac =>
      rw [ac]
      permute [132]
      exact degenerate_area c b
    | inr bc =>
      rw [bc]
      permute [321]
      exact degenerate_area c a


/-- equivalent areas of paralellogram -/
lemma area_of_parallelogram {a b c d : point} {L M N O : line}
    (haL: online a L) (hbL: online b L)
    (hbM: online b M) (hcM: online c M)
    (hcN: online c N) (hdN: online d N)
    (hdO: online d O) (haO: online a O)
    (parLN: para L N)
    (parMO: para M O) :
    area a b c + area a d c = 2*(area a b c)
    ∧ area b a d + area b c d = 2*(area a b c) := by
  constructor
  have := (parasianar hbL haL hcN hdN hbM hcM haO hdO parLN parMO).2.2
  permute [321] at this
  rw [this.symm]
  ring_nf

  have := (parasianar haL hbL hdN hcN haO hdO hbM hcM parLN (para_symm parMO)).2.2
  permute [321] at this
  rw [this.symm]
  ring_nf

  permute [312, ←321]
  field_simp
  exact triarea hdN hcN hbL haL (para_symm parLN)


/-- non-degeneracy of triangle -/
lemma not_online_of_triangle {a b c : point} {L M : line}
    (haL: online a L)
    (hbL: online b L)
    (hbM: online b M)
    (hcM: online c M)
    (hn: ¬ online a M)
    (hdeg: b ≠ c) :
    ¬ online c L := by
  by_contra contra
  rw [line_unique_of_pts hdeg hbL contra hbM hcM] at haL
  exact hn haL


/--parallel line through point -/
lemma parallel_of_line_pt {a : point} {L : line}
    (haL: ¬ online a L) :
    ∃ M : line, (online a M) ∧ (para L M) := by
  obtain ⟨ b, hb ⟩ := online_of_line L
  obtain ⟨ c, hc ⟩ := pt_of_line_ne_pt b L
  have := drawpar hc.1 hc.2 hb haL
  obtain ⟨ throwaway,O,hO ⟩ := drawpar hc.1 hc.2 hb haL
  use O
  exact ⟨ hO.2.1, para_symm hO.2.2.2.2 ⟩


/-- parallel projection of point -/
lemma parallel_projection {a : point}{L M N : line}
    (haM: online a M)
    (hpar: para M N)
    (h_L_npara_M: ¬ para L M)
    (haL: ¬ online a L) :
    ∃ b : point, ∃ O : line, (online b N) ∧ (online b O) ∧ (online a O) ∧ (para L O) := by
  -- intersections with L
  obtain ⟨ c, hc ⟩ := pt_of_line_line h_L_npara_M
  have h_L_npara_N : ¬ para L N := by
    by_contra contra
    cases para_trans (para_symm hpar) (para_symm contra) with
    | inl h =>
      rw [h] at haM
      exact haL haM
    | inr h =>
      exact h_L_npara_M (para_symm h)

  obtain ⟨ d, hd ⟩ := pt_of_line_line h_L_npara_N

  have h_c_ne_d : c ≠ d := by
    by_contra contra
    rw [contra] at hc
    dsimp [para] at hpar
    cases hpar d with
    | inl h =>
      exact h hc.2
    | inr h =>
      exact h hd.2

  -- construct parallel to L through a
  obtain ⟨ throwaway,O,hO ⟩ := drawpar h_c_ne_d hc.1 hd.1 haL

  -- construct intersection of O and M
  have h_O_npara_N : ¬ para O N := by
    by_contra contra
    have pNO := para_trans contra  hO.2.2.2.2
    cases pNO with
    | inl pNO =>
      rw [pNO] at hpar
      exact h_L_npara_M (para_symm hpar)
    | inr pNO =>
      exact (online_of_online_para hd.1 (para_symm pNO)) hd.2

  obtain ⟨ ap, hap ⟩ := pt_of_line_line h_O_npara_N

  use ap
  use O

  exact ⟨ hap.2, hap.1, hO.2.1, (para_symm hO.2.2.2.2) ⟩


/-- intersecting lines cannot be parallel -/
lemma not_para_of_online_online {a : point} {L M : line} :
    (online a L) → (online a M) → ¬ para L M := by
  intro hL hM
  dsimp [para]
  simp only [not_forall]
  use a
  rw [not_or,not_not,not_not]
  exact ⟨ hL, hM ⟩


/-- diagonals of a trapezoid imply diffside -/
theorem diffside_of_trapezoid {a b c d : point} {L M N : line}
    (haL: online a L) (hbL: online b L)
    (hbM: online b M) (hcM: online c M)
    (hcN: online c N) (hdN: online d N)
    {D : line}
    (hbD: online b D) (hdD: online d D)
    (parLN: para L N)
    (h_nondeg: a ≠ b ∧ c ≠ d) :
    diffside a c D ∨ diffside a d M := by
  dsimp [diffside]
  by_cases h_ss : sameside a c D
  right
  constructor
  exact not_online_of_triangle hcM hbM hbL haL (online_of_online_para hcN (para_symm parLN)) h_nondeg.1.symm
  constructor
  exact not_online_of_triangle hbM hcM hcN hdN (online_of_online_para hbL parLN) h_nondeg.2

  have := sameside_of_online_online_para hcN hdN (para_symm parLN)
  exact not_sameside_of_sameside_sameside hbL hbM hbD haL hcM hdD this h_ss

  left
  constructor
  exact not_online_of_triangle hdD hbD hbL haL (online_of_online_para hdN (para_symm parLN)) h_nondeg.1.symm
  constructor
  exact not_online_of_triangle hbD hdD hdN hcN (online_of_online_para hbL parLN) h_nondeg.2.symm
  exact h_ss

/-- cannot have B a b c if lengths don't match up -/
lemma not_B_of_short {a b c : point}
    (hlen: length a b < length a c) :
    ¬ B a c b := by
  by_contra contra
  rw [(length_sum_of_B contra).symm] at hlen
  linarith [length_nonneg c b]

/-- B_of_three_online_ne but with one length too short -/
lemma B_of_three_online_ne_short {a b c : point} {L : line}
    (hlen: length a b < length a c) :
    a ≠ b → a ≠ c → b ≠ c → online a L → online b L → online c L →  B a b c ∨ B b a c := by
  intro ab ac bc aL bL cL
  have := B_of_three_online_ne ab ac bc aL bL cL
  convert this
  simp [not_B_of_short hlen]


/-- complement to same_length_of_ne_le -/
theorem same_length_B_of_ne_ge {a b c d : point} (a_ne_b : a ≠ b) (big : length a b < length c d) :
    ∃ (p : point), B a b p ∧ length a p = length c d := by
  have c_ne_d : c ≠ d := by
    by_contra contra
    rw [contra] at big
    rw [length_eq_zero_iff.mpr (Eq.refl d)] at big
    have := length_nonneg a b
    exact not_lt_of_ge this big

  obtain ⟨q,hq⟩ := same_length_B_of_ne_four a_ne_b.symm c_ne_d

  have a_ne_q : a ≠ q := by
    by_contra contra
    rw [contra, length_eq_zero_iff.mpr (Eq.refl q)] at hq
    rw [hq.2.symm] at big
    have := length_nonneg a b
    exact not_lt_of_ge this big

  obtain ⟨C, hC⟩ := circle_of_ne a_ne_q

  obtain ⟨p, hp⟩ := pt_on_circle_of_inside_ne a_ne_q (inside_circle_of_center hC.1)

  obtain ⟨AB, hAB⟩ := line_of_pts a b
  have q_online_AB := online_3_of_B hq.1 hAB.2 hAB.1
  have p_online_AB := online_3_of_B (B_symm hp.1) q_online_AB hAB.1

  have := (on_circle_iff_length_eq hC.1 hp.2).mpr hC.2
  rw [this.symm] at hq

  have b_ne_p : b ≠ p := by
    by_contra contra
    rw [contra.symm] at hq
    rw [contra] at hq big
    rw [hq.2] at big
    simp at big

  rw [hq.2.symm] at big

  have a_ne_p := (ne_12_of_B hp.1).symm

  use p
  refine' ⟨_, hq.2⟩
  have B3 := B_of_three_online_ne_short big a_ne_b a_ne_p b_ne_p hAB.1 hAB.2 p_online_AB
  cases B3 with
  | inl B3 =>
    exact B3
  | inr B3 =>
    exfalso
    exact (not_B324_of_B123_B124 (B_symm hq.1) (B_symm hp.1)) B3


/-- ## Euclid I.33
lines which join the ends of equal and parallel lines in the same directions are themselves equal and parallel
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI33.html -/
theorem para_len_parallelogram {a b c d : point} {L M N O P : line}
    (haL: online a L) (hbL: online b L)
    (hbM: online b M) (hcM: online c M)
    (hcN: online c N) (hdN: online d N)
    (hdO: online d O) (haO: online a O)
    (hcP: online c P) (haP: online a P)
    (hdiff: d ≠ c)
    (hside: diffside b d P)
    (pLN: para L N)
    (hlen: length a b = length c d) :
    para O M := by
  have :=parapostcor hdiff hbL haL hcN hdN hcP haP pLN hside
  rw [angle_symm a c d] at this
  have := ((sas hlen (length_symm a c) this).2.2).symm
  rw [angle_symm c a d] at this

  exact angeqpar (neq_of_para hdN haL (para_symm pLN)) (neq_of_para haL hcN pLN) (neq_of_para hcN hbL (para_symm pLN)) hdO haO hcM hbM haP hcP this (diffside_symm hside)


/-- ## Euclid I.36
parallelograms which are on equal bases and in the same parallels equal one another
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI36.html -/
theorem eq_of_parallelogram_of_eq_basis_of_diffside {a b c d e f g h: point} {L M K N O P: line}
    (haL: online a L) (hdL: online d L) (heL: online e L) (hhL: online h L)
    (hbM: online b M) (hcM: online c M) (hfM: online f M) (hgM: online g M)
    (haK: online a K) (hbK: online b K)
    (hdN: online d N) (hcN: online c N)
    (heO: online e O) (hfO: online f O)
    (hhP: online h P) (hgP: online g P)
    (parLM: para L M) (parKN: para K N) (parOP: para O P)
    (hlen: length b c = length f g)
    {S: line}
    (hcS: online c S) (heS: online e S)
    (hside: diffside b h S)
    (h_b_ne_c: b ≠ c) :
    area a b c + area a d c = area e f g + area e h g := by
  obtain ⟨ Q, hQ ⟩ := line_of_pts b e
  obtain ⟨ R, hR ⟩ := line_of_pts c h
  have' parQR := para_len_parallelogram heL hhL hR.2 hR.1 hcM hbM hQ.1 hQ.2 hcS heS h_b_ne_c (diffside_symm hside) parLM _

  have eq1 := parallelarea haL hdL hbM hcM heL hhL haK hbK hdN hcN hQ.1 hQ.2 hR.1 hR.2 parLM parKN parQR

  have eq2 := parallelarea hbM hcM heL hhL hfM hgM hQ.1 hQ.2 hR.1 hR.2 heO hfO hhP hgP (para_symm parLM) parQR parOP
  permute [132] at eq2
  rw [add_comm] at eq2
  permute [132] at eq2
  rw [eq2] at eq1

  have arp := (area_of_parallelogram haL hdL hdN hcN hcM hbM hbK haK parLM (para_symm parKN)).1
  rw [add_comm] at arp
  rw [arp]

  have arp := (area_of_parallelogram heL hhL hhP hgP hgM hfM hfO heO parLM (para_symm parOP)).1
  rw [add_comm] at arp
  rw [arp]

  have arp := (area_of_parallelogram haL hdL hdN hcN hcM hbM hbK haK parLM (para_symm parKN)).2
  permute [321] at arp
  permute [132] 2 at arp
  rw [arp] at eq1
  rw [eq1]

  have arp := (area_of_parallelogram heL hhL hhP hgP hgM hfM hfO heO parLM (para_symm parOP)).2
  permute [312] at arp
  rw [arp.symm, add_comm]

  rw [Eq.symm (parasianar hfM hgM heL hhL hfO heO hgP hhP (para_symm parLM) parOP).1]
  rw [hlen.symm]
  exact length_symm b c

theorem eq_of_parallelogram_of_eq_basis {a b c d e f g h: point} {L M K N O P: line}
    (haL: online a L) (hdL: online d L) (heL: online e L) (hhL: online h L)
    (hbM: online b M) (hcM: online c M) (hfM: online f M) (hgM: online g M)
    (haK: online a K) (hbK: online b K)
    (hdN: online d N) (hcN: online c N)
    (heO: online e O) (hfO: online f O)
    (hhP: online h P) (hgP: online g P)
    (parLM: para L M) (parKN: para K N) (parOP: para O P)
    (hlen: length b c = length f g) :
    area a b c + area a d c = area e f g + area e h g := by
  have h_fg_eq_eh := (parasianar heL hhL hfM hgM heO hfO hhP hgP parLM parOP).1
  -- trivial case: b=c
  by_cases h_b_ne_c: b=c
  · have h_f_eq_g := (length_eq_zero_iff.mp (Eq.trans hlen.symm (length_eq_zero_iff.mpr h_b_ne_c)))

    have := (parasianar haL hdL hbM hcM haK hbK hdN hcN parLM parKN).1
    have h_a_eq_d := (length_eq_zero_iff.mp (Eq.trans this (length_eq_zero_iff.mpr h_b_ne_c)))

    have h_e_eq_h := (length_eq_zero_iff.mp (Eq.trans h_fg_eq_eh (length_eq_zero_iff.mpr h_f_eq_g)))

    rw [area_of_eq a b c _, area_of_eq a d c _, area_of_eq e f g _, area_of_eq e h g _]
    
    left
    exact h_e_eq_h

    repeat right
    exact h_f_eq_g

    left
    exact h_a_eq_d

    repeat right
    exact h_b_ne_c

  have h_e_ne_h : e ≠ h := by
    by_contra contra
    rw [hlen.symm] at h_fg_eq_eh
    exact h_b_ne_c (length_eq_zero_iff.mp (Eq.trans h_fg_eq_eh.symm (length_eq_zero_iff.mpr contra)))
  rw [(Ne.def b c).symm] at h_b_ne_c

  obtain ⟨ S, hS ⟩ := line_of_pts c e
  obtain ⟨ Q, hQ ⟩ := line_of_pts b e
  obtain ⟨ R, hR ⟩ := line_of_pts c h

  have hside := diffside_of_trapezoid hhL heL hQ.2 hQ.1 hbM hcM hS.2 hS.1 parLM ⟨ h_e_ne_h.symm, h_b_ne_c ⟩

  cases hside with
  | inl hside =>
    exact eq_of_parallelogram_of_eq_basis_of_diffside haL hdL heL hhL hbM hcM hfM hgM haK hbK hdN hcN heO hfO hhP hgP parLM parKN parOP hlen hS.1 hS.2 (diffside_symm hside) h_b_ne_c

  | inr hside =>
    -- invert parallelogram
    rw [length_symm b c] at hlen
    have := eq_of_parallelogram_of_eq_basis_of_diffside hdL haL heL hhL hcM hbM hfM hgM hdN hcN haK hbK heO hfO hhP hgP parLM (para_symm parKN) parOP hlen hQ.1 hQ.2 (diffside_symm hside) h_b_ne_c.symm
    permute [321] at this
    permute [321] 2 at this
    rw [add_comm] at this
    rw [this.symm, (area_of_parallelogram haK hbK hbM hcM hcN hdN hdL haL parKN (para_symm parLM)).2]
    rw [(area_of_parallelogram haK hbK hbM hcM hcN hdN hdL haL parKN (para_symm parLM)).1]

/-- ## Euclid I.38
triangles which are on equal bases and in the same parallels equal one another (version where the vertex is different for both triangles)
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI38.html -/
theorem eq_area_of_eq_base {a b c d e f : point} {L M : line}
    (haM: online a M)
    (hbL: online b L)
    (hcL: online c L)
    (hdM: online d M)
    (heL: online e L)
    (hfL: online f L)
    (pLM: para L M)
    (hlen: length b c = length e f) :
    area a b c=area d e f := by
  -- trivial case: b=c
  by_cases h_b_ne_c: b=c
  · rw [area_of_eq a b c _, area_of_eq d e f _]

    repeat right
    exact length_eq_zero_iff.mp (Eq.trans hlen.symm (length_eq_zero_iff.mpr h_b_ne_c))

    repeat right
    exact h_b_ne_c


  have h_e_ne_f : e ≠ f := by
    by_contra contra
    exact h_b_ne_c (length_eq_zero_iff.mp (Eq.trans hlen (length_eq_zero_iff.mpr contra)))
  rw [(Ne.def b c).symm] at h_b_ne_c

  -- line through a c abd d e
  obtain ⟨ K, hK ⟩ := line_of_pts a c
  obtain ⟨ N, hN ⟩ := line_of_pts d e

  -- construct parallel projection of b through a c
  have h_a_nonline_L := online_of_online_para haM (para_symm pLM)
  have := not_online_of_triangle hK.1 hK.2 hcL hbL h_a_nonline_L h_b_ne_c.symm
  obtain ⟨ g,O,hg ⟩ := parallel_projection hbL pLM (not_para_of_online_online hK.2 hcL) this

  -- construct parallel projection of f through d e
  have h_d_nonline_L := online_of_online_para hdM (para_symm pLM)
  have := not_online_of_triangle hN.1 hN.2 heL hfL h_d_nonline_L h_e_ne_f
  obtain ⟨ h,P,hh ⟩ := parallel_projection hfL pLM (not_para_of_online_online hN.2 heL) this

  have := eq_of_parallelogram_of_eq_basis 
    hg.1 haM hdM hh.1 hbL hcL heL hfL hg.2.1 hg.2.2.1 hK.1 hK.2 hN.1 hN.2 hh.2.1 hh.2.2.1
    (para_symm pLM) (para_symm hg.2.2.2) hh.2.2.2
    hlen

  permute [321] at this
  permute [321] 2 at this

  rw [(area_of_parallelogram hbL hcL hK.2 hK.1 haM hg.1 hg.2.1 hg.2.2.1 pLM hg.2.2.2).2] at this
  -- permute [312] at this
  rw [(area_of_parallelogram hN.1 hN.2 heL hfL hh.2.2.1 hh.2.1 hh.1 hdM hh.2.2.2 pLM).1] at this
  simp at this
  permute [231]
  exact this

/-- ## Euclid I.38
triangles which are on equal bases and in the same parallels equal one another (version where the vertex is the same for both triangles)
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI38.html -/
theorem eq_area_of_eq_base_samevertex (a : point) {b c e f : point} {L : line}
    (hbL: online b L)
    (hcL: online c L)
    (heL: online e L)
    (hfL: online f L)
    (hlen: length b c = length e f) :
    area a b c=area a e f := by
  -- trivial case: b=c
  by_cases h_b_ne_c : b=c
  · rw [length_eq_zero_iff.mpr h_b_ne_c] at hlen
    have := length_eq_zero_iff.mp hlen.symm
    rw [area_of_eq a b c _, area_of_eq a e f _]
    repeat tauto

  have h_e_ne_f : e ≠ f := by
    have := length_eq_zero_iff.not.mpr h_b_ne_c
    rw [hlen] at this
    exact length_eq_zero_iff.not.mp this

  -- trivial case online a L
  by_cases h_a_nonline_L : online a L
  · have := (area_zero_iff_online h_b_ne_c hbL hcL).mpr h_a_nonline_L
    permute [231]
    rw [this]
    apply Eq.symm
    have := (area_zero_iff_online h_e_ne_f heL hfL).mpr h_a_nonline_L
    permute

  obtain ⟨ M, hM ⟩ := parallel_of_line_pt h_a_nonline_L
  exact eq_area_of_eq_base hM.1 hbL hcL hM.1 heL hfL hM.2 hlen


/-- ## Euclid I.37
triangles which are on the same base and in the same parallels equal one another (a special case of I.38)
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI37.html -/
theorem para_implies_eq_area_of_same_base {a b c d : point} {L M : line}
    (haM: online a M)
    (hbL: online b L)
    (hcL: online c L)
    (hdM: online d M)
    (pLM: para L M) :
    area a b c = area d b c := by
  apply eq_area_of_eq_base haM hbL hcL hdM hbL hcL pLM
  simp


/-- area of a triangle cannot equal the area of its subtriangle -/
lemma tri_sum_contra {b c d e: point} {O : line}
    (hbO: online b O)
    (hdO: online d O)
    (heO: online e O)
    (hncO: ¬ online c O)
    (bd: b ≠ d)
    (de: d ≠ e)
    (eb: e ≠ b)
    (hBbed: B b e d)
    (harea: area b c d = area e b c) :
    False := by
  have sum:= (area_add_iff_B bd de eb hbO hdO heO hncO).1 hBbed
  rw [harea] at sum
  permute [213, 321] at sum
  try simp at sum
  have hcO := (area_zero_iff_online de hdO heO).1 (sum)
  contradiction


  /-- ## Euclid I.39
  equal triangles which are on the same base and on the same side are also in the same parallels
  https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI39.html -/
  theorem eq_area_of_same_base_implies_para {a b c d : point} {L M O : line}
    (hbL: online b L)
    (hcL: online c L)
    (hnaL: ¬ online a L)
    (haM: online a M)
    (hdM: online d M)
    (hbO: online b O)
    (hdO: online d O)
    (hncO: ¬ online c O)
    (ad: a ≠ d)
    (bc: b ≠ c)
    (bd: b ≠ d)
    (ssadL: sameside a d L)
    (harea: area a b c = area d b c) :
    para L M := by
  rcases drawpar bc hbL hcL hnaL with ⟨-, N,_,haN,-,-,pNL⟩
  have pLN:= para_symm pNL
  -- show that N and O intersect
  have npNO: ¬ para N O := by
    by_contra pNO
    have LO_or_pLO := para_trans pNL pNO

    cases LO_or_pLO with
    | inl LO =>
      rw [← LO] at hncO
      exact hncO hcL

    | inr pLO =>
      apply neq_of_para hbL hbO pLO
      rfl

  -- contruct e as intersection of N and O
  rcases pt_of_line_line npNO with ⟨e, heN, heO⟩

  have harea2: area a b c = area e b c := by
    apply eq_area_of_eq_base haN hbL hcL heN hbL hcL pLN
    rfl
  rw [harea] at harea2
  permute [231] at harea2

  have be := neq_of_para hbL heN pLN
  by_cases de: d = e
  -- case d = e
  rw [← de] at heN
  rwa [line_unique_of_pts ad haM hdM haN heN]

  -- case d != e (cannot actually occur)
  rw [← Ne.def d e] at de
  exfalso

  cases B_of_three_online_ne be bd de.symm hbO heO hdO with
  -- case B b e d
  | inl hBbed =>
  -- cases B_of_three_online_ne be bd de.symm hbO heO hdO with hBbed hB
    exact tri_sum_contra hbO hdO heO hncO bd de be.symm hBbed harea2

  | inr hB =>
    cases hB with
  -- case B e b d
  | inl hBebd =>
    have ssaeL := sameside_of_online_online_para haN heN pNL
    have ssedL := sameside_symm (sameside_trans ssadL ssaeL)
    have dsedL:= not_sameside13_of_B123_online2 hBebd hbL
    exact dsedL ssedL

  -- case B b d e
  | inr hBbde =>
    permute [312] at harea2
    have := harea2.symm
    permute [231] at this
    exact tri_sum_contra hbO heO hdO hncO be de.symm bd.symm hBbde this
