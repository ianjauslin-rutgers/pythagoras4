import SyntheticEuclid4
import Pythagoras.proportion
import Mathlib.Tactic.SwapVar

open incidence_geometry
variable [i: incidence_geometry]

/-- given two lengths, one is trivial iff the other is -/
lemma same_len_pts_coincide_iff {a b c d : point} (hlen: length a b = length c d) : a = b ↔ c = d := by
    rw [← @length_eq_zero_iff i a b, ← @length_eq_zero_iff i c d, hlen]

/-- find second point on line -/
lemma pt_of_line_ne_pt (a : point) (L : line):
    ∃ b : point, (b ≠ a) ∧ (online b L) := by
  obtain ⟨ b, c, hbc ⟩ := online_ne_of_line L
  by_cases b = a
  · simp_rw [h] at hbc; exact ⟨c, hbc.1.symm, hbc.2.2 ⟩
  · exact ⟨ b, h, hbc.2.1 ⟩

/-- intersection of non_parallel lines -/
lemma pt_of_line_line {L M : line} (hp: ¬ para L M) :
    ∃ a:point, (online a L)∧(online a M) := by
  simp_rw [para, not_forall, not_or, not_not] at hp; exact hp

/-- parallel lines don't intersect -/
lemma neq_of_para {a b : point} {L M : line}
    (haL: online a L)
    (hbM: online b M)
    (hpar: para L M) :
    a ≠ b := fun ab => by
  have := offline_of_para haL hpar
  rw [ab] at this; exact this hbM

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
  simp [not_or] at npMN
  rcases pt_of_line_line npMN.2 with ⟨c, hcM, hcN⟩
  have hncL := offline_of_para hcN (para_symm pLN)
  rcases perpendicular_of_not_online hncL with ⟨-, -, d, -, -, -, hdL, -, -⟩
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
  have hnaO: ¬ online a O := fun haO => neq_of_para hdL hdO (by rwa [← line_unique_of_pts ac haO hcO haM hcM] at pLM) rfl
  have hnbO : ¬ online b O := fun hbO => neq_of_para hdL hdO (by rwa [← line_unique_of_pts bc hbO hcO hbN hcN] at pLN) rfl
  have hnb'O : ¬ online b' O := fun hb'O => neq_of_para hdL hdO (by rwa [← line_unique_of_pts b'c hb'O hcO hb'N hcN] at pLN) rfl
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
    have dsaeO := diffside_of_sameside_diffside (sameside_symm nsaeO) ⟨hne'O, hneO, nse'eO⟩
    swap
    swap_var e ↔ e'
    swap_var heL ↔ he'L
    swap_var ed ↔ e'd
    swap_var hneO ↔ hne'O
    have dsaeO: diffside a e O := ⟨hnaO, hneO, nsaeO⟩
    all_goals {
      have dsbeO := diffside_of_sameside_diffside ssabO dsaeO
      have acd := alternate_eq_of_para haM hcM hcO hdO hdL heL dsaeO (para_symm pLM)
      have bcd := alternate_eq_of_para hbN hcN hcO hdO hdL heL dsbeO (para_symm pLN)

      -- argue about angles given by parallel assumptions in two symmetric cases
      cases ss with
      | inl ssdaN =>
        have sum := (angle_add_iff_sameside bc.symm cd hcN hbN hcO hdO hnaO hnaN hNO).2 ⟨sameside_symm ssabO, ssdaN⟩
        rw [acd, bcd] at sum
        simp [self_eq_add_left] at sum
        exact hnaN ((angle_zero_iff_online bc.symm ac.symm hcN hbN).2 sum).1

      | inr ssdbM =>
      -- sameside d b M
        have sum := (angle_add_iff_sameside ac.symm cd hcM haM hcO hdO hnbO hnbM hMO).2 ⟨ssabO, ssdbM⟩
        rw [acd, bcd] at sum
        simp [self_eq_add_left] at sum
        exact hnbM ((angle_zero_iff_online ac.symm bc.symm hcM haM).2 sum).1
    }
  }

/-- degenerate area: more general statement -/
lemma area_of_eq (a b c : point)
    (h: a=b ∨ a=c ∨ b=c) :
    area a b c = 0 := by
  cases h with
  | inl ab => rw [ab]; exact degenerate_area b c
  | inr h => cases h with
    | inl ac => rw [ac, ar132]; exact degenerate_area c b
    | inr bc => rw [bc, ar321]; exact degenerate_area c a

/-- equivalent areas of paralellogram -/
lemma area_of_parallelogram {a b c d : point} {L M N O : line}
    (abcd: paragram a b c d L M N O) :
    area a b c + area a d c = 2 * (area a b c)
    ∧ area b a d + area b c d = 2 * (area a b c) := by
  obtain ⟨ haL, hbL, hbM, hcM, hcN, hdN, hdO, haO, pLN, pMO⟩ := id abcd
  have bcda : paragram b c d a M N O L := by splitAll <;> perma only [para]

  constructor
  . linperm [(len_ang_area_eq_of_parallelogram bcda).2.2]
  . linperm [(len_ang_area_eq_of_parallelogram abcd).2.2, triarea hcN hdN hbL haL (by perma)]

/-- non-degeneracy of triangle -/
lemma not_online_of_triangle {a b c : point} {L M : line}
    (haL: online a L)
    (hbL: online b L)
    (hbM: online b M)
    (hcM: online c M)
    (hn: ¬ online a M)
    (hdeg: b ≠ c) :
    ¬ online c L := fun hcL => by
  rw [line_unique_of_pts hdeg hbL hcL hbM hcM] at haL; exact hn haL

/--parallel line through point -/
lemma parallel_of_line_pt {a : point} {L : line}
    (haL: ¬ online a L) :
    ∃ M : line, (online a M) ∧ (para L M) := by
  dsimp [para]; exact para_of_offline haL

/-- parallel projection of point -/
lemma parallel_projection {a : point}{L M N : line}
    (haM: online a M)
    (hpar: para M N)
    (h_L_npara_M: ¬ para L M)
    (haL: ¬ online a L) :
    ∃ b : point, ∃ O : line, (online b N) ∧ (online b O) ∧ (online a O) ∧ (para L O) := by

  -- intersections with L
  have h_L_npara_N : ¬ para L N := fun pLN => by
    cases para_trans (para_symm hpar) (para_symm pLN) with
    | inl h => rw [h] at haM; exact haL haM
    | inr h => exact h_L_npara_M (para_symm h)
  obtain ⟨ d, hd ⟩ := pt_of_line_line h_L_npara_N

  -- construct parallel to L through a
  obtain ⟨ O, haO, pLO ⟩ := para_of_offline haL

  -- construct intersection of O and M
  have h_O_npara_N : ¬ para O N := fun pON => by
    have pNO := para_trans pON (para_symm pLO)
    cases pNO with
    | inl pNO => rw [pNO] at hpar; exact h_L_npara_M (para_symm hpar)
    | inr pNO => exact (offline_of_para hd.1 (para_symm pNO)) hd.2

  obtain ⟨ ap, hap ⟩ := pt_of_line_line h_O_npara_N
  exact ⟨ ap, O, hap.2, hap.1, haO, pLO ⟩

/-- intersecting lines cannot be parallel -/
lemma not_para_of_online_online {a : point} {L M : line} :
    (online a L) → (online a M) → ¬ para L M := fun hL hM => by
  simp_rw [para, not_forall, not_or, not_not]
  exact ⟨ a, hL, hM ⟩

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
  by_cases h_ss : sameside a c D
  . right
    refine' ⟨ not_online_of_triangle hcM hbM hbL haL (offline_of_para hcN (para_symm parLN)) h_nondeg.1.symm, _ ⟩
    refine' ⟨ not_online_of_triangle hbM hcM hcN hdN (offline_of_para hbL parLN) h_nondeg.2, _ ⟩
    have := sameside_of_para_online hcN hdN (para_symm parLN)
    exact not_sameside_of_sameside_sameside hbL hbM hbD haL hcM hdD this h_ss

  . left
    refine' ⟨ not_online_of_triangle hdD hbD hbL haL (offline_of_para hdN (para_symm parLN)) h_nondeg.1.symm, _ ⟩
    refine' ⟨ not_online_of_triangle hbD hdD hdN hcN (offline_of_para hbL parLN) h_nondeg.2.symm, h_ss ⟩

/-- cannot have B a b c if lengths don't match up -/
lemma not_B_of_short {a b c : point}
    (hlen: length a b < length a c) :
    ¬ B a c b := fun hBacb => by
  rw [(length_sum_of_B hBacb).symm] at hlen; linarith [length_nonneg c b]

/-- B_of_three_online_ne but with one length too short -/
lemma B_of_three_online_ne_short {a b c : point} {L : line}
    (hlen: length a b < length a c) :
    a ≠ b → a ≠ c → b ≠ c → online a L → online b L → online c L →  B a b c ∨ B b a c := fun ab ac bc aL bL cL => by
  have := B_of_three_online_ne ab ac bc aL bL cL
  convert this; simp [not_B_of_short hlen]

/-- complement to same_length_of_ne_le -/
theorem same_length_B_of_ne_ge {a b c d : point} (a_ne_b : a ≠ b) (big : length a b < length c d) :
    ∃ (p : point), B a b p ∧ length a p = length c d := by
  have c_ne_d : c ≠ d := fun cd => by
    rw [cd, length_eq_zero_iff.mpr rfl] at big
    exact not_lt_of_ge (length_nonneg a b) big

  obtain ⟨q, hq⟩ := length_eq_B_of_ne_four a_ne_b.symm c_ne_d

  have a_ne_q : a ≠ q := fun aq => by
    rw [aq, length_eq_zero_iff.mpr rfl] at hq; rw [hq.2] at big
    exact not_lt_of_ge (length_nonneg a b) big

  obtain ⟨C, hC⟩ := circle_of_ne a_ne_q
  obtain ⟨p, hp⟩ := pt_oncircle_of_inside_ne a_ne_q.symm (inside_circle_of_center hC.1)

  obtain ⟨AB, hAB⟩ := line_of_pts a b
  have q_online_AB := online_3_of_B hq.1 hAB.2 hAB.1
  have p_online_AB := online_3_of_B hp.1 q_online_AB hAB.1

  have := (on_circle_iff_length_eq hC.1 hp.2).mpr hC.2
  rw [← this] at hq; rw [hq.2] at big

  have b_ne_p : b ≠ p := fun bp => by
    rw [←bp, bp] at hq; rw [bp] at big
    simp [lt_self_iff_false] at big

  have a_ne_p := (ne_12_of_B (B_symm hp.1)).symm

  refine' ⟨p, _, hq.2.symm⟩
  have B3 := B_of_three_online_ne_short big a_ne_b a_ne_p b_ne_p hAB.1 hAB.2 p_online_AB
  cases B3 with
  | inl B3 => exact B3
  | inr B3 => exfalso; exact (not_B324_of_B123_B124 (B_symm hq.1) hp.1) B3

/-- ## Euclid I.33
lines which join the ends of equal and parallel lines in the same directions are themselves equal and parallel
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI33.html -/
theorem para_len_parallelogram {a b c d : point} {L M N O P : line}
    (haL: online a L) (hbL: online b L)
    (hcM: online c M) (hdM: online d M)
    (haN: online a N) (hcN: online c N)
    (hbO: online b O) (hdO: online d O)
    (hbP: online b P) (hcP: online c P)
    (hdiff: c ≠ b)
    (hside: diffside a d P)
    (pLM: para L M)
    (hlen: length a b = length c d) :
    para N O := by
  have abc_bcd := alternate_eq_of_para haL hbL hbP hcP hcM hdM hside pLM
  obtain ⟨-, -, bca_cbd⟩ := sas (by perma) (by perm) (by perma)
  exact para_of_ang_eq hdiff haN hcN hcP hbP hbO hdO hside bca_cbd

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
    (pLM: para L M) (pKN: para K N) (pOP: para O P)
    (hlen: length b c = length f g)
    {S: line}
    (hcS: online c S) (heS: online e S)
    (hside: diffside b h S)
    (h_b_ne_c: b ≠ c) :
    area a b c + area a d c = area e f g + area e h g := by
  obtain ⟨ Q, hbQ, heQ ⟩ := line_of_pts b e
  obtain ⟨ R, hcR, hhR ⟩ := line_of_pts c h
  have ec : e ≠ c := by apply neq_of_para heL hcM pLM
  have ehgf : paragram e h g f L P M O := by splitAll <;> perma only [para]

  have : length b c = length e h := by linperm [(len_ang_area_eq_of_parallelogram ehgf).1]
  have' pQR := para_len_parallelogram hbM hcM heL hhL hbQ heQ hcR hhR hcS heS ec hside (para_symm pLM) this

  have eq1 := parallelarea haL hdL hbM hcM heL hhL haK hbK hdN hcN hbQ heQ hcR hhR pLM pKN pQR
  have eq2 := parallelarea hbM hcM heL hhL hfM hgM hbQ heQ hcR hhR heO hfO hhP hgP (para_symm pLM) pQR pOP

  have abcd : paragram a b c d K M N L := by splitAll <;> perma only [para]
  have hgfe : paragram h g f e P M O L := by splitAll <;> perma only [para]

  have: area a b c = area a c d := by linperm [(area_of_parallelogram abcd).1]
  have: area f g h = area e f h := by linperm [(area_of_parallelogram hgfe).1]
  have: 2 * area a b c = area f g h + area e f h := by linperm [(area_of_parallelogram abcd).2]
  linperm [(area_of_parallelogram hgfe).2]


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
  have bcda: paragram b c d a M N L K:= by splitAll <;> perma only [para]
  have fghe: paragram f g h e M P L O:= by splitAll <;> perma only [para]
  have h_fg_eq_eh := (len_ang_area_eq_of_parallelogram fghe).1

  -- trivial case: b = c
  by_cases h_b_ne_c: b = c
  . have h_f_eq_g := (same_len_pts_coincide_iff hlen).mp h_b_ne_c
    have h_h_eq_e := (same_len_pts_coincide_iff h_fg_eq_eh).mp h_f_eq_g
    have h_d_eq_a := (same_len_pts_coincide_iff (len_ang_area_eq_of_parallelogram bcda).1).mp h_b_ne_c
    conv in (occs := *) area _ _ _ => all_goals rw [area_of_eq _ _ _ (by tauto)]

  . rw [(Ne.def b c).symm] at h_b_ne_c
    have h_h_ne_e : h ≠ e := fun he =>
      h_b_ne_c ((same_len_pts_coincide_iff hlen).mpr ((same_len_pts_coincide_iff h_fg_eq_eh).mpr he))

    obtain ⟨ S, hS ⟩ := line_of_pts c e
    obtain ⟨ Q, hQ ⟩ := line_of_pts b e
    obtain ⟨ R, hR ⟩ := line_of_pts c h

    have hside := diffside_of_trapezoid hhL heL hQ.2 hQ.1 hbM hcM hS.2 hS.1 parLM ⟨ h_h_ne_e, h_b_ne_c ⟩

    cases hside with
    | inl hside =>
      exact eq_of_parallelogram_of_eq_basis_of_diffside haL hdL heL hhL hbM hcM hfM hgM haK hbK hdN hcN heO hfO hhP hgP parLM parKN parOP hlen hS.1 hS.2 (diffside_symm hside) h_b_ne_c

    | inr hside =>
      -- invert parallelogram
      rw [length_symm b c] at hlen
      rw [← eq_of_parallelogram_of_eq_basis_of_diffside hdL haL heL hhL hcM hbM hfM hgM hdN hcN haK hbK heO hfO hhP hgP parLM (para_symm parKN) parOP hlen hQ.1 hQ.2 (diffside_symm hside) h_b_ne_c.symm]
      perm [(area_of_parallelogram bcda).1]; rw [this]
      perm [(area_of_parallelogram bcda).2]; rw [this]

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
    area a b c = area d e f := by

  -- trivial case: b = c
  by_cases h_b_ne_c: b = c
  · have h_e_ne_f: e = f := (same_len_pts_coincide_iff hlen).mp h_b_ne_c
    rw [area_of_eq a b c (by tauto), area_of_eq d e f (by tauto)]

  have h_e_ne_f : e ≠ f := fun ef => h_b_ne_c ((same_len_pts_coincide_iff hlen).mpr ef)

  -- line through a c abd d e
  obtain ⟨ K, haK, hcK ⟩ := line_of_pts a c
  obtain ⟨ N, hdN, heN ⟩ := line_of_pts d e

  -- construct parallel projection of b through a c
  have h_a_nonline_L := offline_of_para haM (para_symm pLM)
  have := not_online_of_triangle haK hcK hcL hbL h_a_nonline_L (fun cb => h_b_ne_c cb.symm)
  obtain ⟨ g, O, hgM, hgO, hbO, pKO ⟩ := parallel_projection hbL pLM (not_para_of_online_online hcK hcL) this

  -- construct parallel projection of f through d e
  have h_d_nonline_L := offline_of_para hdM (para_symm pLM)
  have := not_online_of_triangle hdN heN heL hfL h_d_nonline_L h_e_ne_f
  obtain ⟨ h, P, hhM, hhP, hfP, pNP ⟩ := parallel_projection hfL pLM (not_para_of_online_online heN heL) this

  perm [eq_of_parallelogram_of_eq_basis hgM haM hdM hhM hbL hcL heL hfL hgO hbO haK hcK hdN heN hhP hfP (by perma) (by perma) pNP hlen]

  have bcag: paragram b c a g L K M O:= by splitAll <;> perma only [para]
  have fedh: paragram f e d h L N M P:= by splitAll <;> perma only [para]
  have: area b c g + area a c g = 2 * area a b c := by perma [(area_of_parallelogram bcag).2]
  have: area d e f = area d f h := by linperm [(area_of_parallelogram fedh).1]
  linarith

/-- ## Euclid I.38
triangles which are on equal bases and in the same parallels equal one another (version where the vertex is the same for both triangles)
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI38.html -/
theorem eq_area_of_eq_base_samevertex (a : point) {b c e f : point} {L : line}
    (hbL: online b L)
    (hcL: online c L)
    (heL: online e L)
    (hfL: online f L)
    (hlen: length b c = length e f) :
    area a b c = area a e f := by
  -- trivial case: b = c
  by_cases h_b_ne_c : b = c
  · have h_e_ne_f: e = f := (same_len_pts_coincide_iff hlen).mp h_b_ne_c
    rw [area_of_eq a b c (by tauto), area_of_eq a e f (by tauto)]

  have h_e_ne_f : e ≠ f := fun ef => h_b_ne_c ((same_len_pts_coincide_iff hlen).mpr ef)

  -- trivial case online a L
  by_cases h_a_nonline_L : online a L
  · perm [(area_zero_iff_online h_b_ne_c hbL hcL).mpr h_a_nonline_L]; rw [this]
    perm [(area_zero_iff_online h_e_ne_f heL hfL).mpr h_a_nonline_L]; rw [this]

  obtain ⟨ _, hM ⟩ := parallel_of_line_pt h_a_nonline_L
  exact eq_area_of_eq_base hM.1 hbL hcL hM.1 heL hfL hM.2 hlen

/-- ## Euclid I.37
triangles which are on the same base and in the same parallels equal one another (a special case of I.38)
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI37.html -/
theorem para_implies_eq_area_of_same_base {a b c d : point} {L M : line}
    (haM: online a M) (hdM: online d M)
    (hbL: online b L) (hcL: online c L)
    (pLM: para L M) :
    area a b c = area d b c := by
  exact eq_area_of_eq_base haM hbL hcL hdM hbL hcL pLM rfl

/-- area of a triangle cannot equal the area of its subtriangle -/
lemma tri_sum_contra {b c d e: point} {O : line}
    (hbO: online b O) (hdO: online d O) (heO: online e O)
    (hncO: ¬ online c O)
    (bd: b ≠ d)
    (de: d ≠ e)
    (eb: e ≠ b)
    (hBbed: B b e d)
    (harea: area b c d = area b c e) :
    False := by
  apply hncO; apply (area_zero_iff_online de hdO heO).mp
  linperm [(area_add_iff_B eb.symm de.symm bd.symm hbO heO hdO hncO).mp hBbed]

  /-- ## Euclid I.39
  equal triangles which are on the same base and on the same side are also in the same parallels
  https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI39.html -/
  theorem eq_area_of_same_base_implies_para {a b c d : point} {L M O : line}
    (hbL: online b L) (hcL: online c L) (hnaL: ¬ online a L)
    (haM: online a M) (hdM: online d M)
    (hbO: online b O) (hdO: online d O) (hncO: ¬ online c O)
    (ad: a ≠ d)
    (bd: b ≠ d)
    (ssadL: sameside a d L)
    (harea: area a b c = area d b c) :
    para L M := by
  obtain ⟨N, haN, pNL⟩ := para_of_offline hnaL

  -- show that N and O intersect
  have npNO: ¬ para N O := fun pNO => by
    have LO_or_pLO := para_trans (para_symm pNL) pNO
    cases LO_or_pLO with
    | inl LO => rw [← LO] at hncO; exact hncO hcL
    | inr pLO => exact neq_of_para hbL hbO pLO rfl

  -- contruct e as intersection of N and O
  rcases pt_of_line_line npNO with ⟨e, heN, heO⟩

  have harea2 := eq_area_of_eq_base haN hbL hcL heN hbL hcL pNL rfl
  rw [harea] at harea2

  have be := neq_of_para hbL heN pNL
  by_cases de: d = e
  -- case d = e
  rw [← de] at heN; rwa [line_unique_of_pts ad haM hdM haN heN]

  -- case d != e (cannot actually occur)
  rw [← Ne.def d e] at de; exfalso

  cases B_of_three_online_ne be bd de.symm hbO heO hdO with
  -- case B b e d
  | inl hBbed =>
    exact tri_sum_contra hbO hdO heO hncO bd de be.symm hBbed (by perma at harea2)

  | inr hB =>
    cases hB with
  -- case B e b d
    | inl hBebd =>
    have ssaeL := sameside_of_para_online haN heN (para_symm pNL)
    have ssedL := sameside_symm (sameside_trans ssadL ssaeL)
    have dsedL:= not_sameside13_of_B123_online2 hBebd hbL
    exact dsedL ssedL

  -- case B b d e
    | inr hBbde =>
    exact tri_sum_contra hbO heO hdO hncO be de.symm bd.symm hBbde (by perma at harea2)
