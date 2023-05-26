import SyntheticEuclid4
import Pythagoras.proportion
import Mathlib.Tactic.SwapVar

open incidence_geometry
variable [i: incidence_geometry]

/-- a wrapper around proportion_iff utilizing length nonnegativity-/
lemma proportion_len_iff (a b c d e f g h : point) (cd : length c d ≠ 0) (gh: length g h ≠ 0) :
  (length a b) / (length c d) = (length e f) / (length g h) ↔ proportion (length a b) (length c d) (length e f) (length g h) :=
   proportion_iff (length_nonneg _ _) (length_nonneg _ _) (length_nonneg _ _) (length_nonneg _ _) cd gh

/-- given two lengths, one is trivial iff the other is -/
lemma same_len_pts_coincide_iff {a b c d : point} (hlen: length a b = length c d) : a = b ↔ c = d := by
    rw [← @length_eq_zero_iff i a b, ← @length_eq_zero_iff i c d, hlen]

/-- find second point on line -/
lemma pt_of_line_ne_pt (a : point) (L : line) :
    ∃ b : point, (b ≠ a) ∧ (online b L) := by
  obtain ⟨ b, c, Hbc ⟩ := online_ne_of_line L
  by_cases b = a
  · simp_rw [h] at Hbc; exact ⟨c, Hbc.1.symm, Hbc.2.2 ⟩
  · exact ⟨ b, h, Hbc.2.1 ⟩

/-- intersection of non_parallel lines -/
lemma pt_of_line_line {L M : line} (hp: ¬ para L M) :
    ∃a : point, (online a L) ∧ (online a M) := by
  simp_rw [para, not_forall, not_or, not_not] at hp; exact hp

/-- parallel lines don't intersect -/
lemma neq_of_para {a b : point} {L M : line}
    (aL: online a L)
    (bM: online b M)
    (pLM: para L M) :
    a ≠ b := fun ab => by
  have := offline_of_para aL pLM; rw [ab] at this; exact this bM

/-- ## Euclid I.30
parallel is (almost) transitive (almost because parallel means not equal) -/
theorem para_trans {L M N : line}
    (pLM: para L M)
    (pLN: para L N) :
    M = N ∨ (para M N) := by
  by_cases MN : M = N
  · tauto

  -- assume that M, N intersect at c; drop a line from it perpendicular to L
  by_contra npMN; simp [not_or] at npMN
  rcases pt_of_line_line npMN.2 with ⟨c, cM, cN⟩
  have cL := offline_of_para cN (para_symm pLN)
  rcases perpendicular_of_not_online cL with ⟨-, -, d, -, -, -, dL, -, -⟩
  obtain ⟨O, cO, dO⟩ := line_of_pts c d
  have cd : c ≠ d := neq_of_para cM dL (para_symm pLM)
  have LO : L ≠ O := fun LO => cL (by rwa [← LO] at cO)

  -- draw a circle α with center c and radius d; find its intersections with M,N
  obtain ⟨α, Hα⟩ := circle_of_ne cd
  have cα := inside_circle_of_center Hα.1
  have αM := line_circle_inter_of_inside_online cM cα
  have αN := line_circle_inter_of_inside_online cN cα
  obtain ⟨a, a', aa', aM, a'M, aα⟩ := pts_of_line_circle_inter αM
  obtain ⟨b, b', bb', bN, b'N, bα⟩ := pts_of_line_circle_inter αN
  have Baca' := B_of_line_circle_inter aa' cM aM a'M aα.1 aα.2 cα
  have Bbcb' := B_of_line_circle_inter bb' cN bN b'N bα.1 bα.2 cα
  have ac := ne_12_of_B Baca'
  have bc := ne_12_of_B Bbcb'
  have b'c := (ne_23_of_B Bbcb').symm
  have aO: ¬ online a O := fun aO => neq_of_para dL dO (by rwa [← line_unique_of_pts ac aO cO aM cM] at pLM) rfl
  have bO : ¬ online b O := fun bO => neq_of_para dL dO (by rwa [← line_unique_of_pts bc bO cO bN cN] at pLN) rfl
  have b'O : ¬ online b' O := fun hb'O => neq_of_para dL dO (by rwa [← line_unique_of_pts b'c hb'O cO b'N cN] at pLN) rfl
  have aN: ¬ online a N := fun aN => MN (line_unique_of_pts ac aM cM aN cN)
  have bM: ¬ online b M := fun bM => MN (line_unique_of_pts bc bM cM bN cN)
  have b'M: ¬ online b' M := fun hb'M => MN (line_unique_of_pts b'c hb'M cM b'N cN)
  have NO : N ≠ O := fun NO => bO (by rwa [NO] at bN)
  have MO : M ≠ O := fun MO => aO (by rwa [MO] at aM)

  -- choose b so that a, b that lie on the same side of O by symmetry
  by_cases ssbaO: sameside b a O
  have ssabO := sameside_symm ssbaO
  swap
  have nsbb'O := not_sameside13_of_B123_online2 Bbcb' cO
  have ssabO := sameside_of_diffside_diffside ⟨bO, aO, ssbaO⟩ ⟨bO, b'O, nsbb'O⟩
  swap_var b ↔ b'; swap_var bN ↔ b'N; swap_var bM ↔ b'M; swap_var bO ↔ b'O; swap_var bc ↔ b'c
  all_goals
    have ss1 := sameside_of_sameside_not_sameside cd cO cN cM dO bN aM aN (sameside_symm ssabO)
    have ss2 := not_sameside_of_sameside_sameside cO cM cN dO aM bN ssabO
    have ss: sameside d a N ∨ sameside d b M := by tauto

    -- choose e on L so that it lies on the opposite side w.r.t. to O than a, b
    obtain ⟨e0, e0d, -⟩ := pt_of_line_ne_pt d L
    obtain ⟨β, hβ⟩ := circle_of_ne e0d.symm
    have dβ := inside_circle_of_center hβ.1
    have βL := line_circle_inter_of_inside_online dL dβ
    obtain ⟨e, e', ee', eL, e'L, eβ⟩ := pts_of_line_circle_inter βL
    have Bede' := B_of_line_circle_inter ee' dL eL e'L eβ.1 eβ.2 dβ
    have ed := ne_12_of_B Bede'
    have e'd := (ne_23_of_B Bede').symm
    have hneO : ¬ online e O := fun eO => LO (line_unique_of_pts ed eL dL eO dO)
    have hne'O : ¬ online e' O := fun he'O => LO (line_unique_of_pts e'd e'L dL he'O dO)
    by_cases nsaeO: sameside a e' O
    have nse'eO := not_sameside13_of_B123_online2 (B_symm Bede') dO
    have dsaeO := diffside_of_sameside_diffside (sameside_symm nsaeO) ⟨hne'O, hneO, nse'eO⟩
    swap; swap_var e ↔ e'; swap_var eL ↔ e'L; swap_var ed ↔ e'd; swap_var hneO ↔ hne'O
    have dsaeO: diffside a e O := ⟨aO, hneO, nsaeO⟩
    all_goals
      have dsbeO := diffside_of_sameside_diffside ssabO dsaeO
      have acd := alternate_eq_of_para aM cM cO dO dL eL dsaeO (para_symm pLM)
      have bcd := alternate_eq_of_para bN cN cO dO dL eL dsbeO (para_symm pLN)

      -- argue about angles given by parallel assumptions in two symmetric cases
      cases ss with
      | inl ssdaN =>
        have sum := (angle_add_iff_sameside bc.symm cd cN bN cO dO aO aN NO).2 ⟨sameside_symm ssabO, ssdaN⟩
        rw [acd, bcd, self_eq_add_left] at sum
        exact aN ((angle_zero_iff_online bc.symm ac.symm cN bN).2 sum).1
      | inr ssdbM =>
        have sum := (angle_add_iff_sameside ac.symm cd cM aM cO dO bO bM MO).2 ⟨ssabO, ssdbM⟩
        rw [acd, bcd, self_eq_add_left] at sum;
        exact bM ((angle_zero_iff_online ac.symm bc.symm cM aM).2 sum).1

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
  obtain ⟨ aL, bL, bM, cM, cN, dN, dO, aO, pLN, pMO⟩ := id abcd
  have bcda : paragram b c d a M N O L := by splitAll <;> perma only [para]

  constructor
  · linperm [(len_ang_area_eq_of_parallelogram bcda).2.2]
  · linperm [(len_ang_area_eq_of_parallelogram abcd).2.2, triarea cN dN bL aL (by perma)]

/-- non-degeneracy of triangle -/
lemma not_online_of_triangle {a b c : point} {L M : line}
    (aL: online a L)
    (bL: online b L)
    (bM: online b M)
    (cM: online c M)
    (hn: ¬ online a M)
    (bc: b ≠ c) :
    ¬ online c L := fun cL => by rw [line_unique_of_pts bc bL cL bM cM] at aL; exact hn aL

/--parallel line through point -/
lemma parallel_of_line_pt {a : point} {L : line}
    (aL: ¬ online a L) :
    ∃ M : line, (online a M) ∧ (para L M) := by
  dsimp [para]; exact para_of_offline aL

/-- parallel projection of point -/
lemma parallel_projection {a : point}{L M N : line}
    (aM: online a M)
    (pMN: para M N)
    (pLM: ¬ para L M)
    (aL: ¬ online a L) :
    ∃ b : point, ∃ O : line, (online b N) ∧ (online b O) ∧ (online a O) ∧ (para L O) := by
  -- intersections with L
  have pLN : ¬ para L N := fun pLN => by
    cases para_trans (para_symm pMN) (para_symm pLN) with
    | inl h => rw [h] at aM; exact aL aM
    | inr h => exact pLM (para_symm h)
  obtain ⟨ d, dL, dN ⟩ := pt_of_line_line pLN

  -- construct parallel to L through a
  obtain ⟨ O, aO, pLO ⟩ := para_of_offline aL

  -- construct intersection of O and M
  have pON : ¬ para O N := fun pON => by
    have pNO := para_trans pON (para_symm pLO)
    cases pNO with
    | inl pNO => rw [pNO] at pMN; exact pLM (para_symm pMN)
    | inr pNO => exact (offline_of_para dL (para_symm pNO)) dN
  obtain ⟨ b, bO, bN ⟩ := pt_of_line_line pON
  exact ⟨ b, O, bN, bO, aO, pLO ⟩

/-- intersecting lines cannot be parallel -/
lemma not_para_of_online_online {a : point} {L M : line} :
    (online a L) → (online a M) → ¬ para L M := fun hL hM => by
  simp_rw [para, not_forall, not_or, not_not]; exact ⟨ a, hL, hM ⟩

/-- diagonals of a trapezoid imply diffside -/
theorem diffside_of_trapezoid {a b c d : point} {L M N O: line}
    (aL: online a L) (bL: online b L)
    (bM: online b M) (cM: online c M)
    (cN: online c N) (dN: online d N)
    (bO: online b O) (dO: online d O)
    (pLN: para L N)
    (h_nondeg: a ≠ b ∧ c ≠ d) :
    diffside a c O ∨ diffside a d M := by
  by_cases h_ss : sameside a c O
  · right
    refine' ⟨ not_online_of_triangle cM bM bL aL (offline_of_para cN (para_symm pLN)) h_nondeg.1.symm, _ ⟩
    refine' ⟨ not_online_of_triangle bM cM cN dN (offline_of_para bL pLN) h_nondeg.2, _ ⟩
    have := sameside_of_para_online cN dN (para_symm pLN)
    exact not_sameside_of_sameside_sameside bL bM bO aL cM dO this h_ss

  · left
    refine' ⟨ not_online_of_triangle dO bO bL aL (offline_of_para dN (para_symm pLN)) h_nondeg.1.symm, _ ⟩
    refine' ⟨ not_online_of_triangle bO dO dN cN (offline_of_para bL pLN) h_nondeg.2.symm, h_ss ⟩

/-- cannot have B a b c if lengths don't match up -/
lemma not_B_of_short {a b c : point}
    (hlen: length a b < length a c) :
    ¬ B a c b := fun hBacb => by
  rw [(length_sum_of_B hBacb).symm] at hlen; linarith [length_nonneg c b]

/-- B_of_three_online_ne but with one length too short -/
lemma B_of_three_online_ne_short {a b c : point} {L : line}
    (hlen: length a b < length a c) :
    a ≠ b → a ≠ c → b ≠ c → online a L → online b L → online c L →  B a b c ∨ B b a c := fun ab ac bc aL bL cL => by
  have := B_of_three_online_ne ab ac bc aL bL cL; convert this; simp [not_B_of_short hlen]

/-- complement to same_length_of_ne_le -/
theorem same_length_B_of_ne_ge {a b c d : point} (ab : a ≠ b) (big : length a b < length c d) :
    ∃ (p : point), B a b p ∧ length a p = length c d := by
  have cd : c ≠ d := fun cd => by
    rw [cd, length_eq_zero_iff.mpr rfl] at big;
    exact not_lt_of_ge (length_nonneg a b) big
  obtain ⟨q, Hq⟩ := length_eq_B_of_ne_four ab.symm cd
  have aq : a ≠ q := fun aq => by
    rw [aq, length_eq_zero_iff.mpr rfl] at Hq; rw [Hq.2] at big
    exact not_lt_of_ge (length_nonneg a b) big
  obtain ⟨C, hC⟩ := circle_of_ne aq
  obtain ⟨p, Hp⟩ := pt_oncircle_of_inside_ne aq.symm (inside_circle_of_center hC.1)
  obtain ⟨AB, aAB, bAB⟩ := line_of_pts a b
  have qAB := online_3_of_B Hq.1 bAB aAB
  have pAB := online_3_of_B Hp.1 qAB aAB
  have := (on_circle_iff_length_eq hC.1 Hp.2).mpr hC.2
  rw [← this] at Hq; rw [Hq.2] at big
  have bp : b ≠ p := fun bp => by
    rw [←bp, bp] at Hq; rw [bp] at big
    simp [lt_self_iff_false] at big
  have ap := (ne_12_of_B (B_symm Hp.1)).symm
  refine' ⟨p, _, Hq.2.symm⟩

  have B3 := B_of_three_online_ne_short big ab ap bp aAB bAB pAB
  cases B3 with
  | inl B3 => exact B3
  | inr B3 => exfalso; exact (not_B324_of_B123_B124 (B_symm Hq.1) Hp.1) B3

/-- ## Euclid I.33
lines which join the ends of equal and parallel lines in the same directions are themselves equal and parallel
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI33.html -/
theorem para_len_parallelogram {a b c d : point} {L M N O P : line}
    (aL: online a L) (bL: online b L)
    (cM: online c M) (dM: online d M)
    (aN: online a N) (cN: online c N)
    (bO: online b O) (dO: online d O)
    (bP: online b P) (cP: online c P)
    (cb: c ≠ b)
    (aPd: diffside a d P)
    (pLM: para L M)
    (hlen: length a b = length c d) :
    para N O := by
  have abc_bcd := alternate_eq_of_para aL bL bP cP cM dM aPd pLM
  obtain ⟨-, -, bca_cbd⟩ := sas (by perma) (by perm) (by perma)
  exact para_of_ang_eq cb aN cN cP bP bO dO aPd bca_cbd

/-- ## Euclid I.36
parallelograms which are on equal bases and in the same parallels equal one another
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI36.html -/
theorem eq_of_parallelogram_of_eq_basis_of_diffside {a b c d e f g h: point} {L M K N O P: line}
    (aL: online a L) (dL: online d L) (eL: online e L) (hL: online h L)
    (bM: online b M) (cM: online c M) (fM: online f M) (gM: online g M)
    (aK: online a K) (bK: online b K)
    (dN: online d N) (cN: online c N)
    (eO: online e O) (fO: online f O)
    (hP: online h P) (gP: online g P)
    (pLM: para L M) (pKN: para K N) (pOP: para O P)
    (hlen: length b c = length f g)
    {S: line}
    (cS: online c S) (eS: online e S)
    (aPd: diffside b h S)
    (bc: b ≠ c) :
    area a b c + area a d c = area e f g + area e h g := by
  obtain ⟨ Q, bQ, eQ ⟩ := line_of_pts b e
  obtain ⟨ R, cR, hR ⟩ := line_of_pts c h
  have ec : e ≠ c := neq_of_para eL cM pLM
  have ehgf : paragram e h g f L P M O := by splitAll <;> perma only [para]
  have : length b c = length e h := by linperm [(len_ang_area_eq_of_parallelogram ehgf).1]
  have' pQR := para_len_parallelogram bM cM eL hL bQ eQ cR hR cS eS ec aPd (para_symm pLM) this
  have eq1 := parallelarea aL dL bM cM eL hL aK bK dN cN bQ eQ cR hR pLM pKN pQR
  have eq2 := parallelarea bM cM eL hL fM gM bQ eQ cR hR eO fO hP gP (para_symm pLM) pQR pOP
  have abcd : paragram a b c d K M N L := by splitAll <;> perma only [para]
  have hgfe : paragram h g f e P M O L := by splitAll <;> perma only [para]
  have: area a b c = area a c d := by linperm [(area_of_parallelogram abcd).1]
  have: area f g h = area e f h := by linperm [(area_of_parallelogram hgfe).1]
  have: 2 * area a b c = area f g h + area e f h := by linperm [(area_of_parallelogram abcd).2]
  linperm [(area_of_parallelogram hgfe).2]


theorem eq_of_parallelogram_of_eq_basis {a b c d e f g h: point} {L M K N O P: line}
    (aL: online a L) (dL: online d L) (eL: online e L) (hL: online h L)
    (bM: online b M) (cM: online c M) (fM: online f M) (gM: online g M)
    (aK: online a K) (bK: online b K)
    (dN: online d N) (cN: online c N)
    (eO: online e O) (fO: online f O)
    (hP: online h P) (gP: online g P)
    (pLM: para L M) (pKN: para K N) (pOP: para O P)
    (hlen: length b c = length f g) :
    area a b c + area a d c = area e f g + area e h g := by
  have bcda: paragram b c d a M N L K := by splitAll <;> perma only [para]
  have fghe: paragram f g h e M P L O := by splitAll <;> perma only [para]
  have fg_he := (len_ang_area_eq_of_parallelogram fghe).1

  -- trivial case: b = c
  by_cases bc: b = c
  · have hg := (same_len_pts_coincide_iff hlen).mp bc
    have he := (same_len_pts_coincide_iff fg_he).mp hg
    have da := (same_len_pts_coincide_iff (len_ang_area_eq_of_parallelogram bcda).1).mp bc
    conv in (occs := *) area _ _ _ => all_goals rw [area_of_eq _ _ _ (by tauto)]

  · rw [(Ne.def b c).symm] at bc
    have he : h ≠ e := ne_of_ne_len bc (hlen.trans fg_he)
    obtain ⟨ S, cS, eS ⟩ := line_of_pts c e
    obtain ⟨ Q, bQ, eQ ⟩ := line_of_pts b e
    have aPd := diffside_of_trapezoid hL eL eQ bQ bM cM eS cS pLM ⟨ he, bc ⟩
    cases aPd with
    | inl aPd =>
      exact eq_of_parallelogram_of_eq_basis_of_diffside aL dL eL hL bM cM fM gM aK bK dN cN eO fO hP gP pLM pKN pOP hlen cS eS (diffside_symm aPd) bc
    | inr aPd =>
      -- invert parallelogram
      rw [← eq_of_parallelogram_of_eq_basis_of_diffside dL aL eL hL cM bM fM gM dN cN aK bK eO fO hP gP pLM (para_symm pKN) pOP (by perma) bQ eQ (diffside_symm aPd) bc.symm]
      perm [(area_of_parallelogram bcda).1]; rw [this]
      perm [(area_of_parallelogram bcda).2]; rw [this]

/-- ## Euclid I.38
triangles which are on equal bases and in the same parallels equal one another (version where the vertex is different for both triangles)
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI38.html -/
theorem eq_area_of_eq_base {a b c d e f : point} {L M : line}
    (aM: online a M)
    (bL: online b L)
    (cL: online c L)
    (dM: online d M)
    (eL: online e L)
    (fL: online f L)
    (pLM: para L M)
    (hlen: length b c = length e f) :
    area a b c = area d e f := by
  -- trivial case: b = c
  by_cases bc: b = c
  · have ef: e = f := (same_len_pts_coincide_iff hlen).mp bc
    rw [area_of_eq a b c (by tauto), area_of_eq d e f (by tauto)]

  have ef : e ≠ f := ne_of_ne_len bc hlen
  -- line through a c abd d e
  obtain ⟨ K, aK, cK ⟩ := line_of_pts a c
  obtain ⟨ N, dN, eN ⟩ := line_of_pts d e

  -- construct parallel projection of b through a c
  have aL := offline_of_para aM (para_symm pLM)
  have := not_online_of_triangle aK cK cL bL aL (fun cb => bc cb.symm)
  obtain ⟨ g, O, gM, hgO, bO, pKO ⟩ := parallel_projection bL pLM (not_para_of_online_online cK cL) this

  -- construct parallel projection of f through d e
  have dL := offline_of_para dM (para_symm pLM)
  have := not_online_of_triangle dN eN eL fL dL ef
  obtain ⟨ h, P, hhM, hP, hfP, pNP ⟩ := parallel_projection fL pLM (not_para_of_online_online eN eL) this

  perm [eq_of_parallelogram_of_eq_basis gM aM dM hhM bL cL eL fL hgO bO aK cK dN eN hP hfP (by perma) (by perma) pNP hlen]
  have bcag: paragram b c a g L K M O:= by splitAll <;> perma only [para]
  have fedh: paragram f e d h L N M P:= by splitAll <;> perma only [para]
  have: area b c g + area a c g = 2 * area a b c := by perma [(area_of_parallelogram bcag).2]
  have: area d e f = area d f h := by linperm [(area_of_parallelogram fedh).1]
  linarith

/-- ## Euclid I.38
triangles which are on equal bases and in the same parallels equal one another (version where the vertex is the same for both triangles)
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI38.html -/
theorem eq_area_of_eq_base_samevertex (a : point) {b c e f : point} {L : line}
    (bL: online b L)
    (cL: online c L)
    (eL: online e L)
    (fL: online f L)
    (hlen: length b c = length e f) :
    area a b c = area a e f := by
  -- trivial case: b = c
  by_cases bc : b = c
  · have ef: e = f := (same_len_pts_coincide_iff hlen).mp bc
    rw [area_of_eq a b c (by tauto), area_of_eq a e f (by tauto)]

  have ef : e ≠ f := ne_of_ne_len bc hlen
  -- trivial case online a L
  by_cases aL : online a L
  · perm [(area_zero_iff_online bc bL cL).mpr aL]; rw [this]
    linperm [(area_zero_iff_online ef eL fL).mpr aL]

  obtain ⟨ _, hM ⟩ := parallel_of_line_pt aL
  exact eq_area_of_eq_base hM.1 bL cL hM.1 eL fL hM.2 hlen

/-- ## Euclid I.37
triangles which are on the same base and in the same parallels equal one another (a special case of I.38)
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI37.html -/
theorem para_implies_eq_area_of_same_base {a b c d : point} {L M : line}
    (aM: online a M) (dM: online d M)
    (bL: online b L) (cL: online c L)
    (pLM: para L M) :
    area a b c = area d b c := by exact eq_area_of_eq_base aM bL cL dM bL cL pLM rfl

/-- area of a triangle cannot equal the area of its subtriangle -/
lemma tri_sum_contra {b c d e: point} {O : line}
    (bO: online b O) (dO: online d O) (eO: online e O)
    (cO: ¬ online c O)
    (bd: b ≠ d)
    (de: d ≠ e)
    (eb: e ≠ b)
    (Bbed: B b e d)
    (ar: area b c d = area b c e) :
    False := by
  apply cO; apply (area_zero_iff_online de dO eO).mp
  linperm [(area_add_iff_B eb.symm de.symm bd.symm bO eO dO cO).mp Bbed]

  /-- ## Euclid I.39
  equal triangles which are on the same base and on the same side are also in the same parallels
  https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI39.html -/
  theorem eq_area_of_same_base_implies_para {a b c d : point} {L M O : line}
    (bL: online b L) (cL: online c L) (aL: ¬ online a L)
    (aM: online a M) (dM: online d M)
    (bO: online b O) (dO: online d O) (cO: ¬ online c O)
    (ad: a ≠ d)
    (bd: b ≠ d)
    (ssadL: sameside a d L)
    (ar: area a b c = area d b c) :
    para L M := by
  obtain ⟨N, aN, pNL⟩ := para_of_offline aL

  -- show that N and O intersect
  have pNO: ¬ para N O := fun pNO => by
    have LO_or_pLO := para_trans (para_symm pNL) pNO
    cases LO_or_pLO with
    | inl LO => rw [← LO] at cO; exact cO cL
    | inr pLO => exact neq_of_para bL bO pLO rfl

  -- contruct e as intersection of N and O
  rcases pt_of_line_line pNO with ⟨e, eN, eO⟩
  have ar2 := eq_area_of_eq_base aN bL cL eN bL cL pNL rfl; rw [ar] at ar2
  have be := neq_of_para bL eN pNL
  by_cases de: d = e
  · rw [← de] at eN; rwa [line_unique_of_pts ad aM dM aN eN]
  · rw [← Ne.def d e] at de; exfalso
    cases B_of_three_online_ne be bd de.symm bO eO dO with
    | inl Bbed =>
      exact tri_sum_contra bO dO eO cO bd de be.symm Bbed (by perma at ar2)
    | inr HB =>
      cases HB with
      | inl Bebd =>
        have ssaeL := sameside_of_para_online aN eN (para_symm pNL)
        have ssedL := sameside_symm (sameside_trans ssadL ssaeL)
        have dsedL:= not_sameside13_of_B123_online2 Bebd bL
        exact dsedL ssedL
      | inr Bbde =>
        exact tri_sum_contra bO eO dO cO be de.symm bd.symm Bbde (by perma at ar2)
