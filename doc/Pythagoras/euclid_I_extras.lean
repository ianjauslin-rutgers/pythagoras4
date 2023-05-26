open incidence_geometry
variable [i: incidence_geometry]

/-- a wrapper around proportion_iff utilizing length nonnegativity-/
lemma proportion_len_iff (a b c d e f g h : point) (cd : length c d ≠ 0) (gh: length g h ≠ 0) :
  (length a b) / (length c d) = (length e f) / (length g h) ↔ proportion (length a b) (length c d) (length e f) (length g h) 

/-- given two lengths, one is trivial iff the other is -/
lemma same_len_pts_coincide_iff {a b c d : point} (hlen: length a b = length c d) : a = b ↔ c = d 

/-- find second point on line -/
lemma pt_of_line_ne_pt (a : point) (L : line) :
    ∃ b : point, (b ≠ a) ∧ (online b L) 

/-- intersection of non_parallel lines -/
lemma pt_of_line_line {L M : line} (hp: ¬ para L M) :
    ∃a : point, (online a L) ∧ (online a M) 

/-- parallel lines don't intersect -/
lemma neq_of_para {a b : point} {L M : line}
    (aL: online a L)
    (bM: online b M)
    (pLM: para L M) :
    a ≠ b 

/-- ## Euclid I.30
parallel is (almost) transitive (almost because parallel means not equal) -/
theorem para_trans {L M N : line}
    (pLM: para L M)
    (pLN: para L N) :
    M = N ∨ (para M N) 

/-- degenerate area: more general statement -/
lemma area_of_eq (a b c : point)
    (h: a=b ∨ a=c ∨ b=c) :
    area a b c = 0 

/-- equivalent areas of paralellogram -/
lemma area_of_parallelogram {a b c d : point} {L M N O : line}
    (abcd: paragram a b c d L M N O) :
    area a b c + area a d c = 2 * (area a b c)
    ∧ area b a d + area b c d = 2 * (area a b c) 

/-- non-degeneracy of triangle -/
lemma not_online_of_triangle {a b c : point} {L M : line}
    (aL: online a L)
    (bL: online b L)
    (bM: online b M)
    (cM: online c M)
    (hn: ¬ online a M)
    (bc: b ≠ c) :
    ¬ online c L 

/--parallel line through point -/
lemma parallel_of_line_pt {a : point} {L : line}
    (aL: ¬ online a L) :
    ∃ M : line, (online a M) ∧ (para L M) 

/-- parallel projection of point -/
lemma parallel_projection {a : point}{L M N : line}
    (aM: online a M)
    (pMN: para M N)
    (pLM: ¬ para L M)
    (aL: ¬ online a L) :
    ∃ b : point, ∃ O : line, (online b N) ∧ (online b O) ∧ (online a O) ∧ (para L O) 

/-- intersecting lines cannot be parallel -/
lemma not_para_of_online_online {a : point} {L M : line} :
    (online a L) → (online a M) → ¬ para L M 

/-- diagonals of a trapezoid imply diffside -/
theorem diffside_of_trapezoid {a b c d : point} {L M N O: line}
    (aL: online a L) (bL: online b L)
    (bM: online b M) (cM: online c M)
    (cN: online c N) (dN: online d N)
    (bO: online b O) (dO: online d O)
    (pLN: para L N)
    (h_nondeg: a ≠ b ∧ c ≠ d) :
    diffside a c O ∨ diffside a d M 

/-- cannot have B a b c if lengths don't match up -/
lemma not_B_of_short {a b c : point}
    (hlen: length a b < length a c) :
    ¬ B a c b 

/-- B_of_three_online_ne but with one length too short -/
lemma B_of_three_online_ne_short {a b c : point} {L : line}
    (hlen: length a b < length a c) :
    a ≠ b → a ≠ c → b ≠ c → online a L → online b L → online c L →  B a b c ∨ B b a c 

/-- complement to same_length_of_ne_le -/
theorem same_length_B_of_ne_ge {a b c d : point} (ab : a ≠ b) (big : length a b < length c d) :
    ∃ (p : point), B a b p ∧ length a p = length c d 

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
    para N O 

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
    area a b c + area a d c = area e f g + area e h g 

theorem eq_of_parallelogram_of_eq_basis {a b c d e f g h: point} {L M K N O P: line}
    (aL: online a L) (dL: online d L) (eL: online e L) (hL: online h L)
    (bM: online b M) (cM: online c M) (fM: online f M) (gM: online g M)
    (aK: online a K) (bK: online b K)
    (dN: online d N) (cN: online c N)
    (eO: online e O) (fO: online f O)
    (hP: online h P) (gP: online g P)
    (pLM: para L M) (pKN: para K N) (pOP: para O P)
    (hlen: length b c = length f g) :
    area a b c + area a d c = area e f g + area e h g 

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
    area a b c = area d e f 

/-- ## Euclid I.38
triangles which are on equal bases and in the same parallels equal one another (version where the vertex is the same for both triangles)
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI38.html -/
theorem eq_area_of_eq_base_samevertex (a : point) {b c e f : point} {L : line}
    (bL: online b L)
    (cL: online c L)
    (eL: online e L)
    (fL: online f L)
    (hlen: length b c = length e f) :
    area a b c = area a e f 

/-- ## Euclid I.37
triangles which are on the same base and in the same parallels equal one another (a special case of I.38)
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI37.html -/
theorem para_implies_eq_area_of_same_base {a b c d : point} {L M : line}
    (aM: online a M) (dM: online d M)
    (bL: online b L) (cL: online c L)
    (pLM: para L M) :
    area a b c = area d b c 

/-- area of a triangle cannot equal the area of its subtriangle -/
lemma tri_sum_contra {b c d e: point} {O : line}
    (bO: online b O) (dO: online d O) (eO: online e O)
    (cO: ¬ online c O)
    (bd: b ≠ d)
    (de: d ≠ e)
    (eb: e ≠ b)
    (Bbed: B b e d)
    (ar: area b c d = area b c e) :
    False 
