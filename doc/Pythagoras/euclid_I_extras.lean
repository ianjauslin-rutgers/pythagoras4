open incidence_geometry
variable [i: incidence_geometry]

/-- find second point on line -/

lemma pt_of_line_ne_pt {a : point} {L : line} (haL: online a L) :
    ∃ b : point, (b ≠ a) ∧ (online b L) 

/-- intersection of non_parallel lines -/
lemma pt_of_line_line {L M : line} (hp: ¬ para L M) :
    ∃ a:point, (online a L)∧(online a M) 

/-- parallel lines don't intersect -/
lemma neq_of_para {a b : point} {L M : line}
    (haL: online a L)
    (hbM: online b M)
    (hpar: para L M) :
    a ≠ b 

/-- ## Euclid I.30
parallel is (almost) transitive (almost because parallel means not equal) -/
theorem para_trans {L M N : line}
    (pLM: para L M)
    (pLN: para L N) :
    M=N ∨ (para M N) 

/-- reorder areas -/
lemma area_invariant_132 {a b c : point} :
    area a b c = area a c b 

lemma area_invariant_213 {a b c : point} :
    area a b c = area b a c 

lemma area_invariant_231 {a b c : point} :
    area a b c = area b c a 

lemma area_invariant_312 {a b c : point} :
    area a b c = area c a b 

lemma area_invariant_321 {a b c : point} :
    area a b c = area c b a 

/-- degenerate area: more general statement -/
lemma area_of_eq (a b c : point)
    (h: a=b ∨ a=c ∨ b=c) :
    area a b c =0 

/-- equivalent areas of paralellogram -/
lemma area_of_parallelogram {a b c d : point} {L M N O : line}
    (haL: online a L) (hbL: online b L)
    (hbM: online b M) (hcM: online c M)
    (hcN: online c N) (hdN: online d N)
    (hdO: online d O) (haO: online a O)
    (parLN: para L N)
    (parMO: para M O) :
    area a b c + area a d c = 2*(area a b c)
    ∧ area b a d + area b c d = 2*(area a b c) 

/-- non-degeneracy of triangle -/
lemma not_online_of_triangle {a b c : point} {L M : line}
    (haL: online a L)
    (hbL: online b L)
    (hbM: online b M)
    (hcM: online c M)
    (hn: ¬ online a M)
    (hdeg: b ≠ c) :
    ¬ online c L 

/--parallel line through point -/
lemma parallel_of_line_pt {a : point} {L : line}
    (haL: ¬ online a L) :
    ∃ M : line, (online a M) ∧ (para L M) 

/-- parallel projection of point -/
lemma parallel_projection {a : point}{L M N : line}
    (haM: online a M)
    (hpar: para M N)
    (h_L_npara_M: ¬ para L M)
    (haL: ¬ online a L) :
    ∃ b : point, ∃ O : line, (online b N) ∧ (online b O) ∧ (online a O) ∧ (para L O) 

/-- intersecting lines cannot be parallel -/
lemma not_para_of_online_online {a : point} {L M : line} :
    (online a L) → (online a M) → ¬ para L M 

/-- diagonals of a trapezoid imply diffside -/
theorem diffside_of_trapezoid {a b c d : point} {L M N : line}
    (haL: online a L) (hbL: online b L)
    (hbM: online b M) (hcM: online c M)
    (hcN: online c N) (hdN: online d N)
    {D : line}
    (hbD: online b D) (hdD: online d D)
    (parLN: para L N)
    (h_nondeg: a ≠ b ∧ c ≠ d) :
    diffside a c D ∨ diffside a d M 

/-- cannot have B a b c if lengths don't match up -/
lemma not_B_of_short {a b c : point}
    (hlen: length a b < length a c) :
    ¬ B a c b 

/-- B_of_three_online_ne but with one length too short -/
lemma B_of_three_online_ne_short {a b c : point} {L : line}
    (hlen: length a b < length a c) :
    a ≠ b → a ≠ c → b ≠ c → online a L → online b L → online c L →  B a b c ∨ B b a c 

/-- complement to same_length_of_ne_le -/
theorem same_length_B_of_ne_ge {a b c d : point} (a_ne_b : a ≠ b) (big : length a b < length c d) :
    ∃ (p : point), B a b p ∧ length a p = length c d 

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
    para O M 

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
    area a b c + area a d c = area e f g + area e h g 

theorem eq_of_parallelogram_of_eq_basis {a b c d e f g h: point} {L M K N O P: line}
    (haL: online a L) (hdL: online d L) (heL: online e L) (hhL: online h L)
    (hbM: online b M) (hcM: online c M) (hfM: online f M) (hgM: online g M)
    (haK: online a K) (hbK: online b K)
    (hdN: online d N) (hcN: online c N)
    (heO: online e O) (hfO: online f O)
    (hhP: online h P) (hgP: online g P)
    (parLM: para L M) (parKN: para K N) (parOP: para O P)
    (hlen: length b c = length f g) :
    area a b c + area a d c = area e f g + area e h g 

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
    area a b c=area d e f 

/-- ## Euclid I.38
triangles which are on equal bases and in the same parallels equal one another (version where the vertex is the same for both triangles)
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI38.html -/
theorem eq_area_of_eq_base_samevertex (a : point) {b c e f : point} {L : line}
    (hbL: online b L)
    (hcL: online c L)
    (heL: online e L)
    (hfL: online f L)
    (hlen: length b c = length e f) :
    area a b c=area a e f 

/-- ## Euclid I.37
triangles which are on the same base and in the same parallels equal one another (a special case of I.38)
https://mathcs.clarku.edu/~djoyce/java/elements/bookI/propI37.html -/
theorem para_implies_eq_area_of_same_base {a b c d : point} {L M : line}
    (haM: online a M)
    (hbL: online b L)
    (hcL: online c L)
    (hdM: online d M)
    (pLM: para L M) :
    area a b c = area d b c 

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
    false 


