open incidence_geometry
variable [i: incidence_geometry]

/-- technical lemma that really shouldn't be here, but hey... -/

lemma mul_mul_lt (a b c : ℝ) (hc: 0 < c):
    a < b → a * c < b * c 

/-- technical lemma that really shouldn't be here, but hey... -/
lemma gt1_of_n1_n0 {n : ℕ}
    (h0: n ≠ 0) (h1: n ≠ 1) :
    n > 1 

lemma rescale_length {a b : point} {L : line} (n : ℕ)
    (aL: online a L)
    (bL: online b L) :
    ∃ (c : point), (online c L) ∧ (length a c = n * length a b) ∧ (n ≥ 2 ∧ a ≠ b → B a b c) 

/-- rescale base of triangle -/
-- workhorse: version for use in inductive case
lemma rescale_triangle_of_base_inductive (a : point) {b c : point} {L : line} {n : ℕ}
    (bL: online b L)
    (cL: online c L)
    (aL: ¬ online a L) :
    ∀ d : point, (online d L) → (length b d = n * length b c) → B b c d → area a b d = n * area a b c 

-- lemma with B b c d as a hypothesis
lemma rescale_triangle_of_base_B (a : point) {b c d : point} {L : line} {n : ℕ}
    (bL: online b L)
    (cL: online c L)
    (dL: online d L)
    (hlen: length b d = n * length b c)
    (Bbcd: B b c d)
    (aL: ¬ online a L) :
    area a b d = n * area a b c 

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
    area a b d = n * area a b c 

-- full version
lemma rescale_triangle_of_base (a : point) {b c d : point} {L : line} {n : ℕ}
    (bL: online b L)
    (cL: online c L)
    (dL: online d L)
    (hlen: length b d = n * length b c) :
    area a b d = n * area a b c 

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
    (length b c) > (length b f) → (area a b c) > (area a b f) 

-- case where they share a side and not B f b c
lemma lt_area_of_lt_base_sameedge_nBfbc (a : point) {b c f: point} {L: line}
    (bL: online b L)
    (cL: online c L)
    (fL: online f L)
    (bc: b ≠ c)
    (bf: b ≠ f)
    (aL: ¬ online a L)
    (hB: ¬ B f b c) :
    (length b c) > (length b f) → (area a b c) > (area a b f) 

-- case where they share a side
lemma lt_area_of_lt_base_sameedge (a : point) {b c f: point} {L: line}
    (bL: online b L)
    (cL: online c L)
    (fL: online f L)
    (bc: b ≠ c)
    (bf: b ≠ f)
    (aL: ¬ online a L) :
    (length b c) > (length b f) → (area a b c) > (area a b f) 

-- general case
lemma lt_area_of_lt_base {a b c d e f: point} {L M: line}
    (aM: online a M)
    (bL: online b L)
    (cL: online c L)
    (dM: online d M)
    (eL: online e L)
    (fL: online f L)
    (pLM: para L M) :
    (length b c) > (length e f) → (area a b c) > (area d e f) 

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
    proportion (length b c) (length e f) (area a b c) (area d e f) 

/-- version where the vertex is the same for both triangles -/
theorem proportion_area_of_proportion_base_samevertex (a : point) {b c e f: point} {L : line}
    (bL: online b L)
    (cL: online c L)
    (eL: online e L)
    (fL: online f L)
    (aL: ¬ online a L) :
    proportion (length b c) (length e f) (area a b c) (area a e f) 

/-- ## Euclid VI.2
a line cuts the sides of the triangle proportionally iff it is parallel to one of the sides of a triangle (version BD:AD = CE:AE)
 https://mathcs.clarku.edu/~djoyce/java/elements/bookVI/propVI2.html -/
theorem proportional_iff_para {a b c d e: point} {L M N: line}
    (dL: online d L) (eL: online e L)
    (bM: online b M) (cM: online c M)
    (aN: online a N) (dN: online d N)
    (eN: ¬ online e N)
    (Badb : B a d b) (Baec : B a e c) :
    proportion (length b d) (length a d) (length c e) (length a e) ↔ para L M 

/-- ## Euclid VI.2'
a line cuts the sides of the triangle proportionally iff it is parallel to one of the sides of a triangle (version AB:AD = AC:AE)
 https://mathcs.clarku.edu/~djoyce/java/elements/bookVI/propVI2.html -/
theorem proportional_iff_para' {a b c d e: point} {L M N: line}
    (dL: online d L) (eL: online e L)
    (bM: online b M) (cM: online c M)
    (aN: online a N) (dN: online d N)
    (eN: ¬ online e N)
    (Badb : B a d b) (Baec : B a e c) :
    proportion (length a b) (length a d) (length a c) (length a e) ↔ para L M 

/-- equal points are colinear -/
lemma colinear_of_eq_23 (a b : point) : colinear a b b 

/-- equal points are colinear -/
lemma colinear_of_eq_12 (a b : point) : colinear a a b 

/-- equal points are colinear -/
lemma colinear_of_eq_13 (a b : point) : colinear a b a 

/-- not colinear implies different -/
lemma neq_12_of_not_colinear {a b c : point} (h: ¬ colinear a b c) : a ≠ b 

/-- not colinear implies different -/
lemma neq_13_of_not_colinear {a b c : point} (h: ¬ colinear a b c) : a ≠ c 

/-- not colinear implies different -/
lemma neq_23_of_not_colinear {a b c : point} (h: ¬ colinear a b c) : b ≠ c 

/-- not colinear implies one of the points is not aligned -/
lemma not_online_of_not_colinear {a b c : point} {L : line} (aL: online a L) (bL : online b L) (h: ¬ colinear a b c) :
    ¬ online c L 

/-- technical lemma: can always find a point beyond two points -/
lemma pt_extension_of_ne {b c : point} :
    b ≠ c → ∃ a : point, B b c a 

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
    para BC HG 

/-- two similar triangles that share an edge are equal -/
lemma length_eq_of_length_eq {a b c d e f : point}
    (Tabc : ¬ colinear a b c) (Tdef : ¬ colinear d e f) 
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f)
    (hlen: length d f = length a c) :
    length d e = length a b 

/-- Given two similar triangles, if the side of one triangle is smaller than that of the second,
then the remaining sides are also smaller -/
lemma length_lt_of_length_lt {a b c d e f : point}
    (Tabc : ¬ colinear a b c) (Tdef : ¬ colinear d e f) 
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f)
    (lineq: length d f < length a c) :
    length d e < length a b 

/-- Two triangles are similar if they have two angles equal -/
theorem similar_of_AA {a b c d e f : point} (Tabc : ¬ colinear a b c) (Tdef : ¬ colinear d e f) 
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) : 
    proportion (length a b) (length d e) (length a c) (length d f) 
