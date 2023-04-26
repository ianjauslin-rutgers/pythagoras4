open incidence_geometry
variable [i: incidence_geometry]

/-- technical lemma that really shouldn't be here, but hey... -/

lemma mul_mul_lt (a b c : ℝ) (hc: 0<c):
    a<b → a*c<b*c 

/-- technical lemma that really shouldn't be here, but hey... -/
lemma ge2_of_n1_n0 {n : ℕ}
    (h0: n ≠ 0) (h1: n ≠ 1) :
    n ≥ 2 

/-- technical lemma that really shouldn't be here, but hey... -/
lemma gt1_of_n1_n0 {n : ℕ}
    (h0: n ≠ 0) (h1: n ≠ 1) :
    n > 1 

/-- from segment of length l, construct a new segment of length n*l
    based on I.3 -/
lemma rescale_length {a b : point} {L : line} (n : ℕ)
    (haL: online a L)
    (hbL: online b L) :
    ∃ (c : point), (online c L) ∧ (length a c = n*(length a b)) ∧ (n ≥ 2 ∧ a ≠ b → B a b c) 

/-- rescale base of triangle -/
-- workhorse: version for use in inductive case
lemma rescale_triangle_of_base__inductive (a : point) {b c : point} {L : line} {n : ℕ}
    (hbL: online b L)
    (hcL: online c L)
    (h_a_nonline_L: ¬ online a L) :
    ∀ d:point, (online d L) → (length b d = n*(length b c)) → B b c d → area a b d = n*(area a b c) 

-- lemma with B b c d as a hypothesis
lemma rescale_triangle_of_base__B (a : point) {b c d : point} {L : line} {n : ℕ}
    (hbL: online b L)
    (hcL: online c L)
    (hdL: online d L)
    (hlen: length b d = n*(length b c))
    (hB: B b c d)
    (h_a_nonline_L: ¬ online a L) :
    area a b d = n*(area a b c) 

-- not B c b d
lemma rescale_triangle_of_base__notcbd (a : point) {b c d : point} {L : line} {n : ℕ}
    (hbL: online b L)
    (hcL: online c L)
    (hdL: online d L)
    (hlen: length b d = n*(length b c))
    (hB: ¬ B c b d)
    (h_b_ne_c: b ≠ c)
    (h_n_ne_0: n ≠ 0)
    (h_b_ne_d: b ≠ d)
    (h_a_nonline_L: ¬ online a L) :
    area a b d = n*(area a b c) 

-- full version
lemma rescale_triangle_of_base (a : point) {b c d : point} {L : line} {n : ℕ}
    (hbL: online b L)
    (hcL: online c L)
    (hdL: online d L)
    (hlen: length b d = n*(length b c)) :
    area a b d = n*(area a b c) 

/-- triangles between parallels with smaller base have smaller area -/
-- case where they share a side and have the right betweeneness
lemma lt_area_of_lt_base__sameedge_Bbfc (a : point) {b c f: point} {L: line}
    (hbL: online b L)
    (hcL: online c L)
    (hfL: online f L)
    (hB: B b f c)
    (h_b_ne_c: b ≠ c)
    (h_b_ne_f: b ≠ f)
    (h_c_ne_f: c ≠ f)
    (h_a_nonline_L: ¬ online a L) :
    (length b c)>(length b f) → (area a b c)>(area a b f) 

-- case where they share a side and not B f b c
lemma lt_area_of_lt_base__sameedge_nBfbc (a : point) {b c f: point} {L: line}
    (hbL: online b L)
    (hcL: online c L)
    (hfL: online f L)
    (h_b_ne_c: b ≠ c)
    (h_b_ne_f: b ≠ f)
    (h_a_nonline_L: ¬ online a L)
    (hB: ¬ B f b c) :
    (length b c)>(length b f) → (area a b c)>(area a b f) 

-- case where they share a side
lemma lt_area_of_lt_base__sameedge (a : point) {b c f: point} {L: line}
    (hbL: online b L)
    (hcL: online c L)
    (hfL: online f L)
    (h_b_ne_c: b ≠ c)
    (h_b_ne_f: b ≠ f)
    (h_a_nonline_L: ¬ online a L) :
    (length b c)>(length b f) → (area a b c)>(area a b f) 

-- general case
lemma lt_area_of_lt_base {a b c d e f: point} {L M: line}
    (haM: online a M)
    (hbL: online b L)
    (hcL: online c L)
    (hdM: online d M)
    (heL: online e L)
    (hfL: online f L)
    (hpar: para L M) :
    (length b c)>(length e f) → (area a b c)>(area d e f) 

/-- ## Euclid VI.1
two triangles in between parallel lines have their area in proportion with the length of their base
 https://mathcs.clarku.edu/~djoyce/java/elements/bookVI/propVI1.html -/
theorem proportion_area_of_proportion_base {a b c d e f: point} {L M : line}
    (haM: online a M)
    (hbL: online b L)
    (hcL: online c L)
    (hdM: online d M)
    (heL: online e L)
    (hfL: online f L)
    (hpar: para L M) :
    proportion (length b c) (length e f) (area a b c) (area d e f) 

/-- version where the vertex is the same for both triangles -/
theorem proportion_area_of_proportion_base_samevertex (a : point) {b c e f: point} {L : line}
    (hbL: online b L)
    (hcL: online c L)
    (heL: online e L)
    (hfL: online f L)
    (h_a_nonline_L: ¬ online a L) :
    proportion (length b c) (length e f) (area a b c) (area a e f) 

/-- ## Euclid VI.2
a line cuts the sides of the triangle proportionally iff it is parallel to one of the sides of a triangle (version BD:AD = CE:AE)
 https://mathcs.clarku.edu/~djoyce/java/elements/bookVI/propVI2.html -/
theorem proportional_iff_para {a b c d e: point} {L M N: line}
    (hdL: online d L)
    (heL: online e L)
    (hbM: online b M)
    (hcM: online c M)
    (haN: online a N)
    (hdN: online d N)
    (hneN: ¬ online e N)
    (Badb : B a d b) (Baec : B a e c) :
    proportion (length b d) (length a d) (length c e) (length a e) ↔ para L M 

/-- ## Euclid VI.2'
a line cuts the sides of the triangle proportionally iff it is parallel to one of the sides of a triangle (version AB:AD = AC:AE)
 https://mathcs.clarku.edu/~djoyce/java/elements/bookVI/propVI2.html -/
theorem proportional_iff_para' {a b c d e: point} {L M N: line}
    (hdL: online d L)
    (heL: online e L)
    (hbM: online b M)
    (hcM: online c M)
    (haN: online a N)
    (hdN: online d N)
    (hneN: ¬ online e N)
    (Badb : B a d b) (Baec : B a e c) :
    proportion (length a b) (length a d) (length a c) (length a e) ↔ para L M 

/-- colinear is symmetric under odd permutation -/
theorem colinear_symm1 :
    colinear a b c ↔ colinear b a c 

/-- colinear is symmetric under even permutation -/
theorem colinear_symm2 :
    colinear a b c ↔ colinear b c a 

/-- equal points are colinear -/
lemma colinear_of_eq_23 (a b : point) :
    colinear a b b 

/-- equal points are colinear -/
lemma colinear_of_eq_12 (a b : point) :
    colinear a a b 

/-- equal points are colinear -/
lemma colinear_of_eq_13 (a b : point) :
    colinear a b a 

/-- not colinear implies different -/
lemma neq_12_of_not_colinear {a b c : point} (h: ¬ colinear a b c) :
    a ≠ b 

/-- not colinear implies different -/
lemma neq_13_of_not_colinear {a b c : point} (h: ¬ colinear a b c) :
    a ≠ c 

/-- not colinear implies different -/
lemma neq_23_of_not_colinear {a b c : point} (h: ¬ colinear a b c) :
    b ≠ c 

/-- not colinear implies one of the points is not aligned -/
lemma not_online_of_not_colinear {a b c : point} {L : line} (haL: online a L) (hbL : online b L) (h: ¬ colinear a b c) :
    ¬ online c L 

/-- technical lemma: can always find a point beyond two points -/
lemma pt_extension_of_ne {b c : point} :
    b ≠ c → ∃ a : point, B b c a 

/-- similar triangles (should follow from Euclid VI.2) -/
-- show resulting lines are parallel
lemma parallel_of_similar {a b c g h : point} {AB AC BC HG: line}
    (haAB: online a AB)
    (hbAB: online b AB)
    (hhAB: online h AB)
    (haAC: online a AC)
    (hcAC: online c AC)
    (hgAC: online g AC)
    (hbBC: online b BC)
    (hcBC: online c BC)
    (hhHG: online h HG)
    (hgHG: online g HG)
    (b_ne_h: b ≠ h)
    (a_ne_b: a ≠ b)
    (a_ne_c: a ≠ c)
    (b_ne_c: b ≠ c)
    (h_ne_g: h ≠ g)
    (a_ne_g: a ≠ g)
    (b_nonline_AC: ¬ online b AC)
    (an: angle a h g = angle a b c)
    (hB: B a h b)
    (hss: sameside g c AB) :
    para BC HG 

/-- two similar triangles that share an edge are equal -/
lemma length_eq_of_length_eq {a b c d e f : point}
    (tri_abc : ¬ colinear a b c) (tri_def : ¬ colinear d e f) 
    (ang_a_eq_d : angle b a c = angle e d f) (ang_b_eq_e : angle a b c = angle d e f)
    (leq: length d f = length a c) :
    length d e = length a b 

/-- Given two similar triangles, if the side of one triangle is smaller than that of the second,
then the remaining sides are also smaller -/
lemma length_lt_of_length_lt {a b c d e f : point}
    (tri_abc : ¬ colinear a b c) (tri_def : ¬ colinear d e f) 
    (ang_a_eq_d : angle b a c = angle e d f) (ang_b_eq_e : angle a b c = angle d e f)
    (lineq: length d f < length a c) :
    length d e < length a b 

/-- Two triangles are similar if they have two angles equal -/
theorem similar_of_AA {a b c d e f : point} (tri_abc : ¬ colinear a b c) (tri_def : ¬ colinear d e f) 
    (ang_a_eq_d : angle b a c = angle e d f) (ang_b_eq_e : angle a b c = angle d e f) : 
    proportion (length a b) (length d e) (length a c) (length d f) 


