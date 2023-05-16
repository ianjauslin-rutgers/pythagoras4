open incidence_geometry
variable [i: incidence_geometry]

/-- colinear API -/

lemma ne_13_of_not_colinear {a b c : point} (tri_abc : ¬ colinear a b c) : a ≠ c 

lemma ne_12_of_not_colinear {a b c : point} (tri_abc : ¬ colinear a b c) : a ≠ b 

lemma ne_23_of_not_colinear {a b c : point} (tri_abc : ¬ colinear a b c) : b ≠ c 

lemma not_colinear_T {a b c : point} (tri_abc : ¬ colinear a b c) : ¬ colinear b c a 

lemma not_colinear_R {a b c : point} (tri_abc : ¬ colinear a b c) : ¬ colinear b a c 

/-- Aux lemmata -/

lemma aux_1 {a b c : point} (tri_abc : ¬ colinear a b c) (ang_a : rightangle ≤ angle b a c) : 
    ∃ d, B b d c ∧ angle b d a = rightangle 

lemma aux_2 {a b c d : point} (a_ne_b : a ≠ b) (Bbdc : B b d c) : angle a b d = angle a b c 

/-- *** Euclid VI.31 *** -/
theorem pythagorean_proof_two {a b c : point} (tri_abc : ¬ colinear a b c) 
    (ang_a : angle b a c = rightangle) : 
    (length a b)^2 + (length a c)^2 = (length b c)^2 


