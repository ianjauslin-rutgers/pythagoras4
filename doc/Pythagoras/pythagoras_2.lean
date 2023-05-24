open incidence_geometry
variable [i: incidence_geometry]

/-- Aux lemma -/
lemma aux {a b c : point} (Tabc : ¬ colinear a b c) (ang_a : rightangle ≤ angle b a c) :
    ∃ d, B b d c ∧ angle b d a = rightangle 

/-- *** Euclid VI.31 *** -/
theorem pythagorean_proof_two {a b c : point} (Tabc : triangle a b c)
    (ang_a : angle b a c = rightangle) : 
    (length a b)^2 + (length a c)^2 = (length b c)^2
