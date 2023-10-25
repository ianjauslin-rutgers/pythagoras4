import SyntheticEuclid4
--import Mathlib.Tactic

open incidence_geometry
variable [i: incidence_geometry]

-- idea: perhaps Euclid I.9, I.10, I.11 could be used?
-- alternatively, introducing new API and definitions (e.g., for medians) could be helpful
-- or use Ceva's theorem

theorem incenter (a b c d e f : point)
    (Bafb : B a f b) (Bbdc : B b d c) (Baec : B a e c)
    (abc: triangle a b c)
    (Aa : angle b a d = angle d a c)
    (Ab : angle a b e = angle e b c)
    (Ac : angle a c f = angle f c b) :
    ∃ g : point, B a g d ∧ B b g e ∧ B c g f ∧
    ∃ d' e' f' : point,
      Baf'b : B a f' b ∧
      Bbd'c : B b d' c ∧
      Bae'c : B a e' c
      angle g d' b = rightangle ∧
      angle g e' c = rightangle ∧
      angle g f' a = rightangle ∧
    ∃ α : circle, center_circle g α ∧
                  on_circle d' α ∧
                  on_circle e' α ∧
                  on_circle f' α
    := by
  obtain ⟨ L, aL, dL ⟩ := line_of_pts a d
  obtain ⟨ M, bM, eM ⟩ := line_of_pts b e
  have : lines_inter L M
  sorry
  -- sketch: let g be the intersection of L and M, drop perpendiculars from it,
  --         argue about similar triangles to deduce that g lies on the angle bisector at C

theorem circumcenter (a b c d e f : point) (L M N : line)
    (Bafb : B a f b) (Bbdc : B b d c) (Baec : B a e c)
    (Ld : length b d = length c d)
    (Le : length a e = length c e)
    (Lf : length a f = length b f)
    (dL : online d L) (eM : online e M) (fN : online f N)
    (Lbis : ∀ p : point, length b p = length c p → online p L)
    (Mbis : ∀ p : point, length a p = length c p → online p M)
    (Nbis : ∀ p : point, length a p = length b p → online p N) :
    ∃ g : point, online g L ∧ online g M ∧ online g M ∧
    ∃ α : circle, center_circle g α ∧
                  on_circle a α ∧
                  on_circle b α ∧
                  on_circle c α
    := by
  sorry
  -- sketch: https://math.stackexchange.com/questions/2166284/prove-that-the-perpendicular-bisectors-of-all-3-sides-of-a-triangle-intersect-in

theorem orthocenter (a b c d e f : point)
    (Bafb : B a f b) (Bbdc : B b d c) (Baec : B a e c)
    (dalt : angle a d b = rightangle)
    (ealt : angle b e c = rightangle)
    (falt : angle c f a = rightangle) :
    ∃ g : point, B a g d ∧ B b g e ∧ B c g f := by
  sorry
  -- sketch: https://math.stackexchange.com/questions/1700740/three-altitudes-of-a-triangle-are-concurrent?noredirect=1&lq=1
  --        (might need API about cyclic quadrilaterals first)


theorem centroid (a b c d e f : point)
    (Bafb : B a f b) (Bbdc : B b d c) (Baec : B a e c)
    (Ld : length b d = length c d)
    (Le : length a e = length c e)
    (Lf : length a f = length b f) :
    ∃ g : point, B a g d ∧ B b g e ∧ B c g f := by
  obtain ⟨ L, aL, dL ⟩ := line_of_pts a d
  obtain ⟨ M, bM, eM ⟩ := line_of_pts b e
  have : lines_inter L M
  sorry
  -- sketch: the first answer from https://math.stackexchange.com/questions/411709/proving-that-the-medians-of-a-triangle-are-concurrent?rq=1 might be feasible


-- to add: Feuerbach's circle, Euler's line, theorems about angles in circles,...
