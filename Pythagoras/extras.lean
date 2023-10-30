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
      B a f' b ∧
      B b d' c ∧
      B a e' c ∧
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
  have liLM : lines_inter L M := by
    have diffbcL := diffside_of_B_offline' (Bbdc) (dL) ?_
    have sameecL := sameside_of_B_not_online_2 Baec aL ?_
    have := diffside_of_sameside_diffside (sameside_symm sameecL) (diffside_symm diffbcL)
    have : lines_inter L M := lines_inter_of_not_sameside bM eM ?_
    dsimp [diffside] at this
    exact this
  obtain ⟨ g, gL, gM ⟩ := pt_of_lines_inter liLM
  obtain ⟨ BC, bBC, cBC ⟩ := line_of_pts b c
  have gNotOnBC : ¬online g BC := by
    sorry
  have ⟨b2, d2, e2, Bc2d2e2, b2BC, d2BC, e2BC, ge2b2Right, ge2d2Right⟩ := perpendicular_of_not_online gNotOnBC
  -- TODO: Use angle extension theorem or something to turn ge2b2Right, ge2d2Right into something more usable

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
