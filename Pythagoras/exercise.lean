import SyntheticEuclid4

open incidence_geometry
variable {i : incidence_geometry}

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
  have : lines_inter L M := by
    have diffbcL := diffside_of_B_offline' (Bbdc) (dL) ?_
    have sameecL := sameside_of_B_not_online_2 Baec aL ?_
    have := diffside_of_sameside_diffside (sameside_symm sameecL) (diffside_symm diffbcL)
    have : lines_inter L M := lines_inter_of_not_sameside bM eM ?_
    dsimp [diffside] at this
    exact this
  sorry

/-
theorem incenter (a b c d e f : point)
    (Bafb: B a f b) (Bbdc: B b d c) (Baec : B a e c)
    (aa: angle b a d = angle d a c) (bb: angle a b e = angle e b c) (cc: angle a c f = angle b c f):
    ∃ g : point, B a g d ∧ B c g f ∧ B b g e := by
  obtain ⟨L, aL, dL⟩ := line_of_pts a d
  obtain ⟨M, bM, eM⟩ := line_of_pts b e
  have : lines_inter L M
  ·
-/
