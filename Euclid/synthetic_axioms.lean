/-
Copyright (c) 2022 André Hernandez-Espiet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : André Hernandez-Espiet
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite

/-!
# Synthetic Geometry, Euclid's Elements Book I using Avigad Axioms
In this file we ...

## Main definitions
* `incidence_geometry` : class containing axioms...

## Main results
* `pythagorean_theorem` : The Pythagorean theorem
## Tags
synthetic geometry, Euclid elements
-/

universe u1 u2 u3
class incidence_geometry :=
(point : Type u1)
(line : Type u2)
(circle : Type u3)

(online : point → line → Prop)
(sameside : point → point → line → Prop)
(B : point → point → point → Prop) -- Betweenness
(oncircle : point → circle → Prop)
(in_circ : point → circle → Prop)
(cen_circ : point → circle → Prop)
(lines_inter : line → line → Prop)
(line_circle_inter : line → circle → Prop)
(circles_inter : circle → circle → Prop)
(length : point → point → ℝ)
(angle : point → point → point → ℝ)
(rightangle : ℝ)
(area : point → point → point → ℝ)

(more_pts : ∀ (S : Set point), S.Finite → ∃ (a : point), a ∉ S)
(pt_B_of_ne : ∀ {b c : point}, b ≠ c → ∃ (a : point), B b a c) -- old (P3)
(pt_extension_of_ne : ∀ {b c : point}, b ≠ c → ∃ (a : point), B b c a)
(diffside_of_not_online : ∀ {L : line}, ∀ {b : point}, ¬online b L →
  ∃ (a : point), ¬online a L ∧ ¬sameside a b L)
(line_of_pts : ∀ (a b : point), ∃ (L :line), online a L ∧ online b L) -- old (LB_of_line_circle_inter)
(circle_of_ne : ∀ {a b : point}, a ≠ b → ∃ (α : circle),  oncircle b α ∧ cen_circ a α)
(pt_of_lines_inter : ∀ {L M : line}, lines_inter L M →
  ∃ (a : point), online a L ∧ online a M)
(pts_of_line_circle_inter : ∀ {L : line}, ∀ {α : circle}, line_circle_inter L α →
  ∃ (a b : point),  a ≠ b ∧ online a L ∧ online b L ∧ oncircle a α ∧ oncircle b α )
(pt_oncircle_of_inside_outside : ∀ {b c : point}, ∀ {α : circle},
  ¬oncircle c α →in_circ b α → ¬in_circ c α →
  ∃ (a : point), B b a c ∧ oncircle a α )
(pt_oncircle_of_inside_ne : ∀ {b c : point}, ∀ {α : circle}, b ≠ c →in_circ b α →
  ∃ (a : point), B a b c ∧ oncircle a α )
(pts_of_circles_inter : ∀ {α β : circle}, circles_inter α β →
  ∃ (a b : point), a≠ b∧ oncircle a α ∧ oncircle a β ∧ oncircle b α ∧ oncircle b β )
(pt_sameside_of_circles_inter : ∀ {b c d : point}, ∀ {L : line}, ∀ {α β : circle},
  online c L → online d L →¬online b L  → cen_circ c α → cen_circ d β →circles_inter α β
  →  ∃ (a : point), sameside a b L∧ oncircle a α ∧  oncircle a β )
(line_unique_of_pts : ∀ {a b : point}, ∀ {L M : line}, a ≠ b → online a L → online b L →
  online a M → online b M → L = M)
(center_circle_unique : ∀ {a b : point}, ∀ {α : circle}, cen_circ a α → cen_circ b α →
  a = b)
(inside_circle_of_center : ∀ {a : point}, ∀ {α : circle}, cen_circ a α → in_circ a α)
(not_oncircle_of_inside : ∀ {a : point}, ∀ {α : circle}, in_circ a α → ¬oncircle a α)
(B_symm : ∀ {a b c : point}, B a b c → B c b a )
(ne_12_of_B : ∀ {a b c : point}, B a b c → a ≠ b )
(ne_13_of_B : ∀ {a b c : point}, B a b c → a ≠ c)
(ne_23_of_B : ∀ {a b c : point}, B a b c → b ≠ c )
(not_B_of_B : ∀ {a b c : point}, B a b c → ¬B b a c)
(online_3_of_B : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → online b L → online c L)
(online_2_of_B : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → online c L → online b L)
(B124_of_B134_B123 : ∀ {a b c d : point}, B a b c → B a d b → B a d c)
(B124_of_B123_B234 : ∀ {a b c d : point}, B a b c → B b c d → B a b d)
(B_of_three_online_ne : ∀ {a b c : point}, ∀ {L : line}, a ≠ b → a ≠ c → b ≠ c → online a L →
  online b L → online c L →  B a b c ∨ B b a c ∨ B a c b)
(not_B324_of_B123_B124 : ∀ {a b c d : point}, B a b c → B a b d → ¬B c b d)
(sameside_rfl_of_not_online : ∀ {a : point}, ∀ {L : line}, ¬online a L → sameside a a L)
(sameside_symm : ∀ {a b : point}, ∀ {L : line}, sameside a b L → sameside b a L)
(not_online_of_sameside : ∀ {a b : point}, ∀ {L : line}, sameside a b L → ¬online a L)
(sameside_trans : ∀ {a b c : point}, ∀ {L : line}, sameside a b L → sameside a c L → sameside b c L)
(sameside_or_of_diffside : ∀ {a b c : point}, ∀ {L : line}, ¬online a L → ¬online b L → ¬online c L →
  ¬sameside a b L → sameside a c L ∨ sameside b c L)
(sameside12_of_B123_sameside13 : ∀ {a b c : point}, ∀ {L : line}, B a b c → sameside a c L → sameside a b L)
(sameside23_of_B123_online1_not_online2 : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → ¬online b L → sameside b c L)
(not_sameside13_of_B123_online2 : ∀ {a b c : point}, ∀ {L : line}, B a b c → online b L → ¬sameside a c L)
(B_of_online_inter : ∀ {a b c : point}, ∀ {L M : line}, a ≠ b → b≠ c → a≠ c→ M≠ L → online a M → online b M → online c M →
  online b L →  ¬sameside a c L → B a b c)
(not_sameside_of_sameside_sameside : ∀ {a b c d : point}, ∀ {L M N : line}, online a L → online a M → online a N → online b L →
  online c M → online d N → sameside c d L → sameside b c N → ¬sameside b d M)
(sameside_of_sameside_not_sameside : ∀ {a b c d : point}, ∀ {L M N : line}, a≠ b → online a L → online a M → online a N → online b L →
  online c M → online d N → ¬online d M → sameside c d L → ¬sameside b d M →
  sameside b c N)
(B_of_line_circle_inter : ∀ {a b c : point}, ∀ {L : line}, ∀ {α : circle },b ≠ c → online a L → online b L → online c L
  → oncircle b α → oncircle c α → in_circ a α →   B b a c)
(not_sameside_of_circle_inter : ∀ {a b c d : point}, ∀ {L : line}, ∀ {α β : circle},  c ≠ d→ α ≠ β →  online a L
  → online b L  → oncircle c α → oncircle c β → oncircle d α → oncircle d β → cen_circ a α → cen_circ b β →
  circles_inter α β → ¬sameside c d L)
(lines_inter_of_not_sameside : ∀ {a b : point}, ∀ {L M : line}, online a M → online b M → ¬sameside a b L →
  lines_inter L M)
(line_circle_inter_of_not_sameside : ∀ {a b : point}, ∀ {L : line}, ∀ {α : circle},¬sameside a b L → oncircle a α ∨ in_circ a α→
 oncircle b α ∨ in_circ b α  →  line_circle_inter L α)
(line_circle_inter_of_inside_online : ∀ {a : point}, ∀ {L : line}, ∀ {α : circle}, online a L → in_circ a α →  line_circle_inter L α)
(circles_inter_of_inside_oncircle : ∀ {a b : point}, ∀ {α β : circle}, oncircle b α → oncircle a β → in_circ a α →  in_circ b β →
  circles_inter α β)
(length_eq_zero_iff : ∀ {a b : point}, length a b = 0 ↔ a = b)
(length_symm : ∀ (a b : point), length a b = length b a)
(angle_symm : ∀ (a b c : point), angle a b c = angle c b a)
(angle_nonneg : ∀ (a b c : point), 0 ≤ angle a b c)
(length_nonneg : ∀ (a b : point), 0 ≤ length a b)
(area_nonneg : ∀ (a b c : point), 0 ≤ area a b c)
(degenerate_area : ∀ (a b : point), area a a b = 0)
(area_invariant : ∀ (a b c : point), area a b c = area c a b ∧ area a b c = area a c b)
(area_eq_of_SSS : ∀ {a b c a1 b1 c1 : point}, length a b = length a1 b1 → length b c = length b1 c1 →
  length c a = length c1 a1 → area a b c = area a1 b1 c1)
(length_sum_of_B : ∀ {a b c : point}, B a b c → length a b + length b c = length a c)
(oncircle_iff_length_eq : ∀ {a b c : point}, ∀ {α : circle},  oncircle b α → cen_circ a α →
  (length a b = length a c ↔ oncircle c α))
(incircle_iff_length_lt : ∀ {a b c : point}, ∀ {α : circle}, oncircle b α → cen_circ a α →
  (length a c < length a b ↔ in_circ c α))
(angle_zero_iff_online : ∀ {a b c : point}, ∀ {L : line}, a ≠ b → a ≠ c → online a L → online b L →
  (online c L ∧ ¬B b a c ↔ angle b a c = 0))--better reformulation?
(angle_add_iff_sameside : ∀ {a b c d : point}, ∀ {L M : line}, a ≠ b → a ≠ c → online a L → online b L → online a M
  → online c M → ¬online d M → ¬online d L → L ≠ M →
  (angle b a c = angle b a d + angle d a c ↔ sameside b d M ∧ sameside c d L))
(angle_eq_iff_rightangle : ∀ {a b c d : point}, ∀ {L : line}, online a L → online b L → ¬online d L → B a c b →
  (angle a c d = angle d c b ↔ angle a c d = rightangle))
(angle_extension : ∀ {a b c b1 c1 : point}, ∀ {L M : line}, b ≠ a → b1 ≠ a → c ≠ a → c1 ≠ a → online a L → online b L → online b1 L →
  online a M → online c M → online c1 M →  ¬B b a b1 → ¬B c a c1 → angle b a c = angle b1 a c1)
(unparallel_postulate : ∀ {a b c d : point}, ∀ {L M N : line},b ≠ c → online a L → online b L → online b M → online c M →
  online c N → online d N →  sameside a d M → angle a b c + angle b c d < 2 * rightangle →
  ∃ (e : point), online e L ∧ online e N ∧ sameside e a M)
(area_zero_iff_online : ∀ {a b c : point}, ∀ {L : line},a ≠ b → online a L → online b L →
  (area a b c = 0 ↔ online c L))
(area_add_iff_B : ∀ {a b c d : point}, ∀ {L : line}, a ≠ b → b ≠ c → c ≠ a → online a L → online b L →
  online c L → ¬online d L → (B a c b ↔ area a c d + area d c b = area a d b))
(SAS_iff_SSS : ∀ {a b c d e f : point}, length a b = length d e → length a c = length d f →
  (angle b a c = angle e d f ↔ length b c = length e f)) --Euclid Prop 4,8
