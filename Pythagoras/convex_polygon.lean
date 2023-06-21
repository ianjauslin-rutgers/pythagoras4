import SyntheticEuclid4
import Mathlib.Data.List.Rotate
open incidence_geometry
open Classical
open List

variable [i: incidence_geometry]

def WeakSameside (a b : point) (L : line) : Prop := sameside a b L ∨ online a L ∨ online b L

-- allows colinearity, unlike triangle --
structure Triangle where
  a : point
  b : point
  c : point
  ab : a ≠ b
  ac : a ≠ c
  bc : b ≠ c

def nodup_of_triangle (T : triangle a b c) : Nodup [a, b, c] := by
  have ab := ne_12_of_tri T
  have ac := ne_13_of_tri T
  have bc := ne_23_of_tri T
  simp [Nodup, *]

def triangle_to_Triangle (T : triangle a b c) : Triangle := by
  have ab := ne_12_of_tri T
  have ac := ne_13_of_tri T
  have bc := ne_23_of_tri T
  exact Triangle.mk a b c ab ac bc

/-- is abc = t? -/
def triangle_eq_of_pts (a b c : point) (T : Triangle) :=
  (T.a=a ∧ T.b=b ∧ T.c=c) ∨
  (T.a=a ∧ T.b=c ∧ T.c=b) ∨
  (T.a=b ∧ T.b=a ∧ T.c=c) ∨
  (T.a=b ∧ T.b=c ∧ T.c=a) ∨
  (T.a=c ∧ T.b=a ∧ T.c=b) ∨
  (T.a=c ∧ T.b=b ∧ T.c=a)

def triangle_eq (T U : Triangle) :=
  triangle_eq_of_pts T.a T.b T.c U

lemma nodup_of_triangle_eq (eq : triangle_eq_of_pts a b c T) : Nodup [a, b, c] := by
  have ab := T.ab
  have ac := T.ac
  have bc := T.bc
  simp [not_and]
  rcases eq with (h|h|h|h|h|h)
  all_goals
    simp [h.1, h.2.1, h.2.2] at ab ac bc
    tauto

-- symmetric in a,b --
def exterior_triangle (a b x : point) (V : List point) : Prop :=
  (a ∈ V) ∧ (b ∈ V) ∧ (a ≠ b) ∧ (x ∉ V) ∧ ( B a x b ∨
  ∀ L M N : line,
  ( (online a L) ∧ (online b L) ∧
    (online a M) ∧ (online x M) ∧
    (online b N) ∧ (online x N)   ) →
  ∀ c ∈ V, (c ≠ a) → (c ≠ b) →
  (B a c b ∨ (diffside x c L ∧ WeakSameside b c M ∧  WeakSameside a c N)))

-- the a b c is the first triangle in S, then it must be an exterior triangle w.r.t. V = c :: V'
def convex_triangulation (V : List point) (S : List Triangle) : Prop :=
  -- TODO: match V.reverse, S.reverse with
  match V, S with
  | [], _ => False
  | _, [] => False
  | [a, b, c], [T] => triangle_eq_of_pts a b c T
  | x :: V', T :: S' => convex_triangulation V' S' ∧ exterior_triangle T.a T.b x V' ∧ x = T.c
  termination_by convex_triangulation V S => V.length
  -- TODO: decreasing_by simp_wf; exact list_reverse_induction

def triangulation_area (S : List Triangle) : ℝ :=
  match S with
  | [] => 0
  | T :: S' => area T.a T.b T.c + triangulation_area S'

structure ConvexPolygon (V : List point) where
  triangulation : List Triangle
  convex : convex_triangulation V triangulation

namespace ConvexPolygon

def area (P : ConvexPolygon V) : ℝ := triangulation_area P.triangulation

def n (_ : ConvexPolygon V) : ℕ := V.length

lemma vertices_ne_nil (P : ConvexPolygon V) : V ≠ [] := by
  have S := P.triangulation
  have C := P.convex
  match V, S with
  | [], _ => simp [convex_triangulation] at C
  | _ :: _, _ => simp

lemma triangulation_ne_nil (P : ConvexPolygon V) : P.triangulation ≠ [] := by
  have C := P.convex
  set S := P.triangulation
  match V, S with
  | [], [] => simp [convex_triangulation] at C
  | _ :: _, [] => simp [convex_triangulation] at C
  | _ :: _, _ :: _ => simp

lemma nodup (P : ConvexPolygon V) : Nodup V := by
  have C := P.convex
  set S := P.triangulation
  induction V with
  | nil => simp
  | cons x V' IH =>
      match S, V' with
      | [], _ => simp [convex_triangulation] at C
      | [_], [] => simp
      | [T], [_] => simp [convex_triangulation] at C
      | [T], [_, _] => exact nodup_of_triangle_eq C
      | [T], _ :: _ :: _ :: _ => simp [convex_triangulation] at C
      | T :: T' :: S', V' =>
        simp [convex_triangulation] at C; simp [nodup_cons]
        exact ⟨ C.2.1.2.2.2.1 , IH (ConvexPolygon.mk (T' :: S') C.1) C.1⟩

lemma number_of_triangles_eq (P : ConvexPolygon V) : P.triangulation.length + 2 = P.n := by
  have C := P.convex
  have ne_nil := P.triangulation_ne_nil
  generalize hS : P.triangulation = S at C ne_nil
  induction S generalizing V with
  | nil => contradiction
  | cons T S' IH =>
    match V, S' with
    | [], _ => simp [convex_triangulation] at C
    | [_], [] => simp [convex_triangulation] at C
    | [_, _], [] => simp [convex_triangulation] at C
    | [_, _, _], [] => rfl
    | _ :: _ :: _ :: _ :: V', [] => simp [convex_triangulation] at C
    | x :: V', T' :: S'' =>
        simp [ConvexPolygon.n] at IH |-; simp [convex_triangulation] at C
        exact IH (ConvexPolygon.mk (T' :: S'') C.1) (rfl) C.1

end ConvexPolygon

lemma triangle_is_convex (T: Triangle) : ConvexPolygon [T.a, T.b, T.c] := ConvexPolygon.mk [T] (by tauto)

lemma triangle_area_eq (P : ConvexPolygon [a,b,c]) : P.area = area a b c := by
  have C := P.convex
  set S := P.triangulation with ← hS
  match S with
  | [] => exfalso; exact C
  | [T] =>
      dsimp [ConvexPolygon.area, triangulation_area]; ring_nf
      have : triangle_eq_of_pts a b c T := C
      rcases this with (h|h|h|h|h|h) <;> {rw [hS]; simp [triangulation_area, add_zero]; rw [h.1, h.2.1, h.2.2]; perm}
  | _ :: _ :: _ =>
    have := P.number_of_triangles_eq
    simp [ConvexPolygon.n, hS] at this

lemma nodup_of_paragram (pg: paragram a b c d M N O P) : Nodup [a, b, c, d] := by
  have := nodup_of_triangle $ tri124_of_paragram pg; simp [Nodup]; simp [Nodup] at this
  obtain ⟨ _, bM, _, cN, cO, _, dP, aP, pMO, pNP ⟩ := pg
  have ac : a ≠ c := fun ac => by rw [ac] at aP; exact not_para_of_inter cN aP pNP
  have bc : b ≠ c := fun bc => by rw [bc] at bM; exact not_para_of_inter bM cO pMO
  have cd : c ≠ d := fun cd => by rw [← cd] at dP; exact not_para_of_inter cN dP pNP
  tauto

lemma paragram_is_convex (pg: paragram a b c d M N O P) : ConvexPolygon [a, b, c, d] := by
  have nodup := nodup_of_paragram pg; simp [Nodup, and_assoc] at nodup
  obtain ⟨ ab, ac, ad, bc, bd, cd⟩ := nodup
  let T := Triangle.mk b c d  bc bd cd
  let T' := Triangle.mk b d a bd (Ne.symm ab) (Ne.symm ad)
  use [T', T]; simp [convex_triangulation]
  constructor; simp [triangle_eq_of_pts]; simp [exterior_triangle, *]
  right; intro L M' N' bL dL bM' aM' dN' aN' _; right
  obtain ⟨ aM, bM, bN, cN, cO, dO, dP, aP, pMO, pNP ⟩ := id pg
  rw [← line_unique_of_pts ab aM bM aM' bM']
  rw [← line_unique_of_pts (Ne.symm ad) dP aP dN' aN']
  constructor; exact diffside_of_paragram bL dL pg
  constructor; left; exact sameside_of_para_online dO cO (by perma)
  constructor; exact sameside_of_para_online bN cN (by perma)

lemma unique_triangulation (P : ConvexPolygon V) (P' : ConvexPolygon V):
  triangle_eq (P.triangulation.head P.triangulation_ne_nil) (P'.triangulation.head P'.triangulation_ne_nil) := by
  set S := P.triangulation with ← hS
  set S' := P'.triangulation with ← hS'
  simp [hS, hS']
  sorry
  -- untrue as stated, the last added triangle could be degenerate in different ways

def diff_quadri_splits (T U T' U' : Triangle) : Prop :=
  ∃ a b c d : point, ∃ V : List point, ∃ P : ConvexPolygon [a, b, c, d], ∃ P' : ConvexPolygon V,
  [a, b, c, d] ≠ V ∧ Perm [a, b, c, d] V ∧ P.triangulation = [T, U] ∧ P'.triangulation = [T', U']

lemma eq_area_of_quadri (P : ConvexPolygon [a, b, c, d]) (P' : ConvexPolygon V) (perm : Perm [a, b, c, d] V) : P.area = P'.area := by
  sorry

def eq_area_of_quadri_splits (T U T' U' : Triangle) (splits : diff_quadri_splits T U T' U') :
    area T.a T.b T.c + area U.a U.b U.c = area T'.a T'.b T'.c + area U'.a U'.b U'.c := by
  obtain ⟨ a, b, c, d, V, P, P', _, perm, hP, hP' ⟩ := splits
  have := eq_area_of_quadri P P' perm
  convert this <;> simp [ConvexPolygon.area, triangulation_area, hP, hP']

def adj_triangulation (S : List Triangle) (S' : List Triangle) : Prop :=
  ∃ T U T' U' : Triangle, T ∈ S ∧ U ∈ S ∧ T' ∈ S' ∧ U' ∈ S' ∧
  diff_quadri_splits T U T' U' ∧ Perm (S.diff [T, U]) (S'.diff [T', U']) ∧ (S.diff [T, U]) ≠ (S'.diff [T', U'])

lemma eq_area_of_adj_triangulation (P : ConvexPolygon V) (P' : ConvexPolygon V')
    (adj : adj_triangulation P.triangulation P'.triangulation) : P.area = P'area := by
  obtain ⟨ T, U, T', U', TS, US, T'S', U'S', splits, diff⟩ := adj
  sorry

lemma eq_area_of_eq_last_vertex (P : ConvexPolygon (x :: V)) (P' : ConvexPolygon (x :: V')) (R : ConvexPolygon V) (R' : ConvexPolygon V') (H : R.area = R'.area ): P.area = P'.area := by sorry
