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

lemma triangle_is_Triangle (T: triangle a b c) : Triangle := by
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

-- symmetric in a,b --
def exterior_triangle (a b x : point) (V : List point) : Prop :=
  (a ∈ V) ∧ (b ∈ V) ∧ (a ≠ b) ∧ (x ∉ V) ∧
  (B a x b) ∨ (∀ L M N : line,
  ((online a L) ∧ (online b L) ∧
  (online a M) ∧ (online x M) ∧
  (online b N) ∧ (online x N)) →
  ∀ c ∈ V, B a c b ∨ (diffside x c L ∧ WeakSameside b c M ∧  WeakSameside a c N))

-- the a b c is the first triangle in S, then it must be an exterior triangle w.r.t. V = c :: V'
def convex_triangulation (V : List point) (S : List Triangle) : Prop :=
  -- TODO: match V.reverse, S.reverse with
  match V, S with
  | _, [] => False
  | [], _ => False
  | [_], _ => False
  | [_, _], _ => False
  | [a, b, c], [T] => triangle_eq_of_pts a b c T
  | [_, _, _], _ :: _ :: _ => False -- for easier proofs
  | x :: V', T :: S' => convex_triangulation V' S' ∧ exterior_triangle T.a T.b x V ∧ x = T.c
  termination_by convex_triangulation V S => V.length
  -- TODO: decreasing_by simp_wf; exact list_reverse_induction

def triangulation_area (S : List Triangle) : ℝ :=
  match S with
  | [] => 0
  | T :: S' => area T.a T.b T.c + triangulation_area S'

structure ConvexPolygon (V : List point) (S : List Triangle) where
  convex : convex_triangulation V S

def ConvexPolygon.area (_ : ConvexPolygon V S) : ℝ := triangulation_area S

lemma convex_triangulation_any_nil (V : List point): convex_triangulation V [] = False := by
  induction V with
  | nil => rfl
  | cons h t => sorry -- HEq issue?

lemma number_of_triangles_eq (P : ConvexPolygon V S) : S.length + 2 = V.length := by
  have C := P.convex
  induction S generalizing V with
  | nil => exfalso; rwa [convex_triangulation_any_nil V] at C
  | cons T S' IHS =>
      match V with
      | [] => exfalso; exact C
      | [_] => exfalso; exact C
      | [_, _] => exfalso; exact C
      | [a, b, c] =>
          match S' with
          | [] => rfl
          | cons T' S'' => exfalso; exact C
      | x :: V' =>
          induction V' generalizing S' with
          | nil => exfalso; exact C
          | cons y W IHV =>
              have : convex_triangulation W S' ∧ exterior_triangle T.a T.b x V ∧ x = T.c := by sorry -- extract this from C somehow
              have : convex_triangulation W S' := this.1
              sorry

lemma triangle_is_convex (T: Triangle) : ConvexPolygon [T.a, T.b, T.c] [T] := ConvexPolygon.mk (by tauto)

lemma triangle_area_eq (P : ConvexPolygon V S) (abc : V = [a, b, c]) : P.area = area a b c := by
  have := P.convex
  rw [abc] at this
  match S with
  | [] => exfalso; exact this
  | [T] =>
      dsimp [ConvexPolygon.area, triangulation_area]
      ring_nf
      have : triangle_eq_of_pts a b c T := this
      rcases this with (h|h|h|h|h|h)
      all_goals rw [h.1, h.2.1, h.2.2]; perm
  | _ :: _ :: _ =>
      have := number_of_triangles_eq P
      rw [abc] at this
      simp at this
