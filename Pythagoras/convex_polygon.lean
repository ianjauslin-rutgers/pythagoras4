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
  | _, [] => false
  | [], _ => false
  | _ :: [], _ => false
  | _ :: _ :: [], _ => false
  | x :: a :: [b], [T] => triangle_eq_of_pts a b x T
  | x :: V', T :: S' => convex_triangulation V' S' ∧ exterior_triangle T.a T.b x V ∧ x = T.c
  termination_by convex_triangulation V S => V.length
  -- TODO: decreasing_by simp_wf

structure ConvexPolygon where
  vertices : List point
  triangulation : List Triangle
  convex : convex_triangulation vertices triangulation

namespace ConvexPolygon

def triangulation_area (S : List Triangle) : ℝ :=
  match S with
  | [] => 0
  | T :: S' => area T.a T.b T.c + triangulation_area S'

def area (P : ConvexPolygon) : ℝ := triangulation_area P.triangulation

end ConvexPolygon

lemma triangle_is_convex (T: Triangle) : ConvexPolygon :=
  ConvexPolygon.mk [T.c, T.a, T.b] [T] (by tauto)

lemma triangle_area_eq (P : ConvexPolygon) (abc : P.vertices = [a, b, c]): P.area = area a b c := by
  dsimp [ConvexPolygon.area]
  have := P.convex
  match P.triangulation with
  | [] => sorry -- cannot occur
  | [T] =>
    have hT : P.triangulation = [T] := by sorry -- we have that already!
    rw [hT, abc] at this
    dsimp [ConvexPolygon.triangulation_area]
    ring_nf
    have : triangle_eq_of_pts b c a T := this
    dsimp [triangle_eq_of_pts] at this
    rcases this with (h|h|h|h|h|h)
    all_goals rw [h.1, h.2.1, h.2.2]; perm
  | _ :: _ => sorry -- cannot occur
