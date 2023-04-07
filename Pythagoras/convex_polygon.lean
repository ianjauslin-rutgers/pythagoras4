import SyntheticEuclid4
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

open incidence_geometry
open Classical


variables [i: incidence_geometry]

def WeakSameside (a b : point) (L : line) : Prop := sameside a b L ∨ online a L ∨ online b L 

structure ConvexPolygon := 
  (n : ℕ)
  (hn : n ≠ 0)
  (vertex : ZMod n → point)
  (distinct : ∀ i : ZMod n, vertex i ≠ vertex (i+1))
  (convex : ∀ i j k : ZMod n, ∀ L : line, (online (vertex i) L) → (online (vertex (i+1)) L)
    → WeakSameside (vertex j) (vertex k) L)


def ConvexPolygon_split_L (P : ConvexPolygon)
    (i j : ZMod P.n) := by
  refine ConvexPolygon.mk ((i-j).val+1) ?_ (fun n : ZMod ((i-j).val+1) => P.vertex ((j+n).val)) ?_ ?_

  · by_contra contra
    have := @ZMod.val_lt P.n (neZero_iff.mpr P.hn) (i-j)
    linarith

  · intro l
    have := P.distinct (j+l).val
    simp
    sorry

  · intro l m k L
    simp
    intro l_online_L m_online_L
    have := P.convex (j+l) (j+m) (j+k) L ?_ ?_
    sorry

    sorry
    sorry
    
def ConvexPolygon_split_R (P : ConvexPolygon) (i j : ZMod P.n) := ConvexPolygon_split_L P j i

lemma decreasing_ConvexPolygon_split_L (P : ConvexPolygon) (i j : ZMod P.n)
    (hij: i ≠ j) (hijp : i ≠ j+1) (hijm : i ≠ j-1) :
    (ConvexPolygon_split_L P i j).n < P.n := by
  dsimp [ConvexPolygon_split_L]
  have := @ZMod.val_lt P.n (neZero_iff.mpr P.hn) (i-j)
  sorry

lemma decreasing_ConvexPolygon_split_R (P : ConvexPolygon) (i j : ZMod P.n)
    (hij: i ≠ j) (hijp : i ≠ j+1) (hijm : i ≠ j-1) :
    (ConvexPolygon_split_R P i j).n < P.n := by
  refine decreasing_ConvexPolygon_split_L P j i hij.symm ?_ ?_
  by_contra contra
  · rw [contra] at hijm
    ring_nf at hijm
    tauto
  by_contra contra
  · rw [contra] at hijp
    ring_nf at hijp
    tauto


--class Triangle := (a b c : point)
structure Triangle where
  a : point
  b : point
  c : point

/-- is abc = t? -/
def triangle_eq_of_pts (a b c : point) (t : Triangle) :=
  (t.a=a ∧ t.b=b ∧ t.c=c) ∨
  (t.a=a ∧ t.b=c ∧ t.c=b) ∨
  (t.a=b ∧ t.b=a ∧ t.c=c) ∨
  (t.a=b ∧ t.b=c ∧ t.c=a) ∨
  (t.a=c ∧ t.b=a ∧ t.c=b) ∨
  (t.a=c ∧ t.b=b ∧ t.c=a)

def triangle_eq (t u : Triangle) :=
  triangle_eq_of_pts t.a t.b t.c u



/-- is abc in a set of triangles? -/
def triangle_in_set (a b c : point) (T : Set Triangle) :=
  ∃ t ∈ T, triangle_eq_of_pts a b c t

/-- is this point in the polygon -/
def point_in_ConvexPolygon (a : point) (P : ConvexPolygon) :=
  ∃ i : ZMod P.n, a = P.vertex i
/-- is the whole triangle in the polygon -/
def triangle_in_ConvexPolygon (t : Triangle) (P : ConvexPolygon) :=
  point_in_ConvexPolygon t.a P ∧
  point_in_ConvexPolygon t.b P ∧
  point_in_ConvexPolygon t.c P
  

/-- More general: suffices to show that a triangle splits the polygon into two triangulations -/
def is_triangulation (T : Finset Triangle) (P : ConvexPolygon) :=
  match P.n with
  | 0 => T = Finset.empty
  | 1 => T = Finset.empty
  | 2 => T = Finset.empty
  | 3 => T.card = 1 ∧ (∀ t ∈ T, triangle_eq_of_pts (P.vertex 0) (P.vertex 1) (P.vertex 2) t)
  | Nat.succ n => 
    ∃ i j k : ZMod P.n, ∃ h : i≠j ∧ (i≠j-1) ∧ (i≠j+1) ∧ k≠i ∧ k≠j,  (triangle_in_set (P.vertex i) (P.vertex j) (P.vertex k) T)
    ∧ is_triangulation (Finset.filter (fun t:Triangle => triangle_in_ConvexPolygon t (ConvexPolygon_split_L P i j)) T) (ConvexPolygon_split_L P i j)
    ∧ is_triangulation (Finset.filter (fun t:Triangle => triangle_in_ConvexPolygon t (ConvexPolygon_split_R P i j)) T) (ConvexPolygon_split_R P i j)
  -- termination is dictated by P.n
  termination_by is_triangulation T P => P.n
  decreasing_by
    simp_wf
    try exact decreasing_ConvexPolygon_split_L P i j h.1 h.2.2.1 h.2.1
    try exact decreasing_ConvexPolygon_split_R P i j h.1 h.2.2.1 h.2.1



/-- This definition requires the identification of an external triangle -/
def is_triangulation' (T : Finset Triangle) (P : ConvexPolygon) :=
  match P.n with
  | 0=> T = Finset.empty
  | 1 => T = Finset.empty
  | 2 => T = Finset.empty
  | Nat.succ n => 
    ∃ i : ZMod (n+1) , ∃ t ∈ T, triangle_eq_of_pts (P.vertex i) (P.vertex (i+1)) (P.vertex (i+2)) t
    ∧ is_triangulation (Finset.erase T t) (ConvexPolygon_split_L P (i-1) (i+1))
