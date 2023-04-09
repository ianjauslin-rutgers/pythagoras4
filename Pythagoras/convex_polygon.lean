import SyntheticEuclid4
import Mathlib.Data.Fin.Basic

open incidence_geometry

variables [i: incidence_geometry]

def WeakSameside (a b : point) (L : line) : Prop := sameside a b L ∨ online a L ∨ online b L 

def IsConvexPolygon (n : ℕ) (vertex : Fin n → point) : Prop :=
(distinct : ∀ i : Fin n, vertex i ≠ vertex (i+1)) ∧ (convex : ∀ i j k : Fin n, WeakSameside (vertex j) (vertex k) 
  (line_of_pts (vertex i) (vertex (i+1))))

