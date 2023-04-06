import Euclid.synthetic
import Mathlib.Data.ZMod.Basic

open incidence_geometry

variables [i: incidence_geometry] {a b c d e f g h j k l m n: i.point} {L M N O P Q: i.line}

def WeakSameside (a b : point) (L : line) : Prop := sameside a b L ∨ online a L ∨ online b L 

class ConvexPolygon (n : ℕ) := 
(vertex : ZMod n → point)
(distinct : ∀ i : ZMod n, vertex i ≠ vertex (i+1))
(convex : ∀ i j k : ZMod n, WeakSameside (vertex j) (vertex k) 
  (line_of_pts (vertex i) (vertex (i+1))))

  