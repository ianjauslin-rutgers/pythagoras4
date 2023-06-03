import SyntheticEuclid4
-- import Mathlib.Data.FinEnum

open incidence_geometry
open Classical
open List

variable [i: incidence_geometry]

def WeakSameside (a b : point) (L : line) : Prop := sameside a b L ∨ online a L ∨ online b L

def list_shift_nat [DecidableEq α] (lst : List α) (H: lst ≠ []) (a : α) (k : ℕ) : α := by
  let n := lst.length
  let i := lst.indexOf a + k
  have : i % n < n := by
    cases lst
    · contradiction
    · apply Nat.mod_lt _ _; simp
  exact lst[i % n]

/-- ##
  #reduce list_shift ["a", "b", "c", "d"] (by simp) "a" (-1)
 -/
def list_shift [DecidableEq α]  (lst : List α) (H: lst ≠ []) (a : α) (k : ℤ) : α := by
  cases k with
  | ofNat l => exact list_shift_nat lst H a l
  | negSucc l => exact list_shift_nat lst H a (lst.length - l - 1)

def convex (V: List point) (ne: V ≠ []) : Prop :=
  ∀ a b c : point, ∀ L : line,
  (a ∈ V) -> (b ∈ V) -> (c ∈ V) -> (online a L) → (online (list_shift V ne a 1) L) → WeakSameside b c L

lemma convex_of_sublist (C: convex V nV) (sub: W <+ V) (nW: W ≠ []) : convex W nW := by sorry

structure ConvexPolygon where
  vertices : List point
  nonempty: vertices ≠ [] := by simpa
  nodup : Nodup vertices
  convex: convex vertices nonempty

lemma mem_diff_single_of_ne {l₁: List α} (bL: b ∈ l₁) (ab: a ≠ b) : b ∈ l₁.diff [a] :=
  mem_diff_of_mem bL (by simp [ab.symm])

lemma mem_diff_single_of_ne'
{l₁: List α} (bl₁d: b ∈ l₁.diff [a]) (ab: a ≠ b) : b ∈ l₁ := by sorry

lemma mem_diff_single_of_ne2
{l₁: List α} (bl₁d: b ∈ l₁.diff [a]) : a ≠ b := by sorry

def ConvexPolygon_remove_vertex [DecidableEq point] (P : ConvexPolygon) (a b : point)
 (ab: a ≠ b) (bP: b ∈ P.vertices) : ConvexPolygon:= by
  let V := P.vertices.diff [a]
  have ne : V ≠ [] := by
    intro empty
    apply (@eq_nil_iff_forall_not_mem point (P.vertices.diff [a])).mp empty b
    convert mem_diff_single_of_ne bP ab
  have convex := convex_of_sublist P.convex (diff_sublist P.vertices [a]) ne
  exact ConvexPolygon.mk V ne (Nodup.diff P.nodup) convex

#exit
def Fin.neZero_of (i : Fin n) : NeZero n := ⟨Nat.pos_iff_ne_zero.mp (Fin.pos i)⟩

def finenum_shift_nat {S : Set α} [FinEnum S] (a : S) (k : ℕ) : α :=
  haveI := Fin.neZero_of (FinEnum.Equiv a)
  (FinEnum.Equiv.symm ((FinEnum.Equiv a : ℕ) + k) : S)

def finenum_shift {S : Set α} [h_fin: FinEnum S] (a : S) (k : ℤ) : α := by
  cases k with
  | ofNat l => exact finenum_shift_nat a l
  | negSucc l => exact finenum_shift_nat a (h_fin.card - l - 1)

structure ConvexPolygon := 
  (vertices : Set point)
  (h_finenum : FinEnum vertices)
  (convex : ∀ a b c : vertices, ∀ L : line, (online a L) → (online (finenum_shift a 1) L)
    → WeakSameside b c L)


#exit

example (n i j : ℕ) (hji: j < i) (hin: i < n) (l k : ZMod (i - j + 1)) (hlk: l ≠ k) (hjlk: (j : ZMod n) + l = j + k) : 
    False := by
  
  sorry


#exit

open incidence_geometry
open Classical


variable [i: incidence_geometry]

def WeakSameside (a b : point) (L : line) : Prop := sameside a b L ∨ online a L ∨ online b L 

structure ConvexPolygon := 
  (n : ℕ)
  (hn : n ≠ 0)
  (vertex : ZMod n → point)
  (distinct : ∀ i j : ZMod n, i ≠ j → vertex i ≠ vertex j)
  (convex : ∀ i j k : ZMod n, ∀ L : line, (online (vertex i) L) → (online (vertex (i+1)) L)
    → WeakSameside (vertex j) (vertex k) L)

def ConvexPolygon_split_L (P : ConvexPolygon)
    (i j : ℕ) (hji : j < i) (hin : i < P.n) : ConvexPolygon := by    
  refine ConvexPolygon.mk (i - j + 1) (by linarith) (fun (k : ZMod (i - j + 1)) => P.vertex (j + k)) ?_ ?_
  · intro l k hlk hPlk
    refine P.distinct (j+l) (j+k) ?_ hPlk
    intro hjlk
    
    let ii  := l.val
    have : (l : ZMod P.n) = k := by
      have := congr_fun_congr_arg


#exit

      have := congr_fun_congr_arg (fun (m : ZMod P.n) => (j : ZMod P.n) + m) ?_ 
        ?_
    sorry --- ALEX HOMEWORK

  · intro l m k L lL lpoL 
    have := P.convex (j+l) (j+m) (j+k) L ?_ ?_
    repeat {sorry} ---- ALEX HOMEWORK
    
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
def is_triangulation (T : Finset Triangle) (P : ConvexPolygon) : Prop :=
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
def is_triangulation' (T : Finset Triangle) (P : ConvexPolygon) : Prop :=
  match P.n with
  | 0 => T = Finset.empty
  | 1 => T = Finset.empty
  | 2 => T = Finset.empty
  | Nat.succ n => 
    ∃ i : ZMod (n+1) , ∃ t ∈ T, triangle_eq_of_pts (P.vertex i) (P.vertex (i+1)) (P.vertex (i+2)) t
    ∧ is_triangulation (Finset.erase T t) (ConvexPolygon_split_L P (i-1) (i+1))
