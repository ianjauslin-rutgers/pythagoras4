import SyntheticEuclid4
-- import Mathlib.Data.FinEnum

open incidence_geometry
open Classical
open List

variable [i: incidence_geometry]

def WeakSameside (a b : point) (L : line) : Prop := sameside a b L ∨ online a L ∨ online b L

def list_shift_nat [DecidableEq α] (lst : List α) (aL : a ∈ lst) (i : ℕ) : α := by
  let n := lst.length
  let j := lst.indexOf a + i
  have : j % n < n := by
    cases lst
    · contradiction
    · apply Nat.mod_lt _ _; simp
  exact lst[j % n]

/-- ##
  #reduce list_shift ["a", "b", "c", "d"] (by simp) "a" (-1)
 -/
def list_shift [DecidableEq α] (lst : List α) (aL : a ∈ lst) (i : ℤ) : α := by
  cases i with
  | ofNat j => exact list_shift_nat lst aL j
  | negSucc j => exact list_shift_nat lst aL (lst.length - j - 1)

lemma same_of_shift_same {l₁ l₂ : List α} (hl: l₁ = l₂) (aL₁ : a ∈ l₁) (aL₂ : a ∈ l₂) (i : ℤ): list_shift l₁ aL₁ i = list_shift l₂ aL₂ i := by simp [*]

lemma mem_of_idx (lst : List α) (i : ℕ) {hi: i < List.length lst} : lst[i] ∈ lst := by simp [mem_iff_get]

lemma mem_of_shift [DecidableEq α] (lst : List α) (aL : a ∈ lst) (i : ℤ) : list_shift lst aL i ∈ lst := by cases i with | ofNat | negSucc => apply mem_of_idx

lemma same_of_shift_iff [DecidableEq α] (lst : List α) (nodup: lst.Nodup) (aL : a ∈ lst) (i : ℤ) : list_shift lst aL i = a ↔ lst.length % i = 0 := by sorry

lemma list_shift_1_nat (a b c : point): @list_shift_nat _ a _ [a, b, c] (by simp) 1 = b := by dsimp [list_shift_nat]; simp [*]

lemma list_shift_1 (a b c : point): @list_shift _ a _ [a, b, c] (by simp) 1 = b := by conv => rhs; rw [← list_shift_1_nat a b c]

def convex (V: List point) : Prop :=
  ∀ a b c d: point, ∀ L : line,
  (aV: a ∈ V) → (b ∈ V) → (c ∈ V) → (d = list_shift V aV 1) → (online a L) → (online d L) → WeakSameside b c L

  ∀ a b c : point, ∀ L : line,
  (aV: a ∈ V) -> (b ∈ V) → (c ∈ V) → (online a L) → (online (list_shift V aV 1) L) → WeakSameside b c L

lemma convex_of_sublist (C: convex V) (sub: W <+ V) (nW: W ≠ []) : convex W := by sorry

structure ConvexPolygon where
  vertices : List point
  nodup : Nodup vertices
  convex: convex vertices
  nondeg: vertices ≠ [] := by simp

lemma triangle_is_convex (T: triangle a b c) : ConvexPolygon := by
  refine ConvexPolygon.mk [a,b,c] ?_ ?_
  perm [ne_12_of_tri T, ne_13_of_tri T, ne_23_of_tri T]; simp; tauto
  dsimp [convex, WeakSameside]
  intro x y z w L xP yP zP hw xL wL
  have xa : x = a := by
    obtain ⟨ n, hn ⟩ := get_of_mem xP
    have : n = (0 : Fin 3) := by sorry -- WLOG
    simp [*, hn.symm]
  have wP : w ∈ [a, b, c] := by convert mem_of_shift [a,b,c] xP 1
  have : [a,b,c] = [x,b,c] := by simp [xa]
  rw [same_of_shift_same this xP (by simp) 1] at hw
  have wb : w = b := by simp [hw, list_shift_1]
  rw [wb] at wL; rw [xa] at xL
  by_cases ya : y = a
  · simp [xL, ya]
  · by_cases za : z = a
    · simp [xL, za]
    · by_cases yz : y = z
      · by_cases yb : y = b
        · right; left; rwa [yb]
        · have yc : y = c := by
            have : z ≠ b := fun zb => yb $ yz.trans zb
            convert yP; simp [*]
          simp [*]; left; apply sameside_rfl_of_not_online
          simp [yz.symm, yc]; exact online_3_of_triangle xL wL T
      · by_cases yb : y = b
        · simp [*]
        · have yc : y = c := by convert yP; simp [*]
          have zc : z ≠ c := fun zc => yz $ yc.trans zc.symm
          have zb : z = b := by convert zP; simp [*]
          right; right; rwa [←zb] at wL

lemma mem_diff_single_of_ne {l₁: List α} (bL: b ∈ l₁) (ab: a ≠ b) : b ∈ l₁.diff [a] :=
  mem_diff_of_mem bL (by simp [ab.symm])

def ConvexPolygon_remove_vertex [DecidableEq point] (P : ConvexPolygon) (a b : point)
 (ab: a ≠ b) (bP: b ∈ P.vertices) : ConvexPolygon:= by
  let V := P.vertices.diff [a]
  have ne : V ≠ [] := by
    intro empty
    apply (@eq_nil_iff_forall_not_mem point (P.vertices.diff [a])).mp empty b
    convert mem_diff_single_of_ne bP ab
  have convex := convex_of_sublist P.convex (diff_sublist P.vertices [a]) ne
  exact ConvexPolygon.mk V (Nodup.diff P.nodup) convex ne

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
