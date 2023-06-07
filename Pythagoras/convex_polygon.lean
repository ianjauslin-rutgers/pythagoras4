import SyntheticEuclid4
import Mathlib.Data.List.Rotate
open incidence_geometry
open Classical
open List

variable [i: incidence_geometry]

def WeakSameside (a b : point) (L : line) : Prop := sameside a b L ∨ online a L ∨ online b L

example (a b c : α) [DecidableEq α] : Nodup [a,b,c] → List.indexOf a [a,b,c] = 0 := by simp [indexOf_cons_ne]

example (a b c : α) [DecidableEq α] : Nodup [a,b,c] → List.indexOf b [a,b,c] = 1 := by
  intro nodup; simp at nodup; simp [@indexOf_cons_ne _ _ b a [b,c] (by tauto)]

def list_shift_nat [DecidableEq α] (l : List α) (a : α) (al : a ∈ l) (i : ℕ) : α := by
  let n := l.length
  let j := l.indexOf a + i
  have : j % n < n := by
    cases l
    · contradiction
    · apply Nat.mod_lt _ _; simp
  exact l[j % n]

/-- ### An alternative definition, currently not used -/
def list_shift_nat' [DecidableEq α] (l : List α) (a : α) (aL : a ∈ l) (i : ℕ) : α
 := by
  have : l ≠ [] := by aesop
  let j := l.indexOf a + i
  apply (l.rotate j).head; simp[*, isRotated_nil_iff.not.mpr]

/-- #reduce list_shift ["a", "b", "c", "d"] (by simp) "a" (-1) -/
def list_shift [DecidableEq α] (l : List α) (a : α) (al : a ∈ l) (i : ℤ) : α := by
  cases i with
  | ofNat j => exact list_shift_nat l a al j
  | negSucc j => exact list_shift_nat l a al (l.length - j - 1)

@[simp]
lemma eq_of_shift_eq {l : List α} (h : a = b) (al : a ∈ l) (bL : b ∈ l) (i : ℤ): list_shift l a al i = list_shift l b bL i := by simp [*]

lemma mem_of_idx (l : List α) (i : ℕ) {hi: i < List.length l} : l[i] ∈ l := by simp [mem_iff_get]

lemma list_shift_1_nat : ∀ a b c : α, list_shift_nat [a,b,c] a (by simp) 1 = b := by
  intro a b c; simp [list_shift_nat]

lemma list_shift_1 : ∀ a b c : α, list_shift [a,b,c] a (by simp) 1 = b := by
  intro a b c; simp [list_shift]; conv => rhs; rw [← list_shift_1_nat a b c]

lemma list_shift_1_nat' [DecidableEq α] : ∀ a b c : α, Nodup [a,b,c] → list_shift_nat [a,b,c] b (by simp) 1 = c := by
  intro a b c nodup; simp at nodup; simp [list_shift_nat]; ring_nf
  have : [a,b,c].get {val := 2, isLt:= (by simp)} = c := by rfl
  rw [← this]; congr; simp [Nat.mod_eq_of_lt]
  simp [@indexOf_cons_ne _ _ b a [b,c] (by tauto)]

lemma list_shift_1' : ∀ a b c : α, Nodup [a,b,c] → list_shift [a,b,c] b (by simp) 1 = c := by
  intro a b c nodup; conv => rhs; rw [← list_shift_1_nat' a b c nodup]

lemma list_shift_1_nat'' : ∀ a b c : α, Nodup [a,b,c] → list_shift_nat [a,b,c] c (by simp) 1 = a := by
  intro a b c nodup; simp at nodup; simp [list_shift_nat]; ring_nf
  have : [a,b,c].get {val := 0, isLt:= (by simp)} = a := by rfl
  rw [← this]; congr; simp [Nat.mod_eq_of_lt]
  simp [@indexOf_cons_ne _ _ c a [b,c] (by tauto), @indexOf_cons_ne _ _ c b [c] (by tauto)]

lemma list_shift_1'' : ∀ a b c : α, Nodup [a,b,c] → list_shift [a,b,c] c (by simp) 1 = a := by
  intro a b c nodup; conv => rhs; rw [← list_shift_1_nat'' a b c nodup]

def convex (V: List point) : Prop :=
  ∀ a b c d : point, ∀ L : line,
  (aV: a ∈ V) → (b ∈ V) → (c ∈ V) → (d = list_shift V a aV 1) → (online a L) → (online d L) → WeakSameside b c L

def convex' (V: List point) : Prop :=
  ∀ a b c d : point, ∀ L : line,
  (aV: a ∈ V) → (b ∈ V) → (c ∈ V) → (d = list_shift V a aV 1) → (a ≠ b) → (a ≠ c) → (b ≠ c) → (b ≠ d) → (c ≠ d) → (online a L) → (online d L) → WeakSameside b c L

lemma convex_iff_convex' [DecidableEq point] (V: List point): convex V ↔ convex' V := by
  constructor
  intro C a b c d L aV bV cB hD _ _ _ _ _ aL dL; exact C a b c d L aV bV cB hD aL dL
  intro C a b c d L aV bV cB hD aL dL
  by_cases ab : a = b
  · right; left; rwa [ab] at aL
  · by_cases ac : a = c
    · right; right; rwa [ac] at aL
    · by_cases bc : b = c
      · by_cases cL : online c L
        · right; right; exact cL
        · left; rw [bc]; exact sameside_rfl_of_not_online cL
      · by_cases bd : b = d
        · right; left; rwa [← bd] at dL
        by_cases cd : c = d
        · right; right; rwa [← cd] at dL
        · exact C a b c d L aV bV cB hD ab ac bc bd cd aL dL

lemma convex_of_sublist (C: convex V) (sub: W <+ V) (nW: W ≠ []) : convex W := by sorry

structure ConvexPolygon where
  vertices : List point
  nodup : Nodup vertices
  convex: convex vertices
  nondeg: vertices ≠ [] := by simp

lemma triangle_is_convex_aux (a b c x : point) (xP: x ∈ [a,b,c]) (yP: y ∈ [a,b,c]) (zP: z ∈ [a,b,c]) (hw : w = list_shift [a,b,c] x xP 1) (xa : x = a) (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z) (yw : y ≠ w) (zw : z ≠ w) : WeakSameside y z L := by
  have wb : w = b := by simp [eq_of_shift_eq xa, hw, list_shift_1]
  have yc : y = c := by convert yP; rw [← xa, ← wb]; simp [xy.symm, yw]
  have zc : z = c := by convert zP; rw [← xa, ← wb]; simp [xz.symm, zw]
  exfalso; exact yz $ yc.trans zc.symm

lemma triangle_is_convex (T: triangle a b c) : ConvexPolygon := by
  have nodup: Nodup [a,b,c] := by perm [ne_12_of_tri T, ne_13_of_tri T, ne_23_of_tri T]; simp; tauto
  refine ConvexPolygon.mk [a,b,c] nodup ?_
  rw [convex_iff_convex']; intro x y z w L xP yP zP hw xy xz yz yw zw _ _
  by_cases xa: x = a
  · exact triangle_is_convex_aux a b c x xP yP zP hw xa xy xz yz yw zw
  · by_cases xb: x = b
    · refine' triangle_is_convex_aux b c a x (by simp [*]) _ _ _ xb xy xz yz yw zw
      repeat rwa [← @IsRotated.mem_iff _ [a,b,c] [b,c,a]]; use 1; rfl
      simp [xb, list_shift_1' a b c nodup, hw, list_shift_1]
    · have xc : x = c := by convert xP; simp [*]
      refine' triangle_is_convex_aux c a b x (by simp [*]) _ _ _ xc xy xz yz yw zw
      repeat rwa [← @IsRotated.mem_iff _ [a,b,c] [c,a,b]]; use 2; rfl
      simp [eq_of_shift_eq xc, list_shift_1'' a b c nodup, hw, list_shift_1]

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
