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
        simp [convex_triangulation] at C; rw [nodup_cons]
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

lemma eq_number_of_triangles_of_perm (P : ConvexPolygon V) (P' : ConvexPolygon V') (perm : V ~ V') :
   P.triangulation.length = P'.triangulation.length := by
  suffices List.length P.triangulation + 2 = List.length P'.triangulation + 2 by   simpa
  simp [P.number_of_triangles_eq, P'.number_of_triangles_eq, ConvexPolygon.n, Perm.length_eq perm]

lemma triangle_is_convex (T : Triangle) : ConvexPolygon [T.a, T.b, T.c] := ConvexPolygon.mk [T] (by tauto)

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

lemma perm_of_two {x y : α} {V : List α} (perm : [x, y] ~ V) : V = [x, y] ∨ V = [y, x] := by
  cases perm with
  | cons _ hy => simp [perm_singleton] at hy; simp [hy]
  | swap => simp
  | trans perm' perm'' =>
    induction perm'' with
    | nil => simp at perm'
    | cons X perm =>
        rename_i T _ _
        have := perm'.mem_iff.mpr (by simp : X ∈ X :: T)
        by_cases hX : X = x
        · simp [hX, perm_singleton.mp (((hX ▸ perm').cons_inv).trans perm).symm]
        · simp [hX] at this
          simp [this, (((Perm.swap x y []).trans $ this ▸ perm').cons_inv.trans perm).symm |> perm_singleton.mp]
    | swap X Y T =>
        by_cases hY : Y = x
        · have := (hY ▸ perm').cons_inv.symm |> perm_singleton.mp
          rw [cons.injEq] at this; simp [this, hY]
        · have Yy := perm'.mem_iff.mpr (by simp : Y ∈ Y :: X :: T); simp [hY] at Yy
          have := Yy ▸ (Perm.swap x y []).trans perm'
          rw [perm_cons, singleton_perm, cons.injEq] at this; simp [this, Yy]
    | trans perm'' _ _ IH => exact IH (perm'.trans perm'')

lemma perm_of_three {x y : α} {V : List α} (perm : [x, y, z] ~ V) :
    V = [x, y, z] ∨ V = [x, z, y] ∨ V = [y, x, z] ∨ V = [y, z, x] ∨ V = [z, x, y] ∨ V = [z, y, x] := by
  cases perm with
  | cons _ perm' => rcases perm_of_two perm' with (h|h) <;> simp [h]
  | swap => simp
  | trans perm' perm'' =>
    induction perm'' with
    | nil => simp at perm'
    | cons X perm =>
        rename_i _ T _
        have perm := perm'.trans $ perm.cons X
        have XV := (perm).mem_iff.mpr (by simp : X ∈ X :: T)
        by_cases hX : X = x
        · simp [hX, Perm.cons_inv] at perm
          rcases perm_of_two perm with (h|h) <;> simp [hX, h]
        · simp [hX] at XV
          rcases XV with (h|h)
          · have := (Perm.swap x y [z]).trans perm; simp [h] at this
            rcases perm_of_two this with (H|H) <;> simp [h, H]
          · have := ((Perm.swap x z [y]).trans $ (Perm.swap y z []).cons x).trans perm
            simp [h] at this
            rcases perm_of_two this with (H|H) <;> simp [h, H]
    | swap X Y T =>
        by_cases hY : Y = x
        · rw [hY] at perm' |-
          rcases perm_of_two perm'.cons_inv with (h|h) <;> {simp at h; simp [h]}
        · have YV := perm'.mem_iff.mpr (by simp : Y ∈ Y :: X :: T); simp [hY] at YV
          rcases YV with (h|h)
          · have perm := (Perm.swap x y [z]).trans perm';
            simp [h, Perm.cons_inv] at perm
            rcases perm_of_two perm with (H|H) <;> {simp at H; simp [H, h]}
          · have := ((Perm.swap x z [y]).trans $ (Perm.swap y z []).cons x).trans perm'
            simp [h, Perm.cons_inv] at this
            rcases perm_of_two this with (H|H) <;> {simp at H; simp [H, h]}
    | trans perm'' _ _ IH => exact IH (perm'.trans perm'')

lemma eq_area_of_tri (P : ConvexPolygon [a, b, c]) (P' : ConvexPolygon V) (perm : [a, b, c] ~ V) : P.area = P'.area := by
  have C' := P'.convex
  set S' := P'.triangulation with ← hS
  have triples := perm_of_three perm
  match S' with
  | [] => exfalso; exact P'.triangulation_ne_nil hS
  | _ :: _ :: _ =>
      have := P'.number_of_triangles_eq
      simp [ConvexPolygon.n, Perm.length_eq perm.symm, length_eq_one, hS] at this
  | [T] =>
      have := Perm.length_eq perm.symm
      match V with
      | [] => simp [convex_triangulation] at C'
      | [_] => simp [convex_triangulation] at C'
      | [_, _] => simp [convex_triangulation] at C'
      | _ :: _ :: _ :: _ :: _ => simp [List.length] at this
      | [x, y, z] =>
          simp [triangle_area_eq]
          rcases triples with (h|h|h|h|h|h) <;> {simp at h; rw [h.1, h.2.1, h.2.2]; perm}

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
  let T := Triangle.mk b c d bc bd cd
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

lemma eq_area_of_eq_last_vertex (P: ConvexPolygon $ x :: V) (P': ConvexPolygon $ x :: V') (hS : P.triangulation = T :: S) (hS' : P'.triangulation = U :: S') :
    triangulation_area [T] = triangulation_area [U] := by
  -- distinguish if the last triangle is degenerate or not
  sorry

def eq_area_of_quadri_splits (P: ConvexPolygon $ x :: y :: V) (P': ConvexPolygon $ y :: x :: V) (hS : P.triangulation = T :: T' :: S) (hS' : P'.triangulation = U :: U' :: S') : P.area = P'.area := by
  -- use induction on V and reduce to the parallelogram case
 sorry

lemma permuted_ConvexPolygon (P : ConvexPolygon V) (perm: V ~ V') : ConvexPolygon V' := by
  -- use induction
  sorry

theorem eq_area_of_perm_vertices (P : ConvexPolygon V) (P' : ConvexPolygon V') (perm: V ~ V') : P.area = P'.area := by
  set S := P.triangulation with ← hS
  set S' := P'.triangulation with ← hS'
  have lens := eq_number_of_triangles_of_perm P P' perm
  induction perm with
  | nil => exfalso; apply P.vertices_ne_nil; rfl
  | cons x h IH =>
    rename_i W W'
    match S, S' with
    | [], _ => exfalso; apply P.triangulation_ne_nil; exact hS
    | _, [] => exfalso; apply P'.triangulation_ne_nil; exact hS'
    | [T], _ :: _ :: _ => have := hS ▸ hS' ▸ lens; simp at this; contradiction
    | [T], [_] =>
        have := hS ▸ P.number_of_triangles_eq
        simp [ConvexPolygon.n] at this
        match W with
        | [] => simp at this
        | [_] => simp at this
        | [y, z] => exact eq_area_of_tri P P' $ h.cons x
    | T :: T' :: S'', [_] => have := hS ▸ hS' ▸ lens; simp at this
    | T :: T' :: S'', U :: U' :: S''' =>
        have C := hS ▸ P.convex; simp [convex_triangulation] at C
        have C' := hS' ▸ P'.convex; simp [convex_triangulation] at C'
        let PW := ConvexPolygon.mk (T' :: S'') C.1
        let PW' := ConvexPolygon.mk (U' :: S''') C'.1
        have : triangulation_area (T :: T' :: S'') = triangulation_area [T] + triangulation_area (T' :: S'') := by simp [triangulation_area]
        have hT: ConvexPolygon.area P = ConvexPolygon.area PW + triangulation_area [T] := by
          simp [ConvexPolygon.area, hS, this]; ring_nf
        have : triangulation_area (U :: U' :: S''') = triangulation_area [U] + triangulation_area (U' :: S''') := by simp [triangulation_area]
        have hU: ConvexPolygon.area P' = ConvexPolygon.area PW' + triangulation_area [U] := by
          simp [ConvexPolygon.area, hS', this]; ring_nf
        have : triangulation_area [T] = triangulation_area [U] := eq_area_of_eq_last_vertex P P' hS hS'
        rw [hT, hU, this]; simp [add_right_inj]; apply IH PW PW' (by rfl) (by rfl)
        simp [hS, hS', length_cons, Nat.succ.injEq, add_left_inj] at lens; simp [lens]
  | swap x y =>
      rename_i W
      match S, S' with
    | [], _ => exfalso; apply P.triangulation_ne_nil; exact hS
    | _, [] => exfalso; apply P'.triangulation_ne_nil; exact hS'
    | [T], _ :: _ :: _ => have := hS ▸ hS' ▸ lens; simp at this; contradiction
    | [T], [U] =>
        match W with
        | [] => have := hS ▸ P.number_of_triangles_eq; simp [ConvexPolygon.n] at this
        | [z] => exact eq_area_of_tri P P' $ Perm.swap x y [z]
        | _ :: _ :: _ => have := hS ▸ P.number_of_triangles_eq; simp [ConvexPolygon.n] at this; contradiction
    | T :: T' :: S'', [_] => have := hS ▸ hS' ▸ lens; simp at this
    | T :: T' :: S'', U :: U' :: S''' => exact eq_area_of_quadri_splits P P' hS hS'
  | trans perm' _ IH IH' =>
      let P'' := permuted_ConvexPolygon P perm'
      have lens' := eq_number_of_triangles_of_perm P P'' perm'
      exact Eq.trans (by apply IH P P'' hS.symm; rfl; rw [← lens']) (by apply IH' P'' P'; rfl; rfl ; rw [← lens, lens'])


#exit

def diff_quadri_splits (T U T' U' : Triangle) : Prop :=
  ∃ a b c d : point, ∃ V : List point, ∃ P : ConvexPolygon [a, b, c, d], ∃ P' : ConvexPolygon V,
  [a, b, c, d] ≠ V ∧ [a, b, c, d] ~ V ∧ P.triangulation = [T, U] ∧ P'.triangulation = [T', U']

lemma eq_area_of_quadri (P : ConvexPolygon [a, b, c, d]) (P' : ConvexPolygon V) (perm : [a, b, c, d] ~ V) : P.area = P'.area := by
  sorry

def eq_area_of_quadri_splits' (T U T' U' : Triangle) (splits : diff_quadri_splits T U T' U') :
    area T.a T.b T.c + area U.a U.b U.c = area T'.a T'.b T'.c + area U'.a U'.b U'.c := by
  obtain ⟨ a, b, c, d, V, P, P', _, perm, hP, hP' ⟩ := splits
  have := eq_area_of_quadri P P' perm
  convert this <;> simp [ConvexPolygon.area, triangulation_area, hP, hP']

def adj_triangulation (S : List Triangle) (S' : List Triangle) : Prop :=
  ∃ T U T' U' : Triangle, T ∈ S ∧ U ∈ S ∧ T' ∈ S' ∧ U' ∈ S' ∧
  diff_quadri_splits T U T' U' ∧ S.diff [T, U] ~ S'.diff [T', U'] ∧ (S.diff [T, U]) ≠ (S'.diff [T', U'])

lemma eq_area_of_perm_triangulation (S S' : List Triangle) (perm : S ~ S') : triangulation_area S = triangulation_area S' := by
  induction perm with
  | nil => rfl
  | cons _ _ IH => dsimp [triangulation_area]; rw [IH]
  | swap => dsimp [triangulation_area]; ring
  | trans _ _ _ _ => linarith

lemma triangulation_area_of_erase (S : List Triangle) (T : Triangle) (TS : T ∈ S) :
   triangulation_area S = triangulation_area (S.erase T) + triangulation_area [T] := by
  have := (@cons_perm_iff_perm_erase Triangle _ T (S.erase T) S).mpr ⟨TS, (by rfl)⟩
  have := eq_area_of_perm_triangulation S (T :: List.erase S T) this.symm
  rw [this]
  dsimp [TS, triangulation_area]
  linarith

lemma triangulation_area_of_diff (S : List Triangle) (T : Triangle) (TS : T ∈ S) :
   triangulation_area S = triangulation_area (S.diff [T]) + triangulation_area [T] := by
  simp [List.diff, TS]
  exact triangulation_area_of_erase S T TS

lemma triangulation_area_of_diff_two (S : List Triangle) (T U: Triangle) (TS : T ∈ S) (US : U ∈ S) (TU : T ≠ U) :
    triangulation_area S = triangulation_area (List.diff S [T, U]) + triangulation_area [T] + triangulation_area [U] := by
  have : U ∉ [T] := by intro x; exact TU (mem_singleton.mp x).symm
  have := mem_diff_of_mem US this; simp [List.diff, TS] at this
  simp [List.diff, elem_iff, ne_eq, TS, this]
  have := triangulation_area_of_erase _ U this
  ring_nf
  conv => rw [add_assoc, add_comm]; rhs; rw [add_assoc, add_comm]; lhs; rw [add_comm]; rw [← this]
  exact triangulation_area_of_erase _ T TS

lemma eq_area_of_adj_triangulation (P : ConvexPolygon V) (P' : ConvexPolygon V')
    (adj : adj_triangulation P.triangulation P'.triangulation) : P.area = P'.area := by
  obtain ⟨ T, U, T', U', TS, US, T'S', U'S', splits, perm, diff⟩ := adj
  have TU:  T ≠ U := by sorry
  have T'U' : T' ≠ U' := by sorry
  have hS := triangulation_area_of_diff_two P.triangulation T U TS US TU
  have hS' := triangulation_area_of_diff_two P'.triangulation T' U' T'S' U'S' T'U'
  simp [ConvexPolygon.area, hS, hS']
  dsimp [triangulation_area]; ring_nf
  have := eq_area_of_quadri_splits' T U T' U' splits
  conv => lhs; rw [add_assoc, this]
  conv => rhs; rw [add_assoc]
  simp
  have := eq_area_of_perm_triangulation (List.diff P.triangulation [T, U]) (List.diff P'.triangulation [T', U']) perm
  convert this <;> simp
