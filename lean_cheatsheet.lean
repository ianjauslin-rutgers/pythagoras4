/-!

This document lists recipes for what to do when faced with a proof in lean.

* ∧ in goal:
  If the goal is of the form 'a ∧ b', you can split the goal into two using
    constructor
  or, if you know a and b, use
    exact ⟨ a , b ⟩

* ∧ in hypothesis
  If a hypothesis h is of the form 'a ∧ b', you can extract 'a' with
    h.1
  and 'b' with
    h.2
  (not that if h is 'a ∧ b ∧ c', to get 'b', you have to use h.2.1.


* ∨ in goal
  If the goal is of the form 'a ∨ b', first prove a or b, then use
    left
  if you've proved a, or
    right
  if you've proved b.

* ∨ in hypothesis
  If a hypothesis h is of the form 'a ∨ b', then use
    cases h with
    | inl h =>
      -- what do to if a is true
    | inr h =>
      -- what to do if b is true



* ∃ in goal:
  If the goal is of the form '∃ x : ..., ...', specify 'x' using
    use x

* ∃ in hypothesis:
  If a hypothesis h is of the form '∃ x : ..., ...', 'x' can be extracted using
    cases h with x hx
  or
    obtain <x,hx> : h


* ∀ in goal:
  If the goal is of the form '∀ x : ..., ...', get 'x' with
    intro x

* ∀ in hypothesis:
  If a hypothesis h is of the form '∀ x : ..., ...', apply to an 'x' using
    h x


* Missing proofs of hypotheses:
  If you haven't proved all the hypotheses for a theorem, but still want to use
  the theorem, you can replace the missing hypotheses by
    ?_
  which will turn them into goals. This allows you to proceed with the proof
  and deal with the hypothesis later.
  To do this in an 'exact' statement, use
    refine
  instead of 'exact'


* Adding a statement to be proved later:
  In a similar vein as '?_', if you want to add a hypothesis h that you will
  prove later, use
    suffices h


* Simplification:
  Lean can simplify expressions using the 'simp' tactic. To simplify the
  goal, use
    simp
  to simplify a hypothesis h, use
    simp at h
  You can also instruct simp to use a hypothesis k with
    simp [k]
  Finally, you can instruct simp to only use what it needs with
    simp only [...]
  
  If you use 'simp', you can get lean to tell you what simp used, and replace
  it with a 'simp only' using
    squeeze_simp
  (not yet supported in lean4)


* Rewriting:
  Lean can rewrite goals and hypothesis with the 'rw' tactic. 'rw' takes
  equalities or iff statements and replaces occurrences in goals or hypothesis.
  To rewrite the goal, use
    rw [...]
  to rewrite a hypothesis h, use
    rw [...] at h
  You can chain rw's with
    rw [h1,h2,...]
  You can also rewrite in several hypotheses at once:
    rw [..] at h1 h2 ...


* Problems with coercions (↑):
  When running into issues with coercions (e.g. treating a ℚ as a ℝ),
  'norm_cast' will sometimes help by ensuring that your various variables are
  coerced in the same way.


* If/then statements:
  To write a proof of the form 'if h, then ...', use
    by_cases : h
    · ...
  which will create two goals: one assuming h and the other assuming ¬h.
  (the '·' is actually syntactically required)


* Proof by contradiction:
  To carry out a proof by contradiction, use
    by_contra contra
  This will create a hypothesis contra which is ¬ goal.


* Induction:
  To prove something inductively, use
    induction n with
    | zero =>
      ...
    | succ n hn =>
      ...
  which will set up an induction on n. hn will be the inductive hypothesis.


* Simplifications involving division:
  If, for instance, you want to prove 'a=b' and you know '2*a=2*b', then use
    field_simp


* Changing the order of goals:
  If you want to change the order of the goals, say, move the n-th goal to the
  front, use
    swap n
  (by default, swap brings the second goal to the front).


* Changing the order of variables in an (in)equality:
  To get 'b = a' from h: 'a = b', use
    h.symm


* Changing the negation of an equality to an inquality (e.g., after 'by_ cases'):
  To get 'a ≠ b' from h: ¬ a = b, use
    rw [← Ne.def a b] at h

* To close a logical goal with sufficient hypotheses:
    tauto


** How to type that symbol?
  \ : \\
  ∃ : \exists or \ex
  ∀ : \forall or \all
  ≠ : \ne or \neq or \eqn or \=n
  ⟨ : \bra or \< or \langle
  ⟩ : \> or \rangle
  ⊢ : \vdash or \|- or \entails
  ⊥ : \bot or \perp
  ⊤ : \top
  ⊣ : \dashv or \-|
  ℝ : \R or \Bbb{R} or \real or \Real or \br or \bbR
  ℚ : \Q or \Bbb{Q} or \rat or \Rat or \bq or \bbQ
  ℤ : \Z or \Bbb{Z} or \int or \Int or \bz or \bbZ
  ℕ : \N or \Bbb{N} or \nat or \Nat or \bn or \bbN
  → : \to or \imp ot \-> or \rightarrow or \r or \r-
  ← : \l or \l- or \<- or \gets or \leftarrow
  ↔ : \iff or \lr or \lr- \<-> or \leftrightarrow
  ↑ : \u or \uparrow or \u-
  ⇑ : \u= or \Uparrow
  ∈ : \in or \mem or \member
  ∋ : \ni
  ⊆ : \sub or \subseteq or \subseteqq
  ⊊ : \subsetneq or \subsetneqq
  ⊇ : \sup or \supseteq or \supseteqq
  ⊋ : \supsetneq or \supsetneqq
  ∩ : \i or \cap or \intersection
  ∪ : \un or \cap or \union
  ∧ : \and or \wedge
  ∨ : \or or \vee
  ≥ : \ge or \>= or \geqslant or \geq
  ≤ : \le or \<= or \leqslant or \leq
  ¬ : \not or \neg or \lnot
  ∫ : \integral
  ∂ : \partial
  ∘ : \o or \comp or \circ
  • : \bu or \bub
  ⦃ : \{{
  ⦄ : \}}
  ⟦ : \[[
  ⟧ : \]]
  ∥ : \|| or \parallel or \shortparallel
  ∅ : \empty or \emptyset
  ≃ : \simeq or \~- or \equiv
  ≅ : \cong or \~= or \iso
  ≡ : \==
  ≡ : \==
  ≄ : \~-n or \nsimeq
  ≇ : \ncong or \~=n
  ≢ : \nequiv or \==n
  ≁ : \nsim or \~n
  · : \.
  
  subscript : \_...
  superscript : \^...
  greek letters: \alpha, \beta, etc... or \Ga, \Gb, etc...


-/
