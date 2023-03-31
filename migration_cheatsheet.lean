/-!

Here are some tips on migrating

* There are no ',' at the end of lines anymore!

* There are no 'begin' or 'end' anymore

* Indentation is important!

* 'by_contradiction' is now 'by_contra'

* You can no longer do
    have := blabla _ _
  instead, you need to do
    have' := blabla _ _
  or
    have := blabla ?_ ?_
  The same holds for refine.

* 'split' is now 'constructor'

* 'cases h : ha hb' is now
  cases h with
  | inl ha =>
    ...
  | inr hb =>
    ...

* 'induction n with n hn' is now
  induction n with
  | zero =>
    ...
  | succ n hn =>
    ...

* 'λ x, y' is now
  fun x => y

* 'rw x', 'rwa x', 'rw ← x', 'rwa ← x' is now
  rw [x], rwa [x], rw [← x], rwa [← x], respectively
  
* There doesn't seem to be squeeze_simp in mathlib4 yet.

-/
