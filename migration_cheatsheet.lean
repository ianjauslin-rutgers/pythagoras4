/-!

Here are some tips on migrating

* There are no ',' anymore!

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

* There doesn't seem to be squeeze_simp in mathlib4 yet.

-/
