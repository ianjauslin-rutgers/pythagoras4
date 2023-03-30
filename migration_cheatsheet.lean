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

* 'split' is now 'constructor'

* 'cases h : ha hb' is now
  cases h with
  | inl ha =>
    ...
  | inr hb =>
    ...

-/
