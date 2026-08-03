module

public import Mathlib.Data.List.Basic

/-!
# Additional basic list lemmas

This file contains compatibility lemmas intended for upstreaming to
`Mathlib.Data.List.Basic`.
-/

public section

namespace List

/-- Erasing an entry rejected by a filter does not change the filtered list. -/
theorem filter_eraseIdx_eq_of_getElem_not
    {α : Type*} {p : α → Bool} {l : List α} {i : ℕ}
    (hi : i < l.length) (hpi : ¬p l[i]) :
    (l.eraseIdx i).filter p = l.filter p := by
  rw [List.eraseIdx_eq_take_drop_succ, List.filter_append]
  conv_rhs =>
    rw [← List.take_append_drop i l, List.filter_append,
      List.drop_eq_getElem_cons hi, List.filter_cons_of_neg hpi]

end List
