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
  calc
    (l.eraseIdx i).filter p =
        (l.take i ++ l.drop (i + 1)).filter p := by
      rw [List.eraseIdx_eq_take_drop_succ]
    _ = (l.take i ++ l[i] :: l.drop (i + 1)).filter p := by
      simp only [List.filter_append, List.filter_cons_of_neg hpi]
    _ = l.filter p := by
      rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]

end List
