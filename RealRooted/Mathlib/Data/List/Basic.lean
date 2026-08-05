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
  rw [eraseIdx_eq_take_drop_succ, filter_append]
  conv_rhs =>
    rw [← take_append_drop i l, filter_append,
      drop_eq_getElem_cons hi, filter_cons_of_neg hpi]

/-- Erasing an index inside the middle block of a three-block concatenation. -/
theorem eraseIdx_append_middle
    {α : Type*} (pre middle post : List α) (i : ℕ)
    (hi : i < middle.length) :
    (pre ++ middle ++ post).eraseIdx (pre.length + i) =
      pre ++ middle.eraseIdx i ++ post := by
  rw [append_assoc,
    eraseIdx_append_of_length_le (by simp),
    Nat.add_sub_cancel_left,
    eraseIdx_append_of_lt_length hi,
    append_assoc]

end List
