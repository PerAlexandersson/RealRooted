module

public import Mathlib.Data.List.OfFn

/-!
# Additional lemmas about lists of finite functions

This file contains compatibility lemmas intended for upstreaming to
`Mathlib.Data.List.OfFn`.
-/

public section

namespace List

/-- Removing a finite-function coordinate agrees with erasing that list index. -/
theorem ofFn_succAbove_eq_eraseIdx
    {α : Type*} {n : ℕ}
    (f : Fin (n + 1) → α) (p : Fin (n + 1)) :
    List.ofFn (fun i : Fin n => f (p.succAbove i)) =
      (List.ofFn f).eraseIdx p := by
  apply List.ext_getElem
  · simp [List.length_eraseIdx, p.isLt]
  · intro i hi₁ hi₂
    simp only [List.getElem_ofFn, List.getElem_eraseIdx]
    split
    · rw [Fin.succAbove_of_castSucc_lt p _ (by
        change i < (p : ℕ)
        exact ‹i < (p : ℕ)›)]
      congr
    · rw [Fin.succAbove_of_le_castSucc p _ (by
        change (p : ℕ) ≤ i
        exact Nat.le_of_not_gt ‹¬i < (p : ℕ)›)]
      congr

end List
