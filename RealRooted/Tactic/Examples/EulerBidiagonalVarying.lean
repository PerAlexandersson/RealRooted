module

import RealRooted.EulerBidiagonal.VaryingRows

/-!
# Varying Euler bidiagonal row regression

The parameter pairs `(1, 5)` and `(2, 4)` alternate: their sum stays six and their
product oscillates between five and eight.
-/

open Polynomial

namespace RealRooted

example (n : ℕ) :
    let a : ℕ → ℝ := fun m => if Even m then 1 else 2
    let b : ℕ → ℝ := fun m => 6 - a m
    let F := EulerBidiagonal.rowsVar a b
    IsNegativeSimple (F n) ∧ (F n).natDegree = n ∧
      StrictInterl (F n) (F (n + 1)) ∧
      ∀ r, ¬ ((F n).IsRoot r ∧ (F (n + 1)).IsRoot r) := by
  let a : ℕ → ℝ := fun m => if Even m then 1 else 2
  have ha : ∀ m, 0 ≤ a m := by
    intro m
    dsimp [a]
    split <;> norm_num
  have hb : ∀ m, 0 ≤ 6 - a m := by
    intro m
    dsimp [a]
    split <;> norm_num
  have hab : ∀ m, 0 < a m * (6 - a m) := by
    intro m
    dsimp [a]
    split <;> norm_num
  exact ⟨EulerBidiagonal.isNegativeSimple_rowsVar ha hb hab n,
    EulerBidiagonal.natDegree_rowsVar ha hb hab n,
    EulerBidiagonal.strictInterl_rowsVar_succ ha hb hab (fun m => by simp) n⟩

end RealRooted
