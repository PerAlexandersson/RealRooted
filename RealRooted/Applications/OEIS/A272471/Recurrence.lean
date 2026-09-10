import RealRooted.Mathlib.Algebra.LinearRecurrence.Annihilator
import Mathlib.Data.Real.Basic

/-!
# The A272471 evaluation recurrence

This opt-in client ports the defining polynomial recurrence for OEIS A272471.
Source: <https://github.com/sqrt-of-2/real-rooted-oeis-proofs>, commit
`d08b1579b1da5d9b7823a07941849cd34abf9c7c`, file `ProofsOeis/A272471.lean`.
It records only the algebraic recurrence after scalar evaluation; resultant
factorization and real root estimates remain separate work.
-/

namespace RealRooted.Applications.OEIS

open Polynomial

/-- The polynomial sequence underlying OEIS A272471. -/
noncomputable def a272471Polynomial : ℕ → ℝ[X]
  | 0 => 1 + X
  | 1 => 2 + 4 * X
  | 2 => 3 + 9 * X + X ^ 2
  | 3 => 4 + 18 * X + 7 * X ^ 2
  | n + 4 => 2 * a272471Polynomial (n + 3) + (-1 + X) * a272471Polynomial (n + 2) +
      (1 + X) * a272471Polynomial (n + 1) - a272471Polynomial n

/-- The scalar recurrence obtained from A272471 by evaluating at `x`. -/
def a272471EvalRecurrence (x : ℝ) : LinearRecurrence ℝ :=
  ⟨4, ![-1, 1 + x, x - 1, 2]⟩

/-- Evaluation of the A272471 polynomial recurrence solves its scalar
constant-coefficient recurrence. -/
theorem a272471_eval_isSolution (x : ℝ) :
    (a272471EvalRecurrence x).IsSolution (fun n ↦ (a272471Polynomial n).eval x) := by
  intro n
  unfold a272471EvalRecurrence
  simp only [Fin.sum_univ_four, Fin.isValue, Matrix.cons_val_zero, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, add_zero, neg_mul, one_mul, Matrix.cons_val_one, Nat.one_mod,
    Matrix.cons_val, Nat.reduceMod, Nat.mod_succ]
  rw [a272471Polynomial]
  simp only [eval_add, eval_sub, eval_mul, eval_X, eval_ofNat, eval_one, eval_neg]
  ring

/-- The characteristic polynomial of the A272471 scalar recurrence annihilates
the evaluated sequence under the forward shift. -/
theorem a272471_eval_aeval_charPoly_eq_zero (x : ℝ) :
    Polynomial.aeval LinearRecurrence.forwardShift (a272471EvalRecurrence x).charPoly
      (fun n ↦ (a272471Polynomial n).eval x) = 0 :=
  LinearRecurrence.isSolution_iff_aeval_charPoly_eq_zero _ _ |>.mp
    (a272471_eval_isSolution x)

end RealRooted.Applications.OEIS
