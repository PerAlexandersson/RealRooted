module

import RealRooted.EulerBidiagonal.GeneralRows
import RealRooted.Recurrence.RowModel
import RealRooted.WagnerX.ListInterlacing
import RealRooted.Linear
public import RealRooted.Basic.ProperPosition

/-!
# The A304334 Euler-bidiagonal model

After the forced factor `X` is removed, the A304334 recurrence is the general
Euler-bidiagonal step with parameters `(κ, a, b, u, v) = (1, 1, 1, 6, 4)`.
Its comparison defect is strictly negative on the nonpositive half-line, so
the general row theorem gives adjacent strict interlacing.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A304334

open EulerBidiagonal

private abbrev dividedRows : ℕ → ℝ[X] :=
  generalRows 1 1 1 6 4

private lemma comparisonDefect_neg (t : ℝ) (_ : t ≤ 0) :
    comparisonDefect 1 1 1 6 4 t < 0 := by
  dsimp [comparisonDefect]
  nlinarith [sq_nonneg t]

private lemma recurrence_step_X_mul (p : ℝ[X]) :
    X ^ 2 * (X * p).derivative.derivative +
          (X + 4 * X ^ 2) * (X * p).derivative + 2 * X * (X * p) =
      X * generalStep 1 1 1 6 4 p := by
  rw [generalStep_eq_second_derivative]
  simp only [derivative_mul, derivative_X, one_mul, map_add, map_one, C_ofNat]
  ring

private theorem strictInterl_dividedRows_succ (n : ℕ) :
    StrictInterl (dividedRows n) (dividedRows (n + 1)) := by
  exact (strictInterl_generalRows 1 1 1 6 4 (by norm_num) (by norm_num)
    (by norm_num) (fun k => by positivity) comparisonDefect_neg n).1

private theorem dividedRows_roots_nonpos (n : ℕ) :
    ∀ r ∈ (dividedRows n).roots, r ≤ 0 := by
  intro r hr
  have hsimple :=
    (isNegativeSimple_generalRows 1 1 1 6 4 (by norm_num) (by norm_num)
      (by norm_num) (fun k => by positivity) comparisonDefect_neg n).1
  exact (hsimple.2.2.2.2 r hr).le

/-- A sequence with the A304334 base rows and recurrence has interlacing
consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = X)
    (htwo : P 2 = X + 6 * X ^ 2)
    (hrec : ∀ n : ℕ,
      P (n + 2) =
        X ^ 2 * (P (n + 1)).derivative.derivative +
          (X + 4 * X ^ 2) * (P (n + 1)).derivative +
          2 * X * P (n + 1))
    (n : ℕ) : Interlaces (P n) (P (n + 1)) := by
  have heq : ∀ m : ℕ, P (m + 1) = X * dividedRows m := by
    intro m
    induction m with
    | zero => simpa only [dividedRows, generalRows, mul_one] using hone
    | succ m ih =>
        rcases m with _ | m
        · exact htwo.trans (by
            norm_num [dividedRows, generalRows, generalStep, theta, map_ofNat]
            ring)
        · rw [hrec, ih, recurrence_step_X_mul]
          rfl
  cases n with
  | zero =>
      rw [hzero, hone]
      exact interlaces_one_linear (p := (X : ℝ[X])) natDegree_X
  | succ n =>
      rw [heq n, heq (n + 1)]
      have hstrict : StrictInterl (X * dividedRows n) (X * dividedRows (n + 1)) :=
        by simpa using (strictInterl_dividedRows_succ n).mul_X_sub_C_both 0
      apply hstrict.toInterlaces
      have hspec :=
        isNegativeSimple_generalRows 1 1 1 6 4 (by norm_num) (by norm_num)
          (by norm_num) (fun k => by positivity) comparisonDefect_neg
      rw [natDegree_mul X_ne_zero (hspec n).1.1,
        natDegree_mul X_ne_zero (hspec (n + 1)).1.1,
        natDegree_X, (hspec n).2, (hspec (n + 1)).2]
      lia

end RealRooted.Applications.OEIS.A304334
