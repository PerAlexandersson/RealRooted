module

public import RealRooted.Applications.OEIS.A056939
public import RealRooted.Interlacing.Euclid
public import RealRooted.Recurrence.Uniqueness
public import RealRooted.Recurrence.RowModel

set_option rr.row.explain true
set_option linter.style.longLine false

@[expose] public section

open RealRooted Polynomial

/-!
# The A359363 model

Apart from its initial row, this family is `X` times the preceding A056939 row.
-/

noncomputable section

namespace RealRooted.Applications.OEIS.A359363

/-- The positive denominator in the A359363 update. -/
def denominator (n : ℕ) : ℝ :=
  (11 / 2) + (1 / 2) * (3 + (n : ℝ)) ^ 2 + (3 / 2) * (n : ℝ)

/-- The lag-two recurrence operator for A359363. -/
def nextRow (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  (C ((1 / denominator n) * ((21 / 2) + (9 / 2) * (n : ℝ))) * X +
      C ((1 / denominator n) * ((-21 / 2) + (-9 / 2) * (n : ℝ))) * X ^ 2) *
      p.derivative +
    (C ((1 / denominator n) *
        (4 + 2 * (n : ℝ) + (-1 / 2) * (3 + (n : ℝ)) ^ 2)) +
      C ((1 / denominator n) *
        ((-31 / 2) + 4 * (3 + (n : ℝ)) ^ 2 + (-11 / 2) * (n : ℝ))) * X) * p +
    (C ((1 / denominator n) *
        (-9 + (3 + (n : ℝ)) ^ 2 + (-5 * (n : ℝ)))) +
      C ((1 / denominator n) *
        (-18 + (-10 * (n : ℝ)) + 2 * (3 + (n : ℝ)) ^ 2)) * X +
      C ((1 / denominator n) *
        (-9 + (3 + (n : ℝ)) ^ 2 + (-5 * (n : ℝ)))) * X ^ 2) * q

/-- The recurrence model for A359363. -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => nextRow n (polynomial (n + 1)) (polynomial n)

private theorem polynomial_succ_eq_X_mul :
    ∀ n : ℕ, polynomial (n + 1) = X * A056939.polynomial n
  | 0 => by
      rw [show polynomial 1 = X from rfl, show A056939.polynomial 0 = 1 from rfl]
      ring
  | 1 => by
      apply Polynomial.funext
      intro r
      simp only [polynomial, nextRow, denominator, A056939.polynomial,
        derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_one, eval_pow]
      norm_num
      ring
  | n + 2 => by
      rw [show polynomial (n + 3) =
          nextRow (n + 1) (polynomial (n + 2)) (polynomial (n + 1)) by rfl]
      rw [polynomial_succ_eq_X_mul (n + 1), polynomial_succ_eq_X_mul n]
      rw [show A056939.polynomial (n + 2) =
          A056939.nextRow n (A056939.polynomial (n + 1))
            (A056939.polynomial n) by rfl]
      apply Polynomial.funext
      intro r
      simp only [nextRow, denominator, A056939.nextRow, A056939.denominator,
        derivative_mul, derivative_X, one_mul, eval_add, eval_mul, eval_C,
        eval_X, eval_pow, Nat.cast_add, Nat.cast_one]
      field_simp
      ring

/-- Every A359363 model row splits over the reals. -/
theorem polynomial_splits (n : ℕ) : (polynomial n).Splits := by
  cases n with
  | zero => simp [polynomial]
  | succ n =>
      rw [polynomial_succ_eq_X_mul]
      exact Polynomial.Splits.X.mul (A056939.polynomial_splits n)

/-- Consecutive A359363 model rows are in directed proper position. -/
theorem polynomial_strictInterl_succ (n : ℕ) :
    StrictInterl (polynomial n) (polynomial (n + 1)) := by
  cases n with
  | zero => simpa [polynomial] using strictInterl_X_pow_succ 0
  | succ n =>
      rw [polynomial_succ_eq_X_mul n, polynomial_succ_eq_X_mul (n + 1)]
      exact (A056939.polynomial_strictInterl_succ n).mul_common_factor
        Polynomial.X_ne_zero Polynomial.Splits.X

/-- Consecutive A359363 model rows interlace. -/
theorem polynomial_interlaces (n : ℕ) :
    Interlaces (polynomial n) (polynomial (n + 1)) := by
  cases n with
  | zero =>
      apply interlaces_of_natDegree_eq_zero_of_natDegree_eq_one
      · norm_num [polynomial]
      · simp only [polynomial, natDegree_one]
      · simp only [polynomial, natDegree_X]
  | succ n =>
      rw [polynomial_succ_eq_X_mul n, polynomial_succ_eq_X_mul (n + 1)]
      exact (A056939.polynomial_interlaces n).mul_both_of_splits
        Polynomial.Splits.X Polynomial.X_ne_zero

/-- A sequence with the A359363 initial rows and update has split rows. -/
@[rr_row_model]
theorem splits_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = X)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    (P n).Splits := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hzero.trans (show (1 : ℝ[X]) = polynomial 0 by rfl))
    (hone.trans (show X = polynomial 1 by rfl))
    hrec (fun _ => rfl)
  rw [heq n]
  exact polynomial_splits n

/-- A sequence with the A359363 initial rows and update has interlacing
consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = X)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (hzero.trans (show (1 : ℝ[X]) = polynomial 0 by rfl))
    (hone.trans (show X = polynomial 1 by rfl))
    hrec (fun _ => rfl)
  rw [heq n, heq (n + 1)]
  exact polynomial_interlaces n

end RealRooted.Applications.OEIS.A359363
