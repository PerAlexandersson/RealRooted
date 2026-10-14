import RealRooted.CombinatorialExamples.CentralFactorial
import RealRooted.Interlacing.Reversal
import RealRooted.Recurrence.RowModel

/-!
# Reflected Euler-bidiagonal rows

Reversing the degree-`n` Euler-bidiagonal row changes its coefficient update into a
second-order derivative recurrence depending on `n`. This module packages that identity and
registers the two classical integer specializations used by A008957 and A191935.
-/

open Polynomial

noncomputable section

namespace RealRooted.ReflectedEulerRows

/-- The recurrence step obtained by reflecting the degree-`n` Euler-bidiagonal row. -/
def nextRow (a b : ℝ) (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  X ^ 3 * p.derivative.derivative +
    C (1 - 2 * (n : ℝ) - a - b) * X ^ 2 * p.derivative +
      p + C (((n : ℝ) + a) * ((n : ℝ) + b)) * X * p

/-- The reflected Euler-bidiagonal rows, defined directly by their derivative recurrence. -/
def rows (a b : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => nextRow a b n (rows a b n)

private theorem reflect_two_C_mul_X_sq (c : ℝ) :
    reflect 2 (C c * X ^ 2) = C c := by
  rw [Polynomial.reflect_C_mul_X_pow]
  simp

private theorem reflect_one_one_add_C_mul_X (c : ℝ) :
    reflect 1 (1 + C c * X) = C c + X := by
  rw [show (1 + C c * X : ℝ[X]) = C 1 * X ^ 0 + C c * X ^ 1 by
      simp only [pow_zero, pow_one, mul_one, C_1],
    Polynomial.reflect_add, Polynomial.reflect_C_mul_X_pow,
    Polynomial.reflect_C_mul_X_pow]
  simp only [Polynomial.revAt_le (by lia : 0 ≤ 1),
    Polynomial.revAt_le (by lia : 1 ≤ 1)]
  norm_num
  simp only [add_comm]

private theorem rows_eq_reflect_eulerRows {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a * b) :
    ∀ n, rows a b n = reflect (0 + n) (EulerBidiagonal.rows a b n) := by
  apply eq_reflect_of_secondOrderDerivativeRecurrence
    (P := rows a b) (R := EulerBidiagonal.rows a b)
    (D₀ := 0)
    (A₂ := fun _ => X ^ 3)
    (A₁ := fun n => C (1 - 2 * (n : ℝ) - a - b) * X ^ 2)
    (A₀ := fun n => 1 + C (((n : ℝ) + a) * ((n : ℝ) + b)) * X)
    (B₂ := fun _ => X ^ 2)
    (B₁ := fun _ => C (a + b + 1) * X)
    (B₀ := fun _ => C (a * b) + X)
  · intro n
    rw [rows, nextRow]
    ring
  · intro n
    rw [EulerBidiagonal.rows, EulerBidiagonal.step_eq_second_derivative]
  · intro n
    compute_degree!
  · intro n
    compute_degree!
  · intro n
    compute_degree!
  · intro n
    simp
  · intro n
    rw [show reflect 3 (X ^ 3 : ℝ[X]) = 1 by simp,
      show reflect 2 (C (1 - 2 * (n : ℝ) - a - b) * X ^ 2) =
          C (1 - 2 * (n : ℝ) - a - b) by
            exact reflect_two_C_mul_X_sq _]
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_neg, eval_X, eval_C, eval_one]
    ring_nf
  · intro n
    rw [show reflect 3 (X ^ 3 : ℝ[X]) = 1 by simp,
      show reflect 2 (C (1 - 2 * (n : ℝ) - a - b) * X ^ 2) =
          C (1 - 2 * (n : ℝ) - a - b) by
            exact reflect_two_C_mul_X_sq _,
      show reflect 1 (1 + C (((n : ℝ) + a) * ((n : ℝ) + b)) * X) =
          C (((n : ℝ) + a) * ((n : ℝ) + b)) + X by
            exact reflect_one_one_add_C_mul_X _]
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_X, eval_C, eval_one]
    ring_nf
  · intro n
    simpa only [zero_add] using (EulerBidiagonal.isNegativeSimple_rows ha hb hab n).2.le
  · simp [rows, EulerBidiagonal.rows]

private theorem eulerRows_hasNonnegCoeffs {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a * b) (n : ℕ) :
    HasNonnegCoeffs (EulerBidiagonal.rows a b n) := by
  have h := (EulerBidiagonal.isNegativeSimple_rows ha hb hab n).1
  exact ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos h.2.1).2
    ⟨h.2.2.2.1, fun r hr => (h.2.2.2.2 r hr).le⟩).1

private theorem eulerRows_coeff_zero_pos {a b : ℝ}
    (hab : 0 < a * b) (n : ℕ) :
    0 < (EulerBidiagonal.rows a b n).coeff 0 := by
  induction n with
  | zero => simp [EulerBidiagonal.rows]
  | succ n ih =>
      rw [EulerBidiagonal.rows, EulerBidiagonal.coeff_step]
      simp only [Nat.cast_zero, zero_add, ite_true, add_zero]
      exact mul_pos hab ih

/-- Reflected Euler-bidiagonal rows interlace for nonnegative parameters with positive
product. -/
theorem interlaces_rows {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a * b)
    (n : ℕ) : Interlaces (rows a b n) (rows a b (n + 1)) := by
  have hforwardDegree : ∀ m, (EulerBidiagonal.rows a b m).natDegree = 0 + m :=
    fun m => by simpa only [zero_add] using
      (EulerBidiagonal.isNegativeSimple_rows ha hb hab m).2
  have hreflectedDegree : ∀ m, (rows a b m).natDegree = 0 + m := fun m => by
    rw [rows_eq_reflect_eulerRows ha hb hab m]
    exact DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne
      (by rw [hforwardDegree m]) (eulerRows_coeff_zero_pos hab m).ne'
  have hreflectedPos : ∀ m, 0 < (rows a b m).leadingCoeff := fun m => by
    rw [rows_eq_reflect_eulerRows ha hb hab m,
      DegreeDropReversal.leadingCoeff_reflect_eq_coeff_zero_of_natDegree_le
        (by rw [hforwardDegree m]) (eulerRows_coeff_zero_pos hab m).ne']
    exact eulerRows_coeff_zero_pos hab m
  apply interlaces_of_eq_reflect (D₀ := 0) (rows_eq_reflect_eulerRows ha hb hab)
    hforwardDegree (eulerRows_hasNonnegCoeffs ha hb hab) hreflectedDegree hreflectedPos
  intro m
  exact (EulerBidiagonal.strictInterl_rows ha hb hab m).1.toInterlaces (by
    rw [hforwardDegree m, hforwardDegree (m + 1)]
    simp only [zero_add])

/-- Any sequence satisfying the reflected central-factorial recurrence has interlacing
consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_centralFactorial_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 1) = nextRow 1 1 n (P n))
    (n : ℕ) : Interlaces (P n) (P (n + 1)) := by
  have heq : ∀ m, P m = rows 1 1 m := by
    intro m
    induction m with
    | zero => exact hzero.trans (show (1 : ℝ[X]) = rows 1 1 0 by rfl)
    | succ m ih =>
        rcases Nat.eq_zero_or_pos m with rfl | _
        · exact hone.trans (by norm_num [rows, nextRow, map_ofNat])
        · rw [hrec, rows, ih]
  rw [heq n, heq (n + 1)]
  exact interlaces_rows (by norm_num) (by norm_num) (by norm_num) n

/-- Any sequence satisfying the reflected Legendre--Stirling recurrence has interlacing
consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_legendreStirling_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + 2 * X)
    (hrec : ∀ n, P (n + 1) = nextRow 1 2 n (P n))
    (n : ℕ) : Interlaces (P n) (P (n + 1)) := by
  have heq : ∀ m, P m = rows 1 2 m := by
    intro m
    induction m with
    | zero => exact hzero.trans (show (1 : ℝ[X]) = rows 1 2 0 by rfl)
    | succ m ih =>
        rcases Nat.eq_zero_or_pos m with rfl | _
        · exact hone.trans (by norm_num [rows, nextRow, map_ofNat])
        · rw [hrec, rows, ih]
  rw [heq n, heq (n + 1)]
  exact interlaces_rows (by norm_num) (by norm_num) (by norm_num) n

end RealRooted.ReflectedEulerRows
