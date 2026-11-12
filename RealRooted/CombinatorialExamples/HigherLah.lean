module

public import RealRooted.EulerBidiagonal.VaryingRows

/-!
# Lah polynomials of higher level two

The Lah number of higher level two `T(n,k)` counts ordered pairs of partitions of `[n]`
into `k` lists with the same block minima; see Aleks Žigon Tankosič,
*The Lah Numbers with Higher Level and the Lah Numbers of Order s*,
[arXiv:2510.26842](https://arxiv.org/abs/2510.26842).

The coefficients satisfy `T(n+1,k) = T(n,k-1) + (n+k)² T(n,k)`, starting with `P₀ = 1`.
Removing the common factor `X` from `P(n+1)` gives the varying Euler parameters
`a m = b m = m + 2`. Thus the reduced rows have simple negative roots and consecutive
reduced rows strictly interlace without common roots.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.HigherLah

/-- The higher-level-two Lah row polynomials, starting with `P₀ = 1`. -/
def polynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => EulerBidiagonal.step (n : ℝ) (n : ℝ) (polynomial n)

/-- The defining higher-level-two Lah coefficient recurrence. -/
theorem coeff_polynomial_succ (n k : ℕ) :
    (polynomial (n + 1)).coeff k =
      ((n : ℝ) + k) ^ 2 * (polynomial n).coeff k +
        if k = 0 then 0 else (polynomial n).coeff (k - 1) := by
  rw [polynomial, EulerBidiagonal.coeff_step]
  ring

/-- The reduced Lah polynomial `P(n+1) / X`. -/
def reducedPolynomial (n : ℕ) : ℝ[X] :=
  EulerBidiagonal.rowsVar (fun m => (m : ℝ) + 2) (fun m => (m : ℝ) + 2) n

/-- All positive-index Lah rows have the expected common factor `X`. -/
theorem polynomial_succ (n : ℕ) : polynomial (n + 1) = X * reducedPolynomial n := by
  induction n with
  | zero => simp [polynomial, reducedPolynomial, EulerBidiagonal.rowsVar,
      EulerBidiagonal.step, theta]
  | succ n ih =>
      rw [polynomial, ih, EulerBidiagonal.step_X_mul]
      simp only [reducedPolynomial, EulerBidiagonal.rowsVar, Nat.cast_add, Nat.cast_one]
      congr 2 <;> ring

/-- Monic division by `X` recovers the reduced row. -/
theorem polynomial_divByMonic_X (n : ℕ) : polynomial (n + 1) /ₘ X = reducedPolynomial n := by
  rw [polynomial_succ, mul_divByMonic_cancel_left _ monic_X]

/-- Every reduced Lah row is negative-simple. -/
theorem isNegativeSimple_reducedPolynomial (n : ℕ) :
    IsNegativeSimple (reducedPolynomial n) :=
  EulerBidiagonal.isNegativeSimple_rowsVar (fun m => by positivity)
    (fun m => by positivity) (fun m => by positivity) n

/-- Every reduced Lah row has degree equal to its index. -/
theorem natDegree_reducedPolynomial (n : ℕ) : (reducedPolynomial n).natDegree = n :=
  EulerBidiagonal.natDegree_rowsVar (fun m => by positivity)
    (fun m => by positivity) (fun m => by positivity) n

/-- Consecutive reduced Lah rows interlace without common roots. -/
theorem strictInterl_reducedPolynomial_succ (n : ℕ) :
    StrictInterl (reducedPolynomial n) (reducedPolynomial (n + 1)) ∧
      ∀ r, ¬ ((reducedPolynomial n).IsRoot r ∧ (reducedPolynomial (n + 1)).IsRoot r) := by
  exact EulerBidiagonal.strictInterl_rowsVar_succ (fun m => by positivity)
    (fun m => by positivity) (fun m => by positivity) (fun m => by push_cast; linarith) n

end RealRooted.HigherLah
