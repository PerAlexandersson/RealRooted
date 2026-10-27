module

public import RealRooted.DerivativeRecurrence.SecondDerivativeDegree
public import RealRooted.EulerOperator.Polar.Pencil
public import RealRooted.EulerOperator

/-!
# Euler factorization for second-derivative recurrences

Target module: `RealRooted.DerivativeRecurrence.SecondOrder.Top`.

This is the nonduplicated operator core of the downstream
`ProofsOeis/SecondDerivativeTop.lean`. The coefficient and degree theory is
already in `DerivativeRecurrence.SecondDerivativeDegree`, and the former
`EulerPencil.lean` results now live in the `EulerOperator`, `ReciprocalShift`,
and `Wronskian` directories. The original downstream development is by Per
Alexandersson and the ProofsOeis/Claude Code contributors for issue #1061.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The lag-two differential expression is the Euler-operator composition
`(n + 1 - theta) (theta + 1)`. -/
def secondDerivativeLagCore (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  polarTheta (n + 1) (thetaPlusOne p)

/-- Differential expansion of `secondDerivativeLagCore`. -/
lemma secondDerivativeLagCore_eq (n : ℕ) (p : ℝ[X]) :
    secondDerivativeLagCore n p =
      C ((n : ℝ) + 1) * p +
        C ((n : ℝ) - 1) * (X * p.derivative) -
          X ^ 2 * p.derivative.derivative := by
  unfold secondDerivativeLagCore polarTheta thetaPlusOne theta
  simp only [derivative_add, derivative_mul, derivative_X, one_mul]
  grind

/-- The lag core preserves Pólya frequency polynomials in its degree box. -/
theorem secondDerivativeLagCore_isPF
    {n : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ n) :
    IsPFPolynomial (secondDerivativeLagCore n p) := by
  unfold secondDerivativeLagCore
  apply polarTheta_preserves_pf (thetaPlusOne_preserves_pf hp)
  have hthetaDegree : (thetaPlusOne p).natDegree ≤ p.natDegree := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_thetaPlusOne, coeff_eq_zero_of_natDegree_lt hk]
    ring
  grind

/-- A nonnegative scalar and one factor of `X` preserve the PF lag core. -/
theorem secondDerivativeLagBranch_isPF
    {n : ℕ} {p : ℝ[X]} {b : ℝ} (hb : 0 ≤ b)
    (hp : IsPFPolynomial p) (hdeg : p.natDegree ≤ n) :
    IsPFPolynomial (C b * X * secondDerivativeLagCore n p) := by
  by_cases hb0 : b = 0
  · simpa only [hb0, map_zero, zero_mul] using IsPFPolynomial.zero
  · simpa only [mul_assoc] using
      IsPFPolynomial.const_mul (lt_of_le_of_ne hb (Ne.symm hb0))
        (secondDerivativeLagCore_isPF hp hdeg).X_mul

/-- The positive second-derivative recurrence is a sum of a current-row
Euler branch and a PF-preserving lag core. -/
lemma secondDerivative_recurrence_factored
    {P : ℕ → ℝ[X]} {b : ℝ}
    (hrec : IsSecondDerivativeFamilyRecurrence P b) (n : ℕ) :
    P (n + 2) =
      (C 1 + C (b + 1 + b * (n : ℝ)) * X) * P (n + 1) +
        C b * X * (1 - X) * (P (n + 1)).derivative +
        C b * X * secondDerivativeLagCore n (P n) := by
  rw [hrec n]
  apply Polynomial.funext
  intro r
  rw [secondDerivativeLagCore_eq]
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_one,
    eval_pow]
  ring

end RealRooted
