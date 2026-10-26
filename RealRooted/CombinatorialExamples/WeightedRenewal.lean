module

public import RealRooted.CombinatorialExamples.PathPowerClique

/-!
# Rigid renewal polynomials

We formalize the rigid specialization of the weighted-renewal family from
[RealRooted issue #2037](https://github.com/PerAlexandersson/RealRooted/issues/2037).
For `d, ℓ ≥ 1`, coefficient extraction from

`1 / (1 - x * (1 + t * x ^ ℓ) ^ d)`

gives the polynomial

`P n = ∑ j, choose (d * (n - ℓ * j)) j * t ^ j`.

We identify it with a sampled path-power polynomial.  The fixed-delay window
from Fisk, Example 16.10, as generalized in `RealRooted.Interlacing.VariableDelay`,
then gives interlacing whenever `d * s ≤ d * ℓ + 1`.
-/

@[expose] public section

open Finset Polynomial

noncomputable section

namespace RealRooted

/-- The coefficient polynomial extracted from
`1 / (1 - x * (1 + t * x ^ ℓ) ^ d)`.

The truncated subtraction is harmless for `ℓ ≥ 1`: the coefficient theorem below
proves explicitly that every summand outside the nonnegative-index range vanishes. -/
def rigidRenewalPolynomial (d ℓ n : ℕ) : ℝ[X] :=
  ∑ j ∈ range (n + 1), C (((d * (n - ℓ * j)).choose j : ℕ) : ℝ) * X ^ j

/-- Coefficients of the rigid renewal polynomial.  In the out-of-range case
`n < ℓ * j`, the proof reduces the upper binomial index to zero before using
that `j > 0`; thus no negative index is represented by truncated subtraction. -/
@[simp]
theorem coeff_rigidRenewalPolynomial (d ℓ n j : ℕ) (hℓ : 1 ≤ ℓ) :
    (rigidRenewalPolynomial d ℓ n).coeff j =
      ((d * (n - ℓ * j)).choose j : ℕ) := by
  simp only [rigidRenewalPolynomial, finsetSum_coeff, coeff_C_mul_X_pow,
    Finset.sum_ite_eq, mem_range]
  split_ifs with hj
  · norm_cast
  · have hnj : n < j := by lia
    have hjℓ : j ≤ ℓ * j := by
      simpa [one_mul] using Nat.mul_le_mul_right j hℓ
    have hsub : n - ℓ * j = 0 := Nat.sub_eq_zero_of_le (by lia)
    rw [hsub, mul_zero, Nat.choose_eq_zero_of_lt (by lia), Nat.cast_zero]

/-- The rigid renewal polynomial is a sampled path-power polynomial.  This is
the compression identity used in
[RealRooted issue #2037](https://github.com/PerAlexandersson/RealRooted/issues/2037). -/
theorem rigidRenewalPolynomial_eq_pathPowerCliquePolynomial
    (d ℓ n : ℕ) (hℓ : 1 ≤ ℓ) :
    rigidRenewalPolynomial d ℓ n =
      pathPowerCliquePolynomial (d * ℓ + 1) (d * n) := by
  ext j
  rw [coeff_rigidRenewalPolynomial d ℓ n j hℓ,
    coeff_pathPowerCliquePolynomial]
  norm_cast
  simp only [Nat.add_sub_cancel]
  rw [mul_assoc, ← Nat.mul_sub_left_distrib]

/-- A rigid renewal polynomial is nonzero. -/
theorem rigidRenewalPolynomial_ne_zero (d ℓ n : ℕ) (hℓ : 1 ≤ ℓ) :
    rigidRenewalPolynomial d ℓ n ≠ 0 := by
  rw [rigidRenewalPolynomial_eq_pathPowerCliquePolynomial d ℓ n hℓ]
  exact pathPowerCliquePolynomial_ne_zero (d * ℓ + 1) (d * n)

/-- Every rigid renewal polynomial splits over the reals. -/
theorem splits_rigidRenewalPolynomial (d ℓ n : ℕ) (hℓ : 1 ≤ ℓ) :
    (rigidRenewalPolynomial d ℓ n).Splits := by
  rw [rigidRenewalPolynomial_eq_pathPowerCliquePolynomial d ℓ n hℓ]
  exact splits_pathPowerCliquePolynomial (d * ℓ + 1) (d * n)

/-- **Rigid renewal interlacing window.**  If `d, ℓ ≥ 1` and
`d * s ≤ d * ℓ + 1`, then the coefficient polynomial of `x ^ n` in
`1 / (1 - x * (1 + t * x ^ ℓ) ^ d)` interlaces the coefficient polynomial
of `x ^ (n + s)`.

This is the rigid case of
[RealRooted issue #2037](https://github.com/PerAlexandersson/RealRooted/issues/2037).
Its fixed-delay input is the weighted form of Fisk, Example 16.10. -/
theorem strictInterl_rigidRenewalPolynomial_add
    (d ℓ n s : ℕ) (hd : 1 ≤ d) (hℓ : 1 ≤ ℓ)
    (hs : d * s ≤ d * ℓ + 1) :
    StrictInterl (rigidRenewalPolynomial d ℓ n)
      (rigidRenewalPolynomial d ℓ (n + s)) := by
  by_cases hs0 : s = 0
  · subst s
    simpa using StrictInterl.refl (rigidRenewalPolynomial_ne_zero d ℓ n hℓ)
      (splits_rigidRenewalPolynomial d ℓ n hℓ)
  · rw [rigidRenewalPolynomial_eq_pathPowerCliquePolynomial d ℓ n hℓ,
      rigidRenewalPolynomial_eq_pathPowerCliquePolynomial d ℓ (n + s) hℓ,
      Nat.mul_add]
    apply strictInterl_pathPowerCliquePolynomial_add
    · have hdℓ : 0 < d * ℓ := Nat.mul_pos hd hℓ
      lia
    · exact Nat.mul_pos hd (Nat.pos_of_ne_zero hs0)
    · exact hs

/-- Consecutive rigid renewal polynomials interlace.  This is the rigid-tiling
consequence requested in RealRooted issue #2037. -/
theorem strictInterl_rigidRenewalPolynomial_succ
    (d ℓ n : ℕ) (hd : 1 ≤ d) (hℓ : 1 ≤ ℓ) :
    StrictInterl (rigidRenewalPolynomial d ℓ n)
      (rigidRenewalPolynomial d ℓ (n + 1)) := by
  apply strictInterl_rigidRenewalPolynomial_add d ℓ n 1 hd hℓ
  have hdℓ : d ≤ d * ℓ := by
    simpa using Nat.mul_le_mul_left d hℓ
  simpa using le_trans hdℓ (Nat.le_add_right (d * ℓ) 1)

end RealRooted
