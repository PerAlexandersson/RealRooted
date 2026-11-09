module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
import RealRooted.Hadamard.Basic
public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import RealRooted.QuadraticRoot

/-!
# Counterexamples for rowwise products of polynomial sequences

Two sequence operators can each preserve real-rootedness while their rowwise Hadamard or
normalized Schur product fails even on a quadratic or linear input.  This file records the
exact failing outputs; both have negative discriminant.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

private theorem hadamardProduct_X_pow (n : ℕ) (q : ℝ[X]) :
    hadamardProduct (X ^ n) q = C (q.coeff n) * X ^ n := by
  ext k
  by_cases hkn : k = n
  · subst k
    simp [coeff_hadamardProduct, coeff_X_pow]
  · simp [coeff_hadamardProduct, coeff_X_pow, hkn]

/-- The sequence in the rowwise ordinary-Hadamard counterexample. -/
def rowwiseHadamardCounterexampleQ (n : ℕ) : ℝ[X] :=
  if n = 1 then
    C (1 / 4 : ℝ) + C (3 / 4 : ℝ) * X + C (1 / 2 : ℝ) * X ^ 2
  else
    1 + C 2 * X + X ^ 2

/-- Rowwise ordinary Hadamard products for the first counterexample. -/
def rowwiseHadamardCounterexampleR (n : ℕ) : ℝ[X] :=
  hadamardProduct (X ^ n) (rowwiseHadamardCounterexampleQ n)

/-- Rowwise ordinary Hadamard products need not preserve real-rootedness: the rooted input
`(1 + 2t)²` is sent to the quadratic `1 + 3x + 4x²`, whose discriminant is `-7`. -/
theorem rowwiseHadamardProduct_counterexample :
    basisTransform rowwiseHadamardCounterexampleR ((1 + C 2 * X) ^ 2) =
        C 4 * X ^ 2 + C 3 * X + 1 ∧
      ¬ (C 4 * X ^ 2 + C 3 * X + 1 : ℝ[X]).Splits := by
  have hR0 : rowwiseHadamardCounterexampleR 0 = 1 := by
    rw [rowwiseHadamardCounterexampleR, hadamardProduct_X_pow]
    norm_num [rowwiseHadamardCounterexampleQ, Polynomial.coeff_one]
  have hR1 : rowwiseHadamardCounterexampleR 1 = C (3 / 4 : ℝ) * X := by
    rw [rowwiseHadamardCounterexampleR, hadamardProduct_X_pow]
    norm_num [rowwiseHadamardCounterexampleQ, Polynomial.coeff_one,
      Polynomial.coeff_X]
  have hR2 : rowwiseHadamardCounterexampleR 2 = X ^ 2 := by
    rw [rowwiseHadamardCounterexampleR, hadamardProduct_X_pow]
    norm_num [rowwiseHadamardCounterexampleQ, Polynomial.coeff_one,
      Polynomial.coeff_X]
  constructor
  · have hin : ((1 + C 2 * X) ^ 2 : ℝ[X]) =
        C 1 * X ^ 0 + C 4 * X ^ 1 + C 4 * X ^ 2 := by
      norm_num [Polynomial.C_ofNat]
      ring
    rw [hin, basisTransform_add, basisTransform_add,
      basisTransform_C_mul_X_pow, basisTransform_C_mul_X_pow,
      basisTransform_C_mul_X_pow, hR0, hR1, hR2]
    ext (_ | _ | _ | k) <;>
      norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  · exact quadraticPoly_not_splits_of_discrim_neg
      (a := (4 : ℝ)) (b := 3) (c := 1) (by norm_num) (by norm_num [discrim])

/-- The degree-two basis `Pₙ = 4⁻ⁿ(x+1)^(2-n)(x+3)^n` of the invertible substitution map
in the normalized-Schur counterexample, explicitly listed for `0 ≤ n ≤ 2`. -/
def normalizedSchurCounterexampleP (n : ℕ) : ℝ[X] :=
  if n = 0 then X ^ 2 + C 2 * X + 1
  else if n = 1 then C (1 / 4 : ℝ) * X ^ 2 + X + C (3 / 4 : ℝ)
  else if n = 2 then C (1 / 16 : ℝ) * X ^ 2 + C (3 / 8 : ℝ) * X + C (9 / 16 : ℝ)
  else 0

/-- Rowwise normalized degree-two Schur squares for the second counterexample. -/
def normalizedSchurCounterexampleR (n : ℕ) : ℝ[X] :=
  schurSzegoComp 2 (normalizedSchurCounterexampleP n)
    (normalizedSchurCounterexampleP n)

/-- Even rowwise normalized Schur products of an identical invertible real-rootedness
preserver can fail: `1 + 2t` is sent to `(9x² + 24x + 17)/8`, with discriminant `-9/16`. -/
theorem rowwiseNormalizedSchurProduct_counterexample :
    basisTransform normalizedSchurCounterexampleR (1 + C 2 * X) =
        C (9 / 8 : ℝ) * X ^ 2 + C 3 * X + C (17 / 8 : ℝ) ∧
      ¬ (C (9 / 8 : ℝ) * X ^ 2 + C 3 * X + C (17 / 8 : ℝ)).Splits := by
  have hR0 : normalizedSchurCounterexampleR 0 = X ^ 2 + C 2 * X + 1 := by
    rw [normalizedSchurCounterexampleR]
    ext (_ | _ | _ | k) <;>
      norm_num [normalizedSchurCounterexampleP, coeff_schurSzegoComp,
        Polynomial.coeff_one, Polynomial.coeff_X]
  have hR1 : normalizedSchurCounterexampleR 1 =
      C (1 / 16 : ℝ) * X ^ 2 + C (1 / 2 : ℝ) * X + C (9 / 16 : ℝ) := by
    rw [normalizedSchurCounterexampleR]
    ext (_ | _ | _ | k) <;>
      norm_num [normalizedSchurCounterexampleP, coeff_schurSzegoComp,
        Polynomial.coeff_one, Polynomial.coeff_X]
  constructor
  · have hin : (1 + C 2 * X : ℝ[X]) = C 1 * X ^ 0 + C 2 * X ^ 1 := by
      norm_num [Polynomial.C_ofNat]
    rw [hin, basisTransform_add, basisTransform_C_mul_X_pow,
      basisTransform_C_mul_X_pow, hR0, hR1]
    ext (_ | _ | _ | k) <;>
      norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
  · exact quadraticPoly_not_splits_of_discrim_neg
      (a := (9 / 8 : ℝ)) (b := 3) (c := (17 / 8 : ℝ))
      (by norm_num) (by norm_num [discrim])

end RealRooted
