import RealRooted.CoefficientDominance.Symmetric.Finite
import Mathlib.Algebra.Polynomial.Roots

/-!
# Polynomial coefficients of elementary-symmetric generating products
-/

namespace RealRooted.CoefficientDominance.Symmetric

open Finset

/-- The coefficients of `∏ (1 + x i X)` are the finite elementary symmetric
functions of the entries. -/
theorem coeff_prod_one_add (x : ℕ → ℝ) (n j : ℕ) :
    (∏ i ∈ range n, (1 + Polynomial.C (x i) * Polynomial.X)).coeff j = esym x n j := by
  induction n generalizing j with
  | zero =>
      rw [Finset.range_zero, Finset.prod_empty, esym, Finset.range_zero]
      cases j with
      | zero => simp
      | succ i =>
          rw [Polynomial.coeff_one]
          simp only [Nat.succ_ne_zero, if_false]
          rw [Finset.powersetCard_eq_empty.mpr (by simp)]
          simp
  | succ n ih =>
      rw [Finset.prod_range_succ]
      set q : Polynomial ℝ := ∏ i ∈ range n, (1 + Polynomial.C (x i) * Polynomial.X) with hq
      have hexp : q * (1 + Polynomial.C (x n) * Polynomial.X)
          = q + Polynomial.C (x n) * (q * Polynomial.X) := by ring
      rw [hexp, Polynomial.coeff_add, Polynomial.coeff_C_mul]
      cases j with
      | zero =>
          simp only [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, mul_zero]
          rw [ih 0, esym_zero, esym_zero]
          ring
      | succ i =>
          rw [Polynomial.coeff_mul_X, ih (i + 1), ih i, esym_succ]

end RealRooted.CoefficientDominance.Symmetric
