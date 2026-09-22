import RealRooted.JacobiDeformation.JacobiMomentFormula
import RealRooted.JacobiDeformation.JacobiMomentTerm

/-!
# Finite-sum reduction for normalized Jacobi moments

This file stops at the explicit finite sum.  Its Chu--Vandermonde evaluation
belongs to the subsequent moment-evaluation leaf.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

private theorem normalizedJacobiFunctional_sum {ι : Type*} (c d : ℝ)
    (s : Finset ι) (p : ι → ℝ[X]) :
    normalizedJacobiFunctional c d (∑ x ∈ s, p x) =
      ∑ x ∈ s, normalizedJacobiFunctional c d (p x) := by
  unfold normalizedJacobiFunctional
  rw [shiftedJacobiFunctional_sum, Finset.sum_div]

private theorem normalizedJacobiFunctional_C_mul (c d a : ℝ) (p : ℝ[X]) :
    normalizedJacobiFunctional c d (C a * p) =
      a * normalizedJacobiFunctional c d p := by
  unfold normalizedJacobiFunctional
  rw [shiftedJacobiFunctional_C_mul]
  ring

/-- Applying the normalized Jacobi functional to a normalized shifted Jacobi
polynomial times `(1 - X)^k` reduces exactly to its finite hypergeometric sum.
The finite sum is intentionally not evaluated here. -/
theorem normalizedJacobiFunctional_normalizedShiftedJacobi_one_sub_X_pow_eq_sum
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (j k : ℕ) :
    normalizedJacobiFunctional c d
        (normalizedShiftedJacobi j c d * (1 - X) ^ k) =
      (risingFactorial d k / risingFactorial (c + d) k) *
        ∑ i ∈ Finset.range (j + 1),
          (-1 : ℝ) ^ i * (j.choose i : ℝ) *
            risingFactorial ((j : ℝ) + c + d - 1) i /
              risingFactorial (c + d + k) i := by
  rw [normalizedShiftedJacobi_eq_sum_coeff hc hd j, Finset.sum_mul,
    normalizedJacobiFunctional_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [mul_assoc, normalizedJacobiFunctional_C_mul,
    coeff_normalizedShiftedJacobi_of_le hc hd hij,
    normalizedJacobiFunctional_mixed_moment hc hd i k]
  calc
    ((-1 : ℝ) ^ i * (j.choose i : ℝ) *
          risingFactorial ((j : ℝ) + c + d - 1) i / risingFactorial c i) *
        (risingFactorial c i * risingFactorial d k /
          risingFactorial (c + d) (i + k)) =
        ((-1 : ℝ) ^ i * (j.choose i : ℝ)) *
          ((risingFactorial ((j : ℝ) + c + d - 1) i / risingFactorial c i) *
            (risingFactorial c i * risingFactorial d k /
              risingFactorial (c + d) (i + k))) := by ring
    _ = ((-1 : ℝ) ^ i * (j.choose i : ℝ)) *
          ((risingFactorial d k / risingFactorial (c + d) k) *
            (risingFactorial ((j : ℝ) + c + d - 1) i /
              risingFactorial (c + d + k) i)) := by
        rw [risingFactorial_mixed_moment_cancel hc hd i k]
    _ = (risingFactorial d k / risingFactorial (c + d) k) *
          ((-1 : ℝ) ^ i * (j.choose i : ℝ) *
            risingFactorial ((j : ℝ) + c + d - 1) i /
              risingFactorial (c + d + k) i) := by ring

end RealRooted.JacobiDeformation
