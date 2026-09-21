import RealRooted.JacobiDeformation.JacobiCoefficientExpansion

/-!
# Reconstruction for the normalized Jacobi moment formula
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- The normalized shifted Jacobi polynomial reconstructed from its finite
coefficient expansion. -/
theorem normalizedShiftedJacobi_eq_sum_coeff
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (j : ℕ) :
    normalizedShiftedJacobi j c d =
      ∑ i ∈ Finset.range (j + 1),
        C ((normalizedShiftedJacobi j c d).coeff i) * X ^ i := by
  ext i
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  by_cases hij : i ≤ j
  · simp [hij, Nat.lt_succ_iff.mpr hij]
  · have hji : j < i := Nat.lt_of_not_ge hij
    rw [coeff_normalizedShiftedJacobi_of_lt j c d hji]
    simp [hij, Nat.lt_succ_iff.not.mpr hij]

end RealRooted.JacobiDeformation
