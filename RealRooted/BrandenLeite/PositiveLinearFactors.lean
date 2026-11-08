module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.WeightedDerivativeKernel
public import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerPositive
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerDetPositive
public import RealRooted.Basic.Coefficients
import RealRooted.Mathlib.Algebra.Polynomial.LinearFactors
import Mathlib.Tactic

/-! # Weighted determinants of polynomial products of positive linear factors -/

public section

open Polynomial

namespace RealRooted

/-- Products of normalized nonnegative linear factors have nonnegative coefficients. -/
theorem hasNonnegCoeffs_prod_one_add_C_mul_X {ι : Type*} (s : Finset ι) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 ≤ α i) :
    HasNonnegCoeffs (∏ i ∈ s, (1 + C (α i) * X : ℝ[X])) :=
  Polynomial.coeff_prod_one_add_C_mul_X_nonneg s α hα

/-- The reflection of a product of normalized negative linear factors with nonnegative
parameters splits and has nonnegative coefficients. -/
theorem splits_and_hasNonnegCoeffs_prod_one_sub_C_mul_X_comp_neg_X {ι : Type*}
    (s : Finset ι) (α : ι → ℝ) (hα : ∀ i ∈ s, 0 ≤ α i) :
    ((∏ i ∈ s, (1 - C (α i) * X : ℝ[X])).comp (-X)).Splits ∧
      HasNonnegCoeffs ((∏ i ∈ s, (1 - C (α i) * X : ℝ[X])).comp (-X)) := by
  rw [Polynomial.prod_one_sub_C_mul_X_comp_neg_X]
  exact ⟨Polynomial.splits_prod_one_add_C_mul_X s α,
    hasNonnegCoeffs_prod_one_add_C_mul_X s α hα⟩

/-- The weighted kernel of the reflection of a nonempty product of normalized
negative linear factors has strictly positive leading determinants. -/
theorem det_weightedDerivativeKernel_prod_linear_comp_neg_X_pos {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    ((Matrix.weightedDerivativeKernel κ
      ((∏ i ∈ s, (1 - C (α i) * X : ℝ[X])).comp (-X)).coeff).submatrix
      Fin.val Fin.val : Matrix (Fin n) (Fin n) ℝ).det > 0 := by
  have hseq :
      ((∏ i ∈ s, (1 - C (α i) * X : ℝ[X])).comp (-X)).coeff =
      fun k ↦ (-1 : ℝ) ^ k * PowerSeries.coeff k
        (∏ i ∈ s, (1 - PowerSeries.C (α i) * PowerSeries.X : PowerSeries ℝ)) := by
    funext k
    rw [← Polynomial.coe_prod_one_sub_C_mul_X, Polynomial.coeff_coe]
    exact congrFun (Polynomial.coeff_comp_neg_X_eq_neg_one_pow_mul _) k
  rw [hseq]
  exact PowerSeries.det_weightedDerivativeKernel_signed_prod_linear_pos s hs α hα hκ n

end RealRooted
