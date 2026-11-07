module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.WeightedDerivativeKernel
public import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerPositive
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerDetPositive
public import RealRooted.Basic.Coefficients
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas
import RealRooted.Mathlib.Algebra.Polynomial.LinearFactors
import Mathlib.Tactic

/-! # Weighted determinants of polynomial products of positive linear factors -/

public section

open Polynomial

namespace RealRooted

/-- Products of normalized nonnegative linear factors have nonnegative coefficients. -/
theorem hasNonnegCoeffs_prod_one_add_C_mul_X {ι : Type*} (s : Finset ι) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 ≤ α i) :
    HasNonnegCoeffs (∏ i ∈ s, (1 + C (α i) * X : ℝ[X])) := by
  apply hasNonnegCoeffs_finsetProd
  intro i hi
  exact hasNonnegCoeffs_one.add (hasNonnegCoeffs_C_mul (hα i hi) hasNonnegCoeffs_X)

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
    rw [← Polynomial.coe_prod_one_sub_C_mul_X, Polynomial.coeff_coe,
      Polynomial.coeff_comp_neg_X]
    exact mul_comm _ _
  rw [hseq]
  exact PowerSeries.det_weightedDerivativeKernel_signed_prod_linear_pos s hs α hα hκ n

end RealRooted
