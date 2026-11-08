module

public import Mathlib.RingTheory.PowerSeries.Basic
public import RealRooted.BrandenLeite.WeightedDerivativeKernel.Basic
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerPositive
import RealRooted.BrandenLeite.NegativePowerDeterminant
import Mathlib.Tactic.Positivity

/-! # Strict positivity of weighted kernels of positive linear products -/

public section

open PowerSeries

namespace RealRooted.BrandenLeite

/-- The signed weighted kernel of a nonempty product of positive linear
factors has positive leading determinant at every size. -/
theorem det_weightedDerivativeKernel_signed_prod_linear_pos {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    ((weightedDerivativeKernel κ
      (fun k ↦ (-1 : ℝ) ^ k * coeff k
        (∏ i ∈ s, (1 - C (α i) * X : PowerSeries ℝ)))).submatrix
      Fin.val Fin.val : Matrix (Fin n) (Fin n) ℝ).det > 0 := by
  rw [det_weightedDerivativeKernel_subst_binomialSeries_neg κ _ (by simp)]
  exact mul_pos (by positivity)
    (coeff_subst_binomialSeries_neg_prod_linear_pos s hs α hα hκ n)

end RealRooted.BrandenLeite
