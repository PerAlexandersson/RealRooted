module

public import RealRooted.TuranHurwitz.FormalHyperbolic
public import RealRooted.TuranHurwitz.BinomialComposition
import RealRooted.TuranHurwitz.CoefficientDerivation
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The formal tanh flow and its weight

We fix the complex parameter `u` and work in `ℂ⟦t⟧`. The powers in the
weight are normalized real binomial powers, so branches and convergence do
not enter the differential identities.
-/

public section

namespace RealRooted.TuranHurwitz

/-- Formal tanh after extension of scalars to the complex numbers. -/
@[expose] noncomputable def complexTanhSeries : PowerSeries ℂ :=
  tanhSeries.map (algebraMap ℝ ℂ)

/-- Complex formal tanh has constant coefficient zero. -/
@[simp] theorem constantCoeff_complexTanhSeries :
    PowerSeries.constantCoeff complexTanhSeries = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, complexTanhSeries,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff]
  simp

/-- Complex formal tanh satisfies the Riccati equation. -/
theorem derivative_complexTanhSeries :
    PowerSeries.derivative complexTanhSeries = 1 - complexTanhSeries ^ 2 := by
  rw [complexTanhSeries, derivative_map, derivative_tanhSeries]
  simp only [map_sub, map_one, map_pow]

local notation "S" => complexTanhSeries

/-- The denominator of the formal fractional-linear tanh flow. -/
@[expose] noncomputable def flowDenominator (u : ℂ) : PowerSeries ℂ :=
  1 - PowerSeries.C u * S

/-- The formal flow `phi(t,u)`. Its denominator has constant coefficient one. -/
@[expose] noncomputable def formalFlow (u : ℂ) : PowerSeries ℂ :=
  (PowerSeries.C u - S) * (flowDenominator u)⁻¹

/-- The normalized formal weight `H(t,u)` in the shift identity. -/
@[expose] noncomputable def flowWeight (d h : ℝ) (u : ℂ) : PowerSeries ℂ :=
  (PowerSeries.binomialSeries ℝ ((d + h) / 2)).subst S *
    (PowerSeries.binomialSeries ℝ ((d - h) / 2)).subst (-S) *
    (PowerSeries.binomialSeries ℝ (-d)).subst (-PowerSeries.C u * S)

/-- Every flow denominator is a unit with constant coefficient one. -/
@[simp] theorem constantCoeff_flowDenominator (u : ℂ) :
    PowerSeries.constantCoeff (flowDenominator u) = 1 := by
  simp [flowDenominator]

/-- The initial value of the formal flow. -/
@[simp] theorem constantCoeff_formalFlow (u : ℂ) :
    PowerSeries.constantCoeff (formalFlow u) = u := by
  simp [formalFlow]

/-- The normalized formal weight has initial value one. -/
@[simp] theorem constantCoeff_flowWeight (d h : ℝ) (u : ℂ) :
    PowerSeries.constantCoeff (flowWeight d h u) = 1 := by
  simp only [flowWeight, map_mul]
  rw [constantCoeff_binomial_subst _ _ (by simp),
    constantCoeff_binomial_subst _ _ (by simp),
    constantCoeff_binomial_subst _ _ (by simp)]
  ring

/-- The formal flow solves the autonomous Riccati equation. -/
theorem derivative_formalFlow (u : ℂ) :
    PowerSeries.derivative (formalFlow u) = formalFlow u ^ 2 - 1 := by
  have hcancel := PowerSeries.mul_inv_cancel (flowDenominator u) (by simp)
  rw [formalFlow, PowerSeries.derivative.leibniz, map_sub, PowerSeries.derivative_C,
    derivative_complexTanhSeries, PowerSeries.derivative_inv']
  rw [flowDenominator, map_sub, PowerSeries.derivative_one,
    PowerSeries.derivative.leibniz, PowerSeries.derivative_C, derivative_complexTanhSeries]
  simp only [zero_sub, smul_eq_mul]
  dsimp [flowDenominator] at hcancel ⊢
  linear_combination (S * (PowerSeries.C u - S) *
    (1 - PowerSeries.C u * S)⁻¹ - 1) * hcancel

private theorem derivative_binomial_tanh (r : ℝ) :
    PowerSeries.derivative ((PowerSeries.binomialSeries ℝ r).subst S) =
      PowerSeries.C (r : ℂ) * (1 - S) *
        (PowerSeries.binomialSeries ℝ r).subst S := by
  have heuler := binomial_subst_euler r S (by simp)
  have hne : (1 + S) ≠ 0 := by
    intro heq
    have h := congrArg PowerSeries.constantCoeff heq
    simp at h
  apply mul_left_cancel₀ hne
  rw [derivative_complexTanhSeries] at heuler
  linear_combination heuler

private theorem derivative_binomial_neg_tanh (r : ℝ) :
    PowerSeries.derivative ((PowerSeries.binomialSeries ℝ r).subst (-S)) =
      -PowerSeries.C (r : ℂ) * (1 + S) *
        (PowerSeries.binomialSeries ℝ r).subst (-S) := by
  have heuler := binomial_subst_euler r (-S) (by simp)
  have hne : (1 + -S) ≠ 0 := by
    intro heq
    have h := congrArg PowerSeries.constantCoeff heq
    simp at h
  apply mul_left_cancel₀ hne
  rw [map_neg, derivative_complexTanhSeries] at heuler
  linear_combination heuler

private theorem derivative_binomial_flowDenominator (d : ℝ) (u : ℂ) :
    PowerSeries.derivative
        ((PowerSeries.binomialSeries ℝ (-d)).subst (-PowerSeries.C u * S)) =
      PowerSeries.C (d : ℂ) * PowerSeries.C u * (1 - S ^ 2) *
        (flowDenominator u)⁻¹ *
          (PowerSeries.binomialSeries ℝ (-d)).subst (-PowerSeries.C u * S) := by
  have heuler := binomial_subst_euler (-d) (-PowerSeries.C u * S) (by simp)
  have hcancel := PowerSeries.mul_inv_cancel (flowDenominator u) (by simp)
  have hne : flowDenominator u ≠ 0 := by
    intro heq
    have h := congrArg PowerSeries.constantCoeff heq
    simp at h
  apply mul_left_cancel₀ hne
  simp only [PowerSeries.derivative.leibniz, map_neg, PowerSeries.derivative_C,
    derivative_complexTanhSeries, neg_zero, mul_zero, add_zero, smul_eq_mul] at heuler
  dsimp [flowDenominator] at hcancel ⊢
  linear_combination heuler -
    (PowerSeries.C (d : ℂ) * PowerSeries.C u * (1 - S ^ 2) *
      (PowerSeries.binomialSeries ℝ (-d)).subst (-PowerSeries.C u * S)) * hcancel

/-- The weight satisfies the first-order equation used to shift the normalized recurrence. -/
theorem derivative_flowWeight (d h : ℝ) (u : ℂ) :
    PowerSeries.derivative (flowWeight d h u) =
      (PowerSeries.C (d : ℂ) * formalFlow u + PowerSeries.C (h : ℂ)) *
        flowWeight d h u := by
  have hsum : PowerSeries.C (((d + h) / 2 : ℝ) : ℂ) +
      PowerSeries.C (((d - h) / 2 : ℝ) : ℂ) = PowerSeries.C (d : ℂ) := by
    rw [← map_add, ← Complex.ofReal_add]
    congr 2
    ring
  have hdiff : PowerSeries.C (((d + h) / 2 : ℝ) : ℂ) -
      PowerSeries.C (((d - h) / 2 : ℝ) : ℂ) = PowerSeries.C (h : ℂ) := by
    rw [← map_sub, ← Complex.ofReal_sub]
    congr 2
    ring
  have hcancel := PowerSeries.mul_inv_cancel (flowDenominator u) (by simp)
  rw [flowWeight, PowerSeries.derivative.leibniz, PowerSeries.derivative.leibniz,
    derivative_binomial_tanh, derivative_binomial_neg_tanh,
    derivative_binomial_flowDenominator]
  dsimp [formalFlow, flowDenominator] at hcancel ⊢
  linear_combination
    ((PowerSeries.binomialSeries ℝ ((d + h) / 2)).subst S *
      (PowerSeries.binomialSeries ℝ ((d - h) / 2)).subst (-S) *
      (PowerSeries.binomialSeries ℝ (-d)).subst (-PowerSeries.C u * S)) * hdiff -
    (S * (PowerSeries.binomialSeries ℝ ((d + h) / 2)).subst S *
      (PowerSeries.binomialSeries ℝ ((d - h) / 2)).subst (-S) *
      (PowerSeries.binomialSeries ℝ (-d)).subst (-PowerSeries.C u * S)) * hsum +
    (PowerSeries.C (d : ℂ) * S *
      (PowerSeries.binomialSeries ℝ ((d + h) / 2)).subst S *
      (PowerSeries.binomialSeries ℝ ((d - h) / 2)).subst (-S) *
      (PowerSeries.binomialSeries ℝ (-d)).subst (-PowerSeries.C u * S)) * hcancel

end RealRooted.TuranHurwitz
