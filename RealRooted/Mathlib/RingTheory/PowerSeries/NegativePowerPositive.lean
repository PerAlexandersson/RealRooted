/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Binomial
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerMul
import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialPositive
import Mathlib.Tactic

/-! # Positive coefficients of negative powers of products of linear factors -/

public section

namespace PowerSeries

/-- A negative binomial series rescaled by a negative positive parameter has
strictly positive coefficients. -/
theorem coeff_rescale_neg_binomialSeries_neg_pos {κ α : ℝ}
    (hκ : 0 < κ) (hα : 0 < α) (n : ℕ) :
    0 < coeff n (rescale (-α) (binomialSeries ℝ (-κ))) := by
  rw [coeff_rescale, binomialSeries_coeff]
  simp only [smul_eq_mul, mul_one]
  have hpow : (-α) ^ n = α ^ n * (-1 : ℝ) ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hpow, mul_assoc, Ring.neg_one_pow_mul_choose_neg]
  exact mul_pos (pow_pos hα _) (Ring.multichoose_pos hκ n)

/-- The canonical negative power of a positive linear factor has strictly
positive coefficients in every degree. -/
theorem coeff_subst_binomialSeries_neg_linear_pos {κ α : ℝ}
    (hκ : 0 < κ) (hα : 0 < α) (n : ℕ) :
    0 < coeff n (subst ((1 - C α * X : PowerSeries ℝ) - 1)
      (binomialSeries ℝ (-κ))) := by
  have harg : (1 - C α * X : PowerSeries ℝ) - 1 = (-α) • X := by
    rw [smul_eq_C_mul, map_neg]
    ring
  rw [harg, ← rescale_eq_subst]
  exact coeff_rescale_neg_binomialSeries_neg_pos hκ hα n

/-- The product of two real power series with strictly positive coefficients
again has strictly positive coefficients. -/
theorem coeff_mul_pos_of_coeff_pos {f g : PowerSeries ℝ}
    (hf : ∀ n, 0 < coeff n f) (hg : ∀ n, 0 < coeff n g) (n : ℕ) :
    0 < coeff n (f * g) := by
  rw [coeff_mul]
  apply Finset.sum_pos'
  · intro p _
    exact (mul_pos (hf p.1) (hg p.2)).le
  · exact ⟨(0, n), by simp, mul_pos (hf 0) (hg n)⟩

/-- Negative powers of nonempty products of positive linear factors have
strictly positive coefficients in every degree. -/
theorem coeff_subst_binomialSeries_neg_prod_linear_pos {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    0 < coeff n (subst
      ((∏ i ∈ s, (1 - C (α i) * X : PowerSeries ℝ)) - 1)
      (binomialSeries ℝ (-κ))) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simp at hs
  | @insert a s ha ih =>
    have haα : 0 < α a := hα a (Finset.mem_insert_self _ _)
    have hsα : ∀ i ∈ s, 0 < α i := fun i hi ↦ hα i (Finset.mem_insert_of_mem hi)
    have hlin : constantCoeff (1 - C (α a) * X : PowerSeries ℝ) = 1 := by simp
    have hprod : constantCoeff (∏ i ∈ s, (1 - C (α i) * X : PowerSeries ℝ)) = 1 := by
      simp
    rw [Finset.prod_insert ha, subst_binomialSeries_neg_mul κ _ _ hlin hprod]
    by_cases hsn : s.Nonempty
    · exact coeff_mul_pos_of_coeff_pos
        (coeff_subst_binomialSeries_neg_linear_pos hκ haα)
        (fun k ↦ ih hsn hsα k) n
    · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsn
      subst s
      simpa [subst_zero_eq_C_constantCoeff] using
        coeff_subst_binomialSeries_neg_linear_pos hκ haα n

end PowerSeries
