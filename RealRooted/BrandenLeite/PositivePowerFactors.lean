module

import RealRooted.BrandenLeite.PositivePowerRow
import RealRooted.Mathlib.Algebra.Polynomial.LinearFactors
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import RealRooted.Basic.ProperPosition
public import RealRooted.BrandenLeite.AffineNegativePower
import RealRooted.BrandenLeite.PositivePowerRegularization
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerDegree
import RealRooted.BrandenLeite.AffineNegativePowerDegree
import Mathlib.Tactic

/-! The positive real-power Brändén–Leite theorem for factored data. -/

public section

open Polynomial

namespace RealRooted.BrandenLeite

/-- The numerator `c X ^ r ∏ (1 + β j X)` of the factored data is nonzero, split, has
nonnegative coefficients and vanishes at zero. -/
private theorem numerator_facts {ν : Type*} (t : Finset ν) (β : ν → ℝ)
    (hβ : ∀ j ∈ t, 0 ≤ β j) {c : ℝ} (hc : 0 < c) (r : ℕ) (hr : r ≠ 0) :
    let B : Polynomial ℝ := C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X)
    HasNonnegCoeffs B ∧ B.coeff 0 = 0 ∧ B ≠ 0 ∧ B.Splits := by
  intro B
  have hBcoe : (B : PowerSeries ℝ) = PowerSeries.C c * PowerSeries.X ^ r *
      ∏ j ∈ t, (1 + PowerSeries.C (β j) * PowerSeries.X : PowerSeries ℝ) :=
    Polynomial.coe_C_mul_X_pow_prod_one_add_C_mul_X c r t β
  obtain ⟨hBnonneg, hBzero, hBpositive⟩ :=
    PowerSeries.coeff_C_mul_X_pow_prod_linear t β hβ hc r
  have hBpos : 0 < B.coeff r := by
    rw [← Polynomial.coeff_coe, hBcoe]
    exact hBpositive
  refine ⟨fun k => ?_, ?_, ?_, (Polynomial.Splits.C_mul_X_pow c r).mul
    (Polynomial.splits_prod_one_add_C_mul_X t β)⟩
  · rw [← Polynomial.coeff_coe, hBcoe]
    exact hBnonneg k
  · rw [← Polynomial.coeff_coe, hBcoe]
    exact hBzero 0 (Nat.pos_of_ne_zero hr)
  · intro hz
    simp only [hz, Polynomial.coeff_zero, lt_self_iff_false] at hBpos

/-- Degree and coefficient positivity of the factored rows, in polynomial form. -/
private theorem degree_and_coeff_pos
    {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
    (hβ : ∀ j ∈ t, 0 ≤ β j) {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ)
    (r : ℕ) (hr : r ≠ 0) (n : ℕ) :
    (affineNegativePowerCoeff κ
        ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
        ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n).natDegree =
        n / r ∧
      ∀ k ≤ n / r, 0 < (affineNegativePowerCoeff κ
        ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
        ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n).coeff
          k := by
  rw [Polynomial.coe_prod_one_sub_C_mul_X s α,
    Polynomial.coe_C_mul_X_pow_prod_one_add_C_mul_X c r t β]
  exact affineNegativePowerCoeff_factor_degree_and_pos
    s hs α hα t β hβ hc hκ r hr n

section

variable {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
  (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
  (hβ : ∀ j ∈ t, 0 ≤ β j) {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ)
  (r : ℕ) (hr : r ≠ 0) (n : ℕ)

include hs hα hβ hc hκ hr

/-- The canonical positive-power row of factored data is nonzero. -/
theorem affineNegativePowerCoeff_factor_ne_zero :
    affineNegativePowerCoeff κ
      ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
      ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n ≠ 0 := by
  obtain ⟨hnn, hB0, -, hBs⟩ := numerator_facts t β hβ hc r hr
  exact (affineNegativePowerCoeff_prod_linear_splits_and_roots_neg
    s hs α hα hκ _ hB0 hBs hnn n).1

/-- The canonical positive-power row of factored data splits. -/
theorem splits_affineNegativePowerCoeff_factor :
    (affineNegativePowerCoeff κ
      ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
      ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n).Splits := by
  obtain ⟨hnn, hB0, -, hBs⟩ := numerator_facts t β hβ hc r hr
  exact (affineNegativePowerCoeff_prod_linear_splits_and_roots_neg
    s hs α hα hκ _ hB0 hBs hnn n).2.1

/-- Every root of the canonical positive-power row of factored data is negative. -/
theorem roots_neg_affineNegativePowerCoeff_factor :
    ∀ x ∈ (affineNegativePowerCoeff κ
      ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
      ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n).roots,
        x < 0 := by
  obtain ⟨hnn, hB0, -, hBs⟩ := numerator_facts t β hβ hc r hr
  exact (affineNegativePowerCoeff_prod_linear_splits_and_roots_neg
    s hs α hα hκ _ hB0 hBs hnn n).2.2

/-- The canonical positive-power row of factored data has degree `n / r`. -/
theorem natDegree_affineNegativePowerCoeff_factor :
    (affineNegativePowerCoeff κ
      ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
      ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n).natDegree =
        n / r :=
  (degree_and_coeff_pos s hs α hα t β hβ hc hκ r hr n).1

/-- The canonical positive-power row of factored data has positive coefficients
through degree `n / r`. -/
theorem coeff_pos_affineNegativePowerCoeff_factor :
    ∀ k ≤ n / r, 0 < (affineNegativePowerCoeff κ
      ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
      ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n).coeff k :=
  (degree_and_coeff_pos s hs α hα t β hβ hc hκ r hr n).2

/-- Consecutive canonical positive-power rows of factored data interlace. -/
theorem interl_affineNegativePowerCoeff_factor :
    Interl (affineNegativePowerCoeff κ
        ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
        ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n)
      (affineNegativePowerCoeff κ
        ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
        ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) (n + 1)) := by
  obtain ⟨hnn, hB0, hBne, hBs⟩ := numerator_facts t β hβ hc r hr
  exact interl_affineNegativePowerCoeff_prod_linear_succ s hs α hα hκ _ hBne hB0 hBs hnn n

end

/-- For a nonempty positive product denominator and a PF product numerator
vanishing to order `r`, every positive real power gives nonzero, split
coefficient rows with strictly negative roots, exact degree `n/r`, positive
coefficients through that degree, and oriented consecutive interlacing. -/
theorem affineNegativePowerCoeff_factor_properties
    {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
    (hβ : ∀ j ∈ t, 0 ≤ β j) {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ)
    (r : ℕ) (hr : r ≠ 0) (n : ℕ) :
    let Q : Polynomial ℝ := ∏ i ∈ s, (1 - C (α i) * X)
    let B : Polynomial ℝ := C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X)
    let q := fun m => affineNegativePowerCoeff κ
      (Q : PowerSeries ℝ) (B : PowerSeries ℝ) m
    q n ≠ 0 ∧ (q n).Splits ∧ (∀ x ∈ (q n).roots, x < 0) ∧
      (q n).natDegree = n / r ∧ (∀ k ≤ n / r, 0 < (q n).coeff k) ∧
      Interl (q n) (q (n + 1)) :=
  ⟨affineNegativePowerCoeff_factor_ne_zero s hs α hα t β hβ hc hκ r hr n,
    splits_affineNegativePowerCoeff_factor s hs α hα t β hβ hc hκ r hr n,
    roots_neg_affineNegativePowerCoeff_factor s hs α hα t β hβ hc hκ r hr n,
    natDegree_affineNegativePowerCoeff_factor s hs α hα t β hβ hc hκ r hr n,
    coeff_pos_affineNegativePowerCoeff_factor s hs α hα t β hβ hc hκ r hr n,
    interl_affineNegativePowerCoeff_factor s hs α hα t β hβ hc hκ r hr n⟩

end RealRooted.BrandenLeite
