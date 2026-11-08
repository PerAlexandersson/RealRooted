module

import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerDegree
import RealRooted.BrandenLeite.AffineNegativePowerDegree
import RealRooted.Mathlib.Algebra.Polynomial.LinearFactors
public import RealRooted.Basic.ProperPosition
public import RealRooted.BrandenLeite.AffineLogarithm
import RealRooted.BrandenLeite.LogarithmicInterlacing
import RealRooted.BrandenLeite.LogarithmDegree

/-! The logarithmic Brändén–Leite theorem for factored data. -/

public section

open Polynomial

namespace RealRooted.BrandenLeite

/-- Degree and coefficient positivity of the factored logarithmic rows, in polynomial
form. -/
private theorem degree_and_coeff_pos
    {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
    (hβ : ∀ j ∈ t, 0 ≤ β j) {c : ℝ} (hc : 0 < c)
    (r : ℕ) (hr : r ≠ 0) (n : ℕ) (hn : n ≠ 0) :
    (affineLogCoeff
        ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
        ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n).natDegree =
        n / r ∧
      ∀ k ≤ n / r, 0 < (affineLogCoeff
        ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
        ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n).coeff
          k := by
  rw [Polynomial.coe_prod_one_sub_C_mul_X s α,
    Polynomial.coe_C_mul_X_pow_prod_one_add_C_mul_X c r t β]
  obtain ⟨hBnonneg, hBzero, hBpositive⟩ :=
    PowerSeries.coeff_C_mul_X_pow_prod_linear t β hβ hc r
  exact affineLogCoeff_prod_linear_degree_and_pos
    s hs α hα _ r hr hBnonneg hBzero hBpositive hn

section

variable {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
  (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
  (hβ : ∀ j ∈ t, 0 ≤ β j) {c : ℝ} (hc : 0 < c)
  (r : ℕ) (hr : r ≠ 0) (n : ℕ) (hn : n ≠ 0)

include hs hα hβ hc hr hn

/-- The logarithmic row of positive index of factored data has positive constant
coefficient. -/
private theorem coeff_zero_pos :
    0 < (affineLogCoeff
      ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
      ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n).coeff 0 :=
  (degree_and_coeff_pos s hs α hα t β hβ hc r hr n hn).2 0 (Nat.zero_le _)

/-- The logarithmic row of positive index of factored data is nonzero. -/
theorem affineLogCoeff_factor_ne_zero :
    affineLogCoeff
      ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
      ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n ≠ 0 := by
  intro hz
  have h := coeff_zero_pos s hs α hα t β hβ hc r hr n hn
  simp only [hz, Polynomial.coeff_zero, lt_self_iff_false] at h

/-- The logarithmic row of positive index of factored data splits. -/
theorem splits_affineLogCoeff_factor :
    (affineLogCoeff
      ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
      ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n).Splits :=
  ((isPFPolynomial_affineLogCoeff_factor s hs α hα t β hβ hc r hr n hn).ne_zero_and_splits
    (affineLogCoeff_factor_ne_zero s hs α hα t β hβ hc r hr n hn)).2

/-- Every root of the logarithmic row of positive index of factored data is negative. -/
theorem roots_neg_affineLogCoeff_factor :
    ∀ x ∈ (affineLogCoeff
      ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
      ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n).roots,
        x < 0 :=
  roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne
    (isPFPolynomial_affineLogCoeff_factor s hs α hα t β hβ hc r hr n hn).hasNonnegCoeffs
    (coeff_zero_pos s hs α hα t β hβ hc r hr n hn).ne'

/-- The logarithmic row of positive index of factored data has degree `n / r`. -/
theorem natDegree_affineLogCoeff_factor :
    (affineLogCoeff
      ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
      ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n).natDegree =
        n / r :=
  (degree_and_coeff_pos s hs α hα t β hβ hc r hr n hn).1

/-- The logarithmic row of positive index of factored data has positive coefficients
through degree `n / r`. -/
theorem coeff_pos_affineLogCoeff_factor :
    ∀ k ≤ n / r, 0 < (affineLogCoeff
      ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
      ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n).coeff k :=
  (degree_and_coeff_pos s hs α hα t β hβ hc r hr n hn).2

end

/-- For a nonempty positive product denominator and a PF product numerator
vanishing to order `r`, every positive-index logarithmic coefficient row is
nonzero and split, with strictly negative roots, exact degree `n/r`, positive
coefficients through that degree, and oriented consecutive interlacing. -/
theorem affineLogCoeff_factor_properties
    {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
    (hβ : ∀ j ∈ t, 0 ≤ β j) {c : ℝ} (hc : 0 < c)
    (r : ℕ) (hr : r ≠ 0) (n : ℕ) (hn : n ≠ 0) :
    let Q : Polynomial ℝ := ∏ i ∈ s, (1 - C (α i) * X)
    let B : Polynomial ℝ := C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X)
    let ℓ := fun m => affineLogCoeff (Q : PowerSeries ℝ) B m
    ℓ n ≠ 0 ∧ (ℓ n).Splits ∧ (∀ x ∈ (ℓ n).roots, x < 0) ∧
      (ℓ n).natDegree = n / r ∧ (∀ k ≤ n / r, 0 < (ℓ n).coeff k) ∧
      Interl (ℓ n) (ℓ (n + 1)) :=
  ⟨affineLogCoeff_factor_ne_zero s hs α hα t β hβ hc r hr n hn,
    splits_affineLogCoeff_factor s hs α hα t β hβ hc r hr n hn,
    roots_neg_affineLogCoeff_factor s hs α hα t β hβ hc r hr n hn,
    natDegree_affineLogCoeff_factor s hs α hα t β hβ hc r hr n hn,
    coeff_pos_affineLogCoeff_factor s hs α hα t β hβ hc r hr n hn,
    interl_affineLogCoeff_factor s hs α hα t β hβ hc r hr n hn⟩

end RealRooted.BrandenLeite
