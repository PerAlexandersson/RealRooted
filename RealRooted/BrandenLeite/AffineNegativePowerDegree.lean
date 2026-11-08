module

import RealRooted.Mathlib.Algebra.Polynomial.LinearFactors
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerDegree
import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialPositive
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerCoefficients
public import RealRooted.BrandenLeite.AffineNegativePower
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerPositive
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

/-! Exact support and positive coefficients of affine negative-power parameter rows. -/

public section

open PowerSeries

namespace RealRooted.BrandenLeite

/-- The exact coefficient support of an affine negative-power row follows
from the first nonzero coefficient of `B` and positivity of the shifted
negative powers of `Q`. -/
theorem coeff_affineNegativePowerCoeff_zero_and_pos
    (Q B : PowerSeries ℝ) (κ : ℝ) (r : ℕ)
    (hQ : constantCoeff Q = 1) (hr : r ≠ 0) (hκ : 0 < κ)
    (hB : ∀ n, 0 ≤ coeff n B)
    (hBzero : ∀ n < r, coeff n B = 0) (hBpos : 0 < coeff r B)
    (hQpos : ∀ (k n : ℕ), 0 < coeff n
      (subst (Q - 1) (binomialSeries ℝ (-κ - (k : ℝ))))) (n k : ℕ) :
    (n < r * k → (affineNegativePowerCoeff κ Q B n).coeff k = 0) ∧
      (r * k ≤ n → 0 < (affineNegativePowerCoeff κ Q B n).coeff k) := by
  have hB0 : constantCoeff B = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hBzero 0 (Nat.pos_of_ne_zero hr)
  have hexp : (affineNegativePowerCoeff κ Q B n).coeff k =
      Ring.multichoose κ k * coeff n
        (B ^ k * subst (Q - 1) (binomialSeries ℝ (-κ - (k : ℝ)))) :=
    coeff_coeff_subst_binomialSeries_neg Q B hQ hB0 κ n k
  rw [hexp]
  exact const_mul_coeff_pow_mul_zero_and_pos (Ring.multichoose_pos hκ k) B _ r hB hBzero
    hBpos (hQpos k) k n

/-- Under coefficient positivity of the shifted negative powers of `Q`,
the affine negative-power row has exact degree `n/r` and positive
coefficients through that degree. -/
theorem natDegree_affineNegativePowerCoeff_and_coeff_pos
    (Q B : PowerSeries ℝ) (κ : ℝ) (r : ℕ)
    (hQ : constantCoeff Q = 1) (hr : r ≠ 0) (hκ : 0 < κ)
    (hB : ∀ n, 0 ≤ coeff n B)
    (hBzero : ∀ n < r, coeff n B = 0) (hBpos : 0 < coeff r B)
    (hQpos : ∀ (k n : ℕ), 0 < coeff n
      (subst (Q - 1) (binomialSeries ℝ (-κ - (k : ℝ))))) (n : ℕ) :
    (affineNegativePowerCoeff κ Q B n).natDegree = n / r ∧
      ∀ k ≤ n / r, 0 < (affineNegativePowerCoeff κ Q B n).coeff k := by
  exact Polynomial.natDegree_eq_div_and_coeff_pos_of_support hr fun k =>
    coeff_affineNegativePowerCoeff_zero_and_pos
      Q B κ r hQ hr hκ hB hBzero hBpos hQpos n k

/-- The constant parameter coefficient is strictly positive for every row
with a nonempty product denominator and positive real exponent. -/
theorem coeff_zero_affineNegativePowerCoeff_prod_linear_pos
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (B : PowerSeries ℝ)
    (hB : constantCoeff B = 0) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    0 < (affineNegativePowerCoeff κ
      (∏ i ∈ s, (1 - C (α i) * X : PowerSeries ℝ)) B n).coeff 0 := by
  unfold affineNegativePowerCoeff
  rw [coeff_coeff_subst_binomialSeries_neg _ B (by simp) hB]
  simpa using coeff_subst_binomialSeries_neg_prod_linear_pos s hs α hα hκ n

/-- For a nonempty product of positive linear factors `Q`, the parameter
rows have exact degree `n/r` and strictly positive coefficients. The
hypotheses on `B` describe precisely its initial coefficient support. -/
theorem affineNegativePowerCoeff_prod_linear_degree_and_pos
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (B : PowerSeries ℝ) (r : ℕ)
    (hr : r ≠ 0) {κ : ℝ} (hκ : 0 < κ)
    (hB : ∀ n, 0 ≤ coeff n B)
    (hBzero : ∀ n < r, coeff n B = 0) (hBpos : 0 < coeff r B) (n : ℕ) :
    let Q := ∏ i ∈ s, (1 - C (α i) * X : PowerSeries ℝ)
    (affineNegativePowerCoeff κ Q B n).natDegree = n / r ∧
      ∀ k ≤ n / r, 0 < (affineNegativePowerCoeff κ Q B n).coeff k := by
  dsimp
  apply natDegree_affineNegativePowerCoeff_and_coeff_pos _ B κ r
    (by simp) hr hκ hB hBzero hBpos
  intro k j
  have hk : 0 < κ + (k : ℝ) := by positivity
  have hexp : -(κ + (k : ℝ)) = -κ - (k : ℝ) := by ring
  simpa only [hexp] using
    coeff_subst_binomialSeries_neg_prod_linear_pos s hs α hα hk j

/-- For the factorized data in the generalized theorem, the canonical
parameter polynomial has degree `n/r` and strictly positive coefficients
in every degree from zero through `n/r`. -/
theorem affineNegativePowerCoeff_factor_degree_and_pos
    {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
    (hβ : ∀ j ∈ t, 0 ≤ β j) {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ)
    (r : ℕ) (hr : r ≠ 0) (n : ℕ) :
    let Q := ∏ i ∈ s, (1 - C (α i) * X : PowerSeries ℝ)
    let B := C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X : PowerSeries ℝ)
    (affineNegativePowerCoeff κ Q B n).natDegree = n / r ∧
      ∀ k ≤ n / r, 0 < (affineNegativePowerCoeff κ Q B n).coeff k := by
  obtain ⟨hB, hBzero, hBpos⟩ := coeff_C_mul_X_pow_prod_linear t β hβ hc r
  exact affineNegativePowerCoeff_prod_linear_degree_and_pos
    s hs α hα _ r hr hκ hB hBzero hBpos n

end RealRooted.BrandenLeite
