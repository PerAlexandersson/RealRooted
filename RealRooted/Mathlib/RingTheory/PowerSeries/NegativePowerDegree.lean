/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import RealRooted.Mathlib.Algebra.Polynomial.LinearFactors
import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialPositive
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerCoefficients
public import RealRooted.Mathlib.RingTheory.PowerSeries.AffineNegativePower
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerPositive
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

/-! Exact support and positive coefficients of negative-power parameter rows. -/

public section

namespace PowerSeries

/-- A positive multiple of `X^r` times nonnegative linear factors has
nonnegative coefficients, vanishes below `r`, and has positive coefficient
in degree `r`. Zero factor parameters are allowed. -/
theorem coeff_C_mul_X_pow_prod_linear
    {ι : Type*} (s : Finset ι) (β : ι → ℝ) (hβ : ∀ i ∈ s, 0 ≤ β i)
    {c : ℝ} (hc : 0 < c) (r : ℕ) :
    let B := C c * X ^ r * ∏ i ∈ s, (1 + C (β i) * X : PowerSeries ℝ)
    (∀ n, 0 ≤ coeff n B) ∧ (∀ n < r, coeff n B = 0) ∧ 0 < coeff r B := by
  classical
  let P : PowerSeries ℝ := ∏ i ∈ s, (1 + C (β i) * X : PowerSeries ℝ)
  have hP : ∀ n, 0 ≤ coeff n P := by
    intro n
    rw [show P = ((∏ i ∈ s, (1 + Polynomial.C (β i) * Polynomial.X : Polynomial ℝ) :
      Polynomial ℝ) : PowerSeries ℝ) from (Polynomial.coe_prod_one_add_C_mul_X s β).symm,
      Polynomial.coeff_coe]
    exact Polynomial.coeff_prod_one_add_C_mul_X_nonneg s β hβ n
  have hP0 : coeff 0 P = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply]
    simp [P]
  change (∀ n, 0 ≤ coeff n (C c * X ^ r * P)) ∧
    (∀ n < r, coeff n (C c * X ^ r * P) = 0) ∧
      0 < coeff r (C c * X ^ r * P)
  have hcoeff (n : ℕ) : coeff n (C c * X ^ r * P) =
      c * if r ≤ n then coeff (n - r) P else 0 := by
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  constructor
  · intro n
    rw [hcoeff]
    split_ifs
    · exact mul_nonneg hc.le (hP _)
    · simp
  constructor
  · intro n hn
    rw [hcoeff, ite_eq_right (Nat.not_le.mpr hn), mul_zero]
  · rw [hcoeff, ite_eq_left le_rfl, Nat.sub_self, hP0, mul_one]
    exact hc

/-- A nonnegative series beginning in degree `r`, with positive coefficient
there, shifts the exact positivity support of every power times a series
whose coefficients are all strictly positive. -/
theorem coeff_pow_mul_zero_and_pos
    (B F : PowerSeries ℝ) (r : ℕ)
    (hB : ∀ n, 0 ≤ coeff n B)
    (hzero : ∀ n < r, coeff n B = 0) (hpos : 0 < coeff r B)
    (hF : ∀ n, 0 < coeff n F) (k : ℕ) :
    (∀ n < r * k, coeff n (B ^ k * F) = 0) ∧
      (∀ n, r * k ≤ n → 0 < coeff n (B ^ k * F)) := by
  induction k with
  | zero =>
    constructor
    · intro n hn
      simp at hn
    · intro n _
      simpa using hF n
  | succ k ih =>
    rcases ih with ⟨ihzero, ihpos⟩
    have ihnonneg (j : ℕ) : 0 ≤ coeff j (B ^ k * F) := by
      rcases lt_or_ge j (r * k) with hj | hj
      · simpa only [ihzero j hj] using (le_refl (0 : ℝ))
      · exact (ihpos j hj).le
    have hrec : B ^ (k + 1) * F = B * (B ^ k * F) := by
      rw [pow_succ]
      ring
    constructor
    · intro n hn
      rw [hrec, coeff_mul]
      apply Finset.sum_eq_zero
      rintro ⟨i, j⟩ hij
      have hij' : i + j = n := Finset.mem_antidiagonal.mp hij
      by_cases hi : i < r
      · rw [hzero i hi, zero_mul]
      · rw [ihzero j (by rw [Nat.mul_succ] at hn; lia), mul_zero]
    · intro n hn
      rw [hrec, coeff_mul]
      apply Finset.sum_pos'
      · intro p _
        exact mul_nonneg (hB p.1) (ihnonneg p.2)
      · refine ⟨(r, n - r), ?_, ?_⟩
        · rw [Finset.mem_antidiagonal]
          rw [Nat.mul_succ] at hn
          lia
        · apply mul_pos hpos
          apply ihpos
          rw [Nat.mul_succ] at hn
          lia

/-- A positive constant times `B ^ k * F` has the same support shift as `B ^ k * F`. -/
theorem const_mul_coeff_pow_mul_zero_and_pos
    {c : ℝ} (hc : 0 < c) (B F : PowerSeries ℝ) (r : ℕ)
    (hB : ∀ n, 0 ≤ coeff n B)
    (hzero : ∀ n < r, coeff n B = 0) (hpos : 0 < coeff r B)
    (hF : ∀ n, 0 < coeff n F) (k n : ℕ) :
    (n < r * k → c * coeff n (B ^ k * F) = 0) ∧
      (r * k ≤ n → 0 < c * coeff n (B ^ k * F)) := by
  have hsupport := coeff_pow_mul_zero_and_pos B F r hB hzero hpos hF k
  exact ⟨fun h => by rw [hsupport.1 n h, mul_zero], fun h => mul_pos hc (hsupport.2 n h)⟩

/-- A real polynomial whose coefficient `k` vanishes for `n < r * k` and is positive for
`r * k ≤ n` has degree `n / r` and positive coefficients through that degree. -/
theorem _root_.Polynomial.natDegree_eq_div_and_coeff_pos_of_support
    {p : Polynomial ℝ} {r n : ℕ} (hr : 0 < r)
    (hsupport : ∀ k, (n < r * k → p.coeff k = 0) ∧ (r * k ≤ n → 0 < p.coeff k)) :
    p.natDegree = n / r ∧ ∀ k ≤ n / r, 0 < p.coeff k := by
  have hiff (k : ℕ) : k ≤ n / r ↔ r * k ≤ n := by
    rw [Nat.le_div_iff_mul_le hr, Nat.mul_comm]
  have hpositive (k : ℕ) (hk : k ≤ n / r) : 0 < p.coeff k :=
    (hsupport k).2 ((hiff k).mp hk)
  refine ⟨Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ (hpositive _ le_rfl).ne',
    hpositive⟩
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => (hsupport k).1 ?_
  exact not_le.mp fun h => absurd ((hiff k).mpr h) (not_le.mpr hk)

/-- The exact coefficient support of an affine negative-power row follows
from the first nonzero coefficient of `B` and positivity of the shifted
negative powers of `Q`. -/
theorem coeff_affineNegativePowerCoeff_zero_and_pos
    (Q B : PowerSeries ℝ) (κ : ℝ) (r : ℕ)
    (hQ : constantCoeff Q = 1) (hr : 0 < r) (hκ : 0 < κ)
    (hB : ∀ n, 0 ≤ coeff n B)
    (hBzero : ∀ n < r, coeff n B = 0) (hBpos : 0 < coeff r B)
    (hQpos : ∀ (k n : ℕ), 0 < coeff n
      (subst (Q - 1) (binomialSeries ℝ (-κ - (k : ℝ))))) (n k : ℕ) :
    (n < r * k → (affineNegativePowerCoeff κ Q B n).coeff k = 0) ∧
      (r * k ≤ n → 0 < (affineNegativePowerCoeff κ Q B n).coeff k) := by
  have hB0 : constantCoeff B = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hBzero 0 hr
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
    (hQ : constantCoeff Q = 1) (hr : 0 < r) (hκ : 0 < κ)
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
    (hr : 0 < r) {κ : ℝ} (hκ : 0 < κ)
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
    (r : ℕ) (hr : 0 < r) (n : ℕ) :
    let Q := ∏ i ∈ s, (1 - C (α i) * X : PowerSeries ℝ)
    let B := C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X : PowerSeries ℝ)
    (affineNegativePowerCoeff κ Q B n).natDegree = n / r ∧
      ∀ k ≤ n / r, 0 < (affineNegativePowerCoeff κ Q B n).coeff k := by
  obtain ⟨hB, hBzero, hBpos⟩ := coeff_C_mul_X_pow_prod_linear t β hβ hc r
  exact affineNegativePowerCoeff_prod_linear_degree_and_pos
    s hs α hα _ r hr hκ hB hBzero hBpos n

end PowerSeries
