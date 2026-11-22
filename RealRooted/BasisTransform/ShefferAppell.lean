module

public import RealRooted.BasisTransform.LimitingAppell
public import RealRooted.BasisTransform.TranslationLahPositiveMeasure
import RealRooted.BasisTransform.AppellTranslationRigidity
import RealRooted.Mathlib.RingTheory.PowerSeries.ExponentialSubstitution
import RealRooted.Mathlib.RingTheory.PowerSeries.FiniteSubstitution
import Mathlib.Tactic

/-!
# The limiting Appell data of a Sheffer basis

For a row EGF `A(z) exp(x B(z))`, the differential symbol is
`A(z) exp(x (B(z) - z))`. Its even top coefficients are the exponential
sequence with parameter `[z²] B`. Under nonpositive-root preservation this
parameter is nonnegative, and its vanishing forces `B(z) = z`.

This is the Sheffer corollary of the unpublished manuscript behind
RealRooted issue #2181. All identities are identities of formal series.
-/

public section

noncomputable section

open Finset Polynomial

namespace RealRooted

private theorem factorial_inv_mul_descFactorial (n k : ℕ) (hk : k ≤ n) :
    (n.factorial : ℝ)⁻¹ * n.descFactorial k = ((n - k).factorial : ℝ)⁻¹ := by
  have h : (((n - k).factorial : ℝ) * n.descFactorial k) = n.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hk
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hnk : ((n - k).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

private theorem appell_series_mul_exp
    {P : ℕ → ℝ[X]} (hdeg : ∀ n, (P n).natDegree = n)
    (hmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits) :
    PowerSeries.mk (appellCoefficient P) * PowerSeries.rescale X (PowerSeries.exp ℝ[X]) =
      polynomialRowEGF P := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hexpand := eq_sum_of_isAppellExpansion_of_natDegree_le
    (isAppellExpansion_appellCoefficient P) hdeg
    (appellCoefficient_natDegree_le hdeg hmonic hpres) (le_refl n)
  rw [coeff_polynomialRowEGF, hexpand, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using mem_range.mp hk
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  have hrat : (algebraMap ℚ ℝ[X]) (1 / ((n - k).factorial : ℚ)) =
      C (((n - k).factorial : ℝ)⁻¹) := by
    change (algebraMap ℚ ℝ[X]) _ = (algebraMap ℝ ℝ[X]) _
    rw [IsScalarTower.algebraMap_apply ℚ ℝ ℝ[X]]
    congr 1
    norm_num
  rw [hrat]
  have hscalar := factorial_inv_mul_descFactorial n k hkn
  conv_rhs => rw [← mul_assoc, ← C_mul, hscalar]
  ring

/-- The differential-coefficient symbol of a normalized preserving Sheffer
basis is its row EGF with the linear term removed from the substitution. -/
theorem appell_series_eq_sheffer_symbol
    {P : ℕ → ℝ[X]} {A B : PowerSeries ℝ}
    (hdeg : ∀ n, (P n).natDegree = n) (hmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits)
    (hB : PowerSeries.constantCoeff B = 0)
    (hEGF : polynomialRowEGF P = A.map C *
      (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C)) :
    PowerSeries.mk (appellCoefficient P) = A.map C *
      (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * (B - PowerSeries.X).map C) := by
  have heq := congrArg
    (fun S : PowerSeries ℝ[X] => S * PowerSeries.rescale (-X) (PowerSeries.exp ℝ[X]))
    (appell_series_mul_exp hdeg hmonic hpres)
  have hcancel : PowerSeries.rescale X (PowerSeries.exp ℝ[X]) *
      PowerSeries.rescale (-X) (PowerSeries.exp ℝ[X]) = 1 := by
    rw [PowerSeries.exp_mul_exp_eq_exp_add]
    simp
  rw [mul_assoc, hcancel, mul_one, hEGF, mul_assoc] at heq
  rw [PowerSeries.rescale_eq_subst, PowerSeries.smul_eq_C_mul] at heq
  have hzero : PowerSeries.constantCoeff (PowerSeries.C X * B.map C) = 0 := by
    rw [map_mul, PowerSeries.constantCoeff_C, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hB, map_zero,
      mul_zero]
  rw [← PowerSeries.subst_exp_add hzero (by simp)] at heq
  convert heq using 2
  congr 1
  simp only [map_sub, PowerSeries.map_X, map_neg]
  ring

private theorem coeff_coeff_exp_subst (F : PowerSeries ℝ)
    (hF : PowerSeries.constantCoeff F = 0) (n j : ℕ) :
    (PowerSeries.coeff n ((PowerSeries.exp ℝ[X]).subst
      (PowerSeries.C X * F.map C))).coeff j =
        (j.factorial : ℝ)⁻¹ * PowerSeries.coeff n (F ^ j) := by
  have hz : PowerSeries.constantCoeff (PowerSeries.C X * F.map C) = 0 := by
    rw [map_mul, PowerSeries.constantCoeff_C, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hF, map_zero,
      mul_zero]
  have hsub := PowerSeries.HasSubst.of_constantCoeff_zero' hz
  rw [PowerSeries.coeff_subst' hsub]
  have hmap := (Polynomial.lcoeff ℝ j).toAddMonoidHom.map_finsum
    (PowerSeries.coeff_subst_finite' hsub (PowerSeries.exp ℝ[X]) n)
  simp only [LinearMap.toAddMonoidHom_coe] at hmap
  change (Polynomial.lcoeff ℝ j) _ = _
  rw [hmap]
  have hterm (k : ℕ) : (Polynomial.lcoeff ℝ j)
      (PowerSeries.coeff k (PowerSeries.exp ℝ[X]) •
        PowerSeries.coeff n ((PowerSeries.C X * F.map C) ^ k)) =
      if k = j then (j.factorial : ℝ)⁻¹ * PowerSeries.coeff n (F ^ j) else 0 := by
    rw [mul_pow, ← map_pow, PowerSeries.coeff_C_mul, ← map_pow, PowerSeries.coeff_map]
    simp only [PowerSeries.coeff_exp, smul_eq_mul, Polynomial.lcoeff_apply]
    have hrat : (algebraMap ℚ ℝ[X]) (1 / (k.factorial : ℚ)) =
        C ((k.factorial : ℝ)⁻¹) := by
      change (algebraMap ℚ ℝ[X]) _ = (algebraMap ℝ ℝ[X]) _
      rw [IsScalarTower.algebraMap_apply ℚ ℝ ℝ[X]]
      congr 1
      norm_num
    rw [hrat]
    rw [show C ((k.factorial : ℝ)⁻¹) *
        (X ^ k * C (PowerSeries.coeff n (F ^ k))) =
        C ((k.factorial : ℝ)⁻¹ * PowerSeries.coeff n (F ^ k)) * X ^ k by
      rw [map_mul]
      ring, coeff_C_mul_X_pow]
    by_cases hkj : k = j
    · subst k
      simp
    · simp [hkj, Ne.symm hkj]
  simp_rw [hterm]
  rw [finsum_eq_single _ j]
  · simp
  · intro k hk
    simp [hk]

private theorem coeff_coeff_prefactor_exp (A F : PowerSeries ℝ)
    (hF : PowerSeries.constantCoeff F = 0) (n j : ℕ) :
    (PowerSeries.coeff n (A.map C * (PowerSeries.exp ℝ[X]).subst
      (PowerSeries.C X * F.map C))).coeff j =
        PowerSeries.coeff n (A * F ^ j) / (j.factorial : ℝ) := by
  rw [PowerSeries.coeff_mul, finsetSum_coeff, PowerSeries.coeff_mul, sum_div]
  apply sum_congr rfl
  intro q hq
  rw [PowerSeries.coeff_map, coeff_C_mul, coeff_coeff_exp_subst F hF]
  ring

private theorem coeff_even_prefactor_pow {A F : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 1)
    (hF₀ : PowerSeries.constantCoeff F = 0) (hF₁ : PowerSeries.coeff 1 F = 0) (j : ℕ) :
    PowerSeries.coeff (2 * j) (A * F ^ j) = PowerSeries.coeff 2 F ^ j := by
  have hdiv : (PowerSeries.X : PowerSeries ℝ) ^ 2 ∣ F := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro m hm
    interval_cases m
    · simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hF₀
    · exact hF₁
  obtain ⟨G, rfl⟩ := hdiv
  rw [mul_pow, ← pow_mul]
  have hG : PowerSeries.coeff 2 (PowerSeries.X ^ 2 * G) = PowerSeries.constantCoeff G := by
    simpa using PowerSeries.coeff_X_pow_mul G 2 0
  rw [hG, mul_left_comm]
  simpa [hA] using PowerSeries.coeff_X_pow_mul (A * G ^ j) (2 * j) 0

/-- The even top differential coefficients of a normalized preserving
Sheffer basis are exponential coefficients with parameter `[z²] B`. -/
theorem coeff_appellCoefficient_even_of_sheffer
    {P : ℕ → ℝ[X]} {A B : PowerSeries ℝ}
    (hdeg : ∀ n, (P n).natDegree = n) (hmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits)
    (hA : PowerSeries.constantCoeff A = 1)
    (hB : PowerSeries.constantCoeff B = 0) (hB₁ : PowerSeries.coeff 1 B = 1)
    (hEGF : polynomialRowEGF P = A.map C *
      (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C)) (j : ℕ) :
    (appellCoefficient P (2 * j)).coeff j =
      PowerSeries.coeff 2 B ^ j / (j.factorial : ℝ) := by
  have hsym := appell_series_eq_sheffer_symbol hdeg hmonic hpres hB hEGF
  have h := congrArg (fun S : PowerSeries ℝ[X] => (PowerSeries.coeff (2 * j) S).coeff j) hsym
  have hF : PowerSeries.constantCoeff (B - PowerSeries.X) = 0 := by simp [hB]
  rw [PowerSeries.coeff_mk, coeff_coeff_prefactor_exp A _ hF] at h
  rw [coeff_even_prefactor_pow hA hF (by simp [hB₁])] at h
  simpa [PowerSeries.coeff_X] using h

/-- The quadratic coefficient of the Sheffer substitution is nonnegative
for a monic basis preserving polynomials with nonpositive roots. -/
theorem coeff_two_sheffer_nonneg
    {P : ℕ → ℝ[X]} {A B : PowerSeries ℝ}
    (hdeg : ∀ n, (P n).natDegree = n) (hmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits)
    (hA : PowerSeries.constantCoeff A = 1)
    (hB : PowerSeries.constantCoeff B = 0) (hB₁ : PowerSeries.coeff 1 B = 1)
    (hEGF : polynomialRowEGF P = A.map C *
      (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C)) :
    0 ≤ PowerSeries.coeff 2 B := by
  have h := two_mul_coeff_one_appellCoefficient_two_nonneg hdeg hmonic hpres
  have heq := coeff_appellCoefficient_even_of_sheffer hdeg hmonic hpres hA hB hB₁ hEGF 1
  norm_num at heq
  rw [heq] at h
  linarith

/-- The limiting Appell family of a normalized preserving Sheffer basis is
the Gaussian (Hermite) family with parameter `[z²] B = B''(0)/2`. -/
theorem limitingAppellPolynomial_eq_hermite_of_sheffer
    {P : ℕ → ℝ[X]} {A B : PowerSeries ℝ}
    (hdeg : ∀ n, (P n).natDegree = n) (hmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits)
    (hA : PowerSeries.constantCoeff A = 1)
    (hB : PowerSeries.constantCoeff B = 0) (hB₁ : PowerSeries.coeff 1 B = 1)
    (hEGF : polynomialRowEGF P = A.map C *
      (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C)) (N : ℕ) :
    limitingAppellPolynomial (fun j => (appellCoefficient P (2 * j)).coeff j) N =
      limitingAppellPolynomial
        (fun j => PowerSeries.coeff 2 B ^ j / (j.factorial : ℝ)) N := by
  congr 1
  funext j
  exact coeff_appellCoefficient_even_of_sheffer hdeg hmonic hpres hA hB hB₁ hEGF j

/-- Vanishing quadratic coefficient forces the substitution series of a
normalized preserving Sheffer basis to be the identity. -/
theorem sheffer_eq_X_of_coeff_two_eq_zero
    {P : ℕ → ℝ[X]} {A B : PowerSeries ℝ}
    (hdeg : ∀ n, (P n).natDegree = n) (hmonic : ∀ n, (P n).Monic)
    (hpres : ∀ p : ℝ[X], p.Splits →
      (∀ r ∈ p.roots, r ≤ 0) → (basisTransform P p).Splits)
    (hA : PowerSeries.constantCoeff A = 1)
    (hB : PowerSeries.constantCoeff B = 0) (hB₁ : PowerSeries.coeff 1 B = 1)
    (hEGF : polynomialRowEGF P = A.map C *
      (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C))
    (hB₂ : PowerSeries.coeff 2 B = 0) : B = PowerSeries.X := by
  have heq := coeff_appellCoefficient_even_of_sheffer hdeg hmonic hpres hA hB hB₁ hEGF 1
  norm_num [hB₂] at heq
  have hQ := (two_mul_coeff_one_appellCoefficient_two_eq_zero_iff hdeg hmonic hpres).mp
    (by rw [heq, mul_zero])
  have hsym := appell_series_eq_sheffer_symbol hdeg hmonic hpres hB hEGF
  have hF : PowerSeries.constantCoeff (B - PowerSeries.X) = 0 := by simp [hB]
  have hAF : A * (B - PowerSeries.X) = 0 := by
    apply PowerSeries.ext
    intro n
    have h := congrArg (fun S : PowerSeries ℝ[X] => (PowerSeries.coeff n S).coeff 1) hsym
    have hzero : (appellCoefficient P n).coeff 1 = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [hQ n]; norm_num)
    rw [PowerSeries.coeff_mk, hzero, coeff_coeff_prefactor_exp A _ hF] at h
    simpa using h.symm
  have hunit : IsUnit A := PowerSeries.isUnit_iff_constantCoeff.mpr (hA ▸ isUnit_one)
  exact sub_eq_zero.mp (hunit.mul_left_cancel (by simpa using hAF))

end RealRooted
