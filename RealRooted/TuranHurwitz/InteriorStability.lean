module

public import RealRooted.TuranHurwitz.FamilyNormalization
import RealRooted.TuranHurwitz.NormalizedTuran
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Stability away from the normalization pole

For `a₁ > 0` and `b₁ + tau a₁ > 0`, the fractional-linear argument maps
the required open half-plane outside the unit disk. The common scale factor
then transports the normalized Turán theorem.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The exact common scaling of the original-family Turán expression. -/
theorem aeval_family_turan_normalization (c : Parameters) (ha : c.a₁ ≠ 0)
    (hden : c.b₁ + c.tau * c.a₁ ≠ 0) (z : ℂ)
    (hscale : normalizationScale c z ≠ 0) (m n : ℕ) :
    Polynomial.aeval z (turan m n (family c)) = normalizationScale c z ^ (2 * m + 2 * n) *
      Polynomial.aeval (normalizationArgument c z)
        (turan m n (normalized (normalizedExponent c) (normalizedOffset c))) := by
  exact aeval_turan_scaling _ _ _ _ _ (aeval_family_normalization c ha hden z hscale) m n

/-- The norm-square difference controlling the half-plane to disk transport. -/
theorem normalization_normSq_difference (c : Parameters) (z : ℂ) :
    Complex.normSq ((c.a₁ : ℂ) / 2 +
      ((c.b₁ : ℂ) + (c.a₁ : ℂ) / 2 * (c.tau : ℂ)) * (z + (c.lam : ℂ))) -
        Complex.normSq (normalizationScale c z) =
      (c.b₁ + c.tau * c.a₁) *
        (c.a₁ * (z + (c.lam : ℂ)).re + c.b₁ * Complex.normSq (z + (c.lam : ℂ))) := by
  simp [normalizationScale, Complex.normSq_apply]
  ring

/-- The normalized argument is outside the unit disk throughout the open half-plane. -/
theorem one_lt_norm_normalizationArgument {c : Parameters} (hc : c.Admissible)
    (ha : 0 < c.a₁) (hden : 0 < c.b₁ + c.tau * c.a₁) (z : ℂ)
    (hz : -c.lam < z.re) (hscale : normalizationScale c z ≠ 0) :
    1 < ‖normalizationArgument c z‖ := by
  have hreal : 0 < (z + (c.lam : ℂ)).re := by simpa using (show 0 < z.re + c.lam by linarith)
  have hpos : 0 < (c.b₁ + c.tau * c.a₁) *
      (c.a₁ * (z + (c.lam : ℂ)).re + c.b₁ * Complex.normSq (z + (c.lam : ℂ))) := by
    exact mul_pos hden (add_pos_of_pos_of_nonneg (mul_pos ha hreal)
      (mul_nonneg hc.b₁_nonneg (Complex.normSq_nonneg _)))
  have hdiff := normalization_normSq_difference c z
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hdiff
  have hnorm : ‖normalizationScale c z‖ <
      ‖(c.a₁ : ℂ) / 2 + ((c.b₁ : ℂ) + (c.a₁ : ℂ) / 2 * (c.tau : ℂ)) *
        (z + (c.lam : ℂ))‖ := by
    nlinarith [norm_nonneg (normalizationScale c z),
      norm_nonneg ((c.a₁ : ℂ) / 2 + ((c.b₁ : ℂ) + (c.a₁ : ℂ) / 2 *
        (c.tau : ℂ)) * (z + (c.lam : ℂ)))]
  rw [normalizationArgument, norm_div]
  exact (one_lt_div (norm_pos_iff.mpr hscale)).mpr hnorm

/-- Theorem 1.1(i) on the normalization domain, before the pole and boundary cases. -/
theorem aeval_family_turan_ne_zero_of_scale_ne_zero {c : Parameters} (hc : c.Admissible)
    (ha : 0 < c.a₁) (hden : 0 < c.b₁ + c.tau * c.a₁) (m n : ℕ) (z : ℂ)
    (hz : -c.lam < z.re) (hscale : normalizationScale c z ≠ 0) :
    Polynomial.aeval z (turan m n (family c)) ≠ 0 := by
  have hd := normalizedExponent_pos hc hden
  have hh := normalizedOffset_mem_Icc hc ha hden
  rw [aeval_family_turan_normalization c ha.ne' hden.ne' z hscale]
  exact mul_ne_zero (pow_ne_zero _ hscale)
    (aeval_normalized_turan_ne_zero hd hh.1 hh.2 m n
      (one_lt_norm_normalizationArgument hc ha hden z hz hscale))

/-- With `tau = 0`, the normalization domain is the entire required half-plane. -/
theorem aeval_family_turan_ne_zero_of_tau_eq_zero {c : Parameters} (hc : c.Admissible)
    (ha : 0 < c.a₁) (hb : 0 < c.b₁) (ht : c.tau = 0) (m n : ℕ) (z : ℂ)
    (hz : -c.lam < z.re) : Polynomial.aeval z (turan m n (family c)) ≠ 0 := by
  apply aeval_family_turan_ne_zero_of_scale_ne_zero hc ha
    (by simpa only [ht, zero_mul, add_zero] using hb) m n z hz
  simp only [normalizationScale, ht, Complex.ofReal_zero, zero_mul, sub_zero, mul_one]
  exact div_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne') (by norm_num)

end RealRooted.TuranHurwitz
