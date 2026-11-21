module

public import RealRooted.TuranHurwitz.Recurrence
public import RealRooted.TuranHurwitz.LinearNormalization
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Fractional-linear normalization of the original family

We prove the normalization inside complex formal series at an arbitrary center.
Taking the constant coefficient gives the pointwise formula, so no analytic
differentiation or convergence theorem is needed.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The scalar prefactor in the original-family normalization. -/
@[expose] noncomputable def normalizationScale (c : Parameters) (z : ℂ) : ℂ :=
  (c.a₁ : ℂ) / 2 * (1 - (c.tau : ℂ) * (z + (c.lam : ℂ)))

/-- The fractional-linear argument, using a numerator without division by `a₁`. -/
@[expose] noncomputable def normalizationArgument (c : Parameters) (z : ℂ) : ℂ :=
  ((c.a₁ : ℂ) / 2 +
    ((c.b₁ : ℂ) + (c.a₁ : ℂ) / 2 * (c.tau : ℂ)) * (z + (c.lam : ℂ))) /
      normalizationScale c z

/-- The two real coefficient identities in the normalized recurrence. -/
theorem normalization_parameter_identities (c : Parameters) (ha : c.a₁ ≠ 0)
    (hden : c.b₁ + c.tau * c.a₁ ≠ 0) :
    c.a₁ / 2 * (normalizedExponent c + normalizedOffset c) = c.a₂ ∧
      normalizedExponent c * (c.b₁ + c.a₁ / 2 * c.tau) -
        normalizedOffset c * (c.a₁ / 2) * c.tau = c.b₁ + c.b₂ := by
  constructor
  · dsimp [normalizedOffset]
    field_simp
    ring
  · dsimp [normalizedExponent, normalizedOffset]
    field_simp
    ring

/-- The original family is the scaled normalized row in any formal affine coordinate. -/
theorem family_aeval_series_normalization (c : Parameters) (ha : c.a₁ ≠ 0)
    (hden : c.b₁ + c.tau * c.a₁ ≠ 0) (g : PowerSeries ℂ)
    (hg : PowerSeries.derivative g = 1)
    (hF : PowerSeries.constantCoeff
      (linearScale ((c.a₁ : ℂ) / 2) (c.tau : ℂ)
        (g + PowerSeries.C (c.lam : ℂ))) ≠ 0) (j : ℕ) :
    Polynomial.aeval g (family c j) =
      linearScale ((c.a₁ : ℂ) / 2) (c.tau : ℂ) (g + PowerSeries.C (c.lam : ℂ)) ^ j *
        Polynomial.aeval
          (linearArgument ((c.a₁ : ℂ) / 2) (c.b₁ : ℂ) (c.tau : ℂ)
            (g + PowerSeries.C (c.lam : ℂ)))
          (normalized (normalizedExponent c) (normalizedOffset c) j) := by
  let a : ℂ := (c.a₁ : ℂ) / 2
  let q := g + PowerSeries.C (c.lam : ℂ)
  let F := linearScale a (c.tau : ℂ) q
  let U := linearArgument a (c.b₁ : ℂ) (c.tau : ℂ) q
  let A := PowerSeries.C (c.a₂ : ℂ) + PowerSeries.C ((c.b₁ + c.b₂ : ℝ) : ℂ) * q
  let L := PowerSeries.C (c.tau : ℂ) * q *
    (PowerSeries.C (2 * a) + PowerSeries.C (c.b₁ : ℂ) * q)
  let Q := q * (1 - PowerSeries.C (c.tau : ℂ) * q) *
    (PowerSeries.C (2 * a) + PowerSeries.C (c.b₁ : ℂ) * q)
  have hq : PowerSeries.derivative q = 1 := by
    simp only [q, map_add, hg, PowerSeries.derivative_C, add_zero]
  have htwo : 2 * a = (c.a₁ : ℂ) := by dsimp [a]; ring
  have hnonzero : F ≠ 0 := by
    intro heq
    exact hF (by change PowerSeries.constantCoeff F = 0; rw [heq, map_zero])
  obtain ⟨hzero, hone⟩ := normalization_parameter_identities c ha hden
  have hzeroC : a * ((normalizedExponent c : ℂ) + (normalizedOffset c : ℂ)) =
      (c.a₂ : ℂ) := by dsimp [a]; exact_mod_cast hzero
  have honeC : (normalizedExponent c : ℂ) * ((c.b₁ : ℂ) + a * (c.tau : ℂ)) -
      (normalizedOffset c : ℂ) * a * (c.tau : ℂ) = ((c.b₁ + c.b₂ : ℝ) : ℂ) := by
    dsimp [a]
    exact_mod_cast hone
  have hA : F * (PowerSeries.C (normalizedExponent c : ℂ) * U +
      PowerSeries.C (normalizedOffset c : ℂ)) = A :=
    linearNormalization_affine a _ _ _ _ _ _ q hF hzeroC honeC
  have hL : F * L + Q * PowerSeries.derivative F = 0 :=
    linearNormalization_cancellation a _ _ q hq
  have hU : F * (U ^ 2 - 1) = Q * PowerSeries.derivative U :=
    linearNormalization_vectorField a _ _ q hq hF
  change Polynomial.aeval g (family c j) =
    F ^ j * Polynomial.aeval U (normalized (normalizedExponent c) (normalizedOffset c) j)
  induction j with
  | zero => simp
  | succ j ih =>
      have hdiff := congrArg PowerSeries.derivative ih
      rw [derivative_aeval_series, hg, mul_one] at hdiff
      rw [scaled_normalized_succ _ _ F U A L Q hnonzero hA hL hU]
      rw [family]
      have hc (r : ℝ) : algebraMap ℝ ℂ r = (r : ℂ) := rfl
      simp only [map_add, map_mul, map_sub, Polynomial.aeval_C,
        shiftedVariable, Polynomial.aeval_X, PowerSeries.algebraMap_apply, hc]
      rw [ih, hdiff]
      change _ = (A + PowerSeries.C (j : ℂ) * L) * _ + Q * _
      dsimp [A, L, Q, q]
      rw [htwo]
      simp only [map_one, Complex.ofReal_add, map_add]
      ring

/-- Pointwise normalization away from the zero of its scalar prefactor. -/
theorem aeval_family_normalization (c : Parameters) (ha : c.a₁ ≠ 0)
    (hden : c.b₁ + c.tau * c.a₁ ≠ 0) (z : ℂ)
    (hscale : normalizationScale c z ≠ 0) (j : ℕ) :
    Polynomial.aeval z (family c j) = normalizationScale c z ^ j *
      Polynomial.aeval (normalizationArgument c z)
        (normalized (normalizedExponent c) (normalizedOffset c) j) := by
  let g : PowerSeries ℂ := PowerSeries.C z + PowerSeries.X
  have hg : PowerSeries.derivative g = 1 := by simp [g]
  have hF : PowerSeries.constantCoeff
      (linearScale ((c.a₁ : ℂ) / 2) (c.tau : ℂ)
        (g + PowerSeries.C (c.lam : ℂ))) ≠ 0 := by
    simpa only [linearScale, map_mul, map_sub, map_one, PowerSeries.constantCoeff_C,
      map_add, g, PowerSeries.constantCoeff_X, add_zero, normalizationScale] using hscale
  have hseries := family_aeval_series_normalization c ha hden g hg hF j
  have h := congrArg PowerSeries.constantCoeff hseries
  rw [constantCoeff_aeval_series, map_mul, map_pow, constantCoeff_aeval_series] at h
  simpa only [g, map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
    add_zero, linearScale, linearArgument, linearNumerator, map_mul, map_sub, map_one,
    PowerSeries.constantCoeff_inv, normalizationScale, normalizationArgument,
    div_eq_mul_inv] using h

end RealRooted.TuranHurwitz
