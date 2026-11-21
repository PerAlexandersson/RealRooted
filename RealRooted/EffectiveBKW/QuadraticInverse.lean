module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Coefficients of the inverse dominant quadratic

The inverse of `1 - 2 a X + b X²` has the usual sine-multiplied coefficient formula.
This form is valid at collisions as well as in the interior, without dividing by `sin θ`.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW

open PowerSeries

/-- The dominant quadratic factor as a formal power series. -/
noncomputable def quadratic (a b : ℝ) : PowerSeries ℝ :=
  1 - C (2 * a) * X + C b * X ^ 2

/-- The inverse of the dominant quadratic, whose constant term is one. -/
noncomputable def quadraticInverse (a b : ℝ) : PowerSeries ℝ :=
  invOfUnit (quadratic a b) 1

/-- The quadratic has constant coefficient one. -/
@[simp] theorem constantCoeff_quadratic (a b : ℝ) :
    constantCoeff (quadratic a b) = 1 := by
  simp [quadratic]

/-- The defined inverse is a right inverse of the quadratic. -/
theorem quadratic_mul_quadraticInverse (a b : ℝ) :
    quadratic a b * quadraticInverse a b = 1 := by
  exact mul_invOfUnit _ _ (by simp)

/-- The defined inverse agrees with the field-coefficient power-series inverse. -/
theorem quadraticInverse_eq_inv (a b : ℝ) :
    quadraticInverse a b = (quadratic a b)⁻¹ := by
  exact invOfUnit_eq' _ _ (by simp)

/-- The constant inverse coefficient is one. -/
@[simp] theorem coeff_quadraticInverse_zero (a b : ℝ) :
    coeff 0 (quadraticInverse a b) = 1 := by
  simp [quadraticInverse, coeff_zero_eq_constantCoeff_apply]

/-- The linear inverse coefficient is `2 a`. -/
@[simp] theorem coeff_quadraticInverse_one (a b : ℝ) :
    coeff 1 (quadraticInverse a b) = 2 * a := by
  have h := congrArg (coeff 1) (quadratic_mul_quadraticInverse a b)
  simp [quadratic, sub_mul, add_mul, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul'] at h
  linarith

/-- Inverse coefficients obey the second-order recurrence of the quadratic. -/
theorem coeff_quadraticInverse_add_two (a b : ℝ) (n : ℕ) :
    coeff (n + 2) (quadraticInverse a b) =
      2 * a * coeff (n + 1) (quadraticInverse a b) -
        b * coeff n (quadraticInverse a b) := by
  have h := congrArg (coeff (n + 2)) (quadratic_mul_quadraticInverse a b)
  simp [quadratic, sub_mul, add_mul, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul'] at h
  linarith

/-- The sine sequence satisfies the normalized quadratic recurrence. -/
private theorem sin_add_two (x θ : ℝ) :
    Real.sin (x + 2 * θ) = 2 * Real.cos θ * Real.sin (x + θ) - Real.sin x := by
  have h := Real.sin_add_sin (x + 2 * θ) x
  rw [show (x + 2 * θ + x) / 2 = x + θ by ring,
    show (x + 2 * θ - x) / 2 = θ by ring] at h
  linarith

/-- The sine-multiplied coefficient formula includes the collision angles. -/
theorem coeff_quadraticInverse_mul_sin (r θ : ℝ) (n : ℕ) :
    coeff n (quadraticInverse (r * Real.cos θ) (r ^ 2)) * Real.sin θ =
      r ^ n * Real.sin (((n : ℝ) + 1) * θ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
      simp only [coeff_quadraticInverse_one, pow_one, Nat.cast_one]
      rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.sin_two_mul]
      ring
  | more n ih₀ ih₁ =>
      rw [coeff_quadraticInverse_add_two, sub_mul,
        mul_assoc (2 * (r * Real.cos θ)) _ (Real.sin θ), ih₁,
        mul_assoc (r ^ 2) _ (Real.sin θ), ih₀]
      have h := sin_add_two (((n : ℝ) + 1) * θ) θ
      rw [show ((n : ℝ) + 1) * θ + 2 * θ = ((n : ℝ) + 2 + 1) * θ by ring,
        show ((n : ℝ) + 1) * θ + θ = ((n : ℝ) + 1 + 1) * θ by ring] at h
      push_cast
      rw [h]
      simp only [pow_add, pow_one, pow_two]
      ring

/-- The inverse coefficient formula in the real parameters of the dominant pair. -/
theorem coeff_quadraticInverse_mul_sin_arccos {a b : ℝ} (hb : 0 < b)
    (hab : a ^ 2 ≤ b) (n : ℕ) :
    coeff n (quadraticInverse a b) * Real.sin (Real.arccos (a / Real.sqrt b)) =
      Real.sqrt b ^ n * Real.sin (((n : ℝ) + 1) * Real.arccos (a / Real.sqrt b)) := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have ha := abs_le.mp (Real.abs_le_sqrt hab)
  have hlo : -1 ≤ a / Real.sqrt b := by
    apply (le_div_iff₀ hs).mpr
    linarith [ha.1]
  have hhi : a / Real.sqrt b ≤ 1 := (div_le_one hs).mpr ha.2
  have hparam : Real.sqrt b * Real.cos (Real.arccos (a / Real.sqrt b)) = a := by
    rw [Real.cos_arccos hlo hhi]
    field_simp
  have h := coeff_quadraticInverse_mul_sin (Real.sqrt b)
    (Real.arccos (a / Real.sqrt b)) n
  rw [hparam, Real.sq_sqrt hb.le] at h
  exact h

/-- Normalizing by the dominant root modulus gives the coefficient identity used by BKW. -/
theorem sin_mul_inv_sqrt_pow_mul_coeff {a b : ℝ} (hb : 0 < b)
    (hab : a ^ 2 ≤ b) (n : ℕ) :
    Real.sin (Real.arccos (a / Real.sqrt b)) * (Real.sqrt b)⁻¹ ^ n *
        coeff n (quadraticInverse a b) =
      Real.sin (((n : ℝ) + 1) * Real.arccos (a / Real.sqrt b)) := by
  have hs : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  have hp : (Real.sqrt b)⁻¹ ^ n * Real.sqrt b ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hs, one_pow]
  calc
    _ = (Real.sqrt b)⁻¹ ^ n *
        (coeff n (quadraticInverse a b) * Real.sin (Real.arccos (a / Real.sqrt b))) := by
      ring
    _ = (Real.sqrt b)⁻¹ ^ n *
        (Real.sqrt b ^ n *
          Real.sin (((n : ℝ) + 1) * Real.arccos (a / Real.sqrt b))) := by
      rw [coeff_quadraticInverse_mul_sin_arccos hb hab]
    _ = _ := by rw [← mul_assoc, hp, one_mul]

/-- In the interior, the inverse quadratic coefficient is the usual sine quotient. -/
theorem coeff_quadraticInverse_eq_sin_div {a b : ℝ} (hb : 0 < b)
    (hab : a ^ 2 < b) (n : ℕ) :
    coeff n (quadraticInverse a b) =
      Real.sqrt b ^ n * Real.sin (((n : ℝ) + 1) * Real.arccos (a / Real.sqrt b)) /
        Real.sin (Real.arccos (a / Real.sqrt b)) := by
  have hsq : (a / Real.sqrt b) ^ 2 < 1 := by
    rw [div_pow, Real.sq_sqrt hb.le]
    exact (div_lt_one hb).mpr hab
  have hs : 0 < Real.sin (Real.arccos (a / Real.sqrt b)) := by
    rw [Real.sin_arccos]
    exact Real.sqrt_pos.mpr (sub_pos.mpr hsq)
  exact (eq_div_iff hs.ne').mpr (coeff_quadraticInverse_mul_sin_arccos hb hab.le n)

end RealRooted.EffectiveBKW
