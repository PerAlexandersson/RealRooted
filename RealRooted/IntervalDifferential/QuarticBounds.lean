/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.CubicDisk
public import RealRooted.IntervalDifferential.QuarticSeeds

/-!
# Coefficient and evaluation bounds from the quartic disk

The quartic seed `X⁴ + kX² + p` is controlled by the quadratic in the
squared variable, `u² + ku + p`. Its roots lift to actual quartic roots.
-/

public noncomputable section

open Polynomial

namespace RealRooted.IntervalDifferential

/-- Every root of the squared-variable quadratic inherits the quartic disk bound. -/
theorem quadratic_root_norm_le_of_quartic_disk (k p : ℝ)
    (hroots : ∀ c : ℂ,
      ((X ^ 4 + C k * X ^ 2 + C p : ℝ[X]).map (algebraMap ℝ ℂ)).eval c = 0 →
        Complex.normSq c ≤ 13 / 3)
    (u : ℂ) (hu : u ^ 2 + (k : ℂ) * u + (p : ℂ) = 0) :
    ‖u‖ ≤ 13 / 3 := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u (n := 2) (by norm_num)
  have hroot :
      ((X ^ 4 + C k * X ^ 2 + C p : ℝ[X]).map (algebraMap ℝ ℂ)).eval c = 0 := by
    simp only [Polynomial.map_add, Polynomial.map_pow, map_X,
      Polynomial.map_mul, map_C, eval_add, eval_pow, eval_X,
      eval_mul, eval_C]
    have hc4 : c ^ 4 = u ^ 2 := by
      calc
        c ^ 4 = (c ^ 2) ^ 2 := by ring
        _ = u ^ 2 := by rw [hc]
    calc
      c ^ 4 + (k : ℂ) * c ^ 2 + (p : ℂ) =
          u ^ 2 + (k : ℂ) * u + (p : ℂ) := by rw [hc4, hc]
      _ = 0 := hu
  have hnorm : Complex.normSq c = ‖u‖ := by
    calc
      Complex.normSq c = ‖c‖ ^ 2 := Complex.normSq_eq_norm_sq c
      _ = ‖c ^ 2‖ := by rw [norm_pow]
      _ = ‖u‖ := by rw [hc]
  simpa only [hnorm] using hroots c hroot

/-- The product of the two quadratic roots bounds the constant coefficient. -/
theorem quartic_constant_abs_le_of_disk (k p : ℝ)
    (hroots : ∀ c : ℂ,
      ((X ^ 4 + C k * X ^ 2 + C p : ℝ[X]).map (algebraMap ℝ ℂ)).eval c = 0 →
        Complex.normSq c ≤ 13 / 3) :
    |p| ≤ (13 / 3 : ℝ) ^ 2 := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq
    ((k : ℂ) ^ 2 - 4 * (p : ℂ)) (n := 2) (by norm_num)
  let u : ℂ := (-(k : ℂ) + d) / 2
  let v : ℂ := (-(k : ℂ) - d) / 2
  have hsum : u + v = -(k : ℂ) := by dsimp [u, v]; ring
  have hprod : u * v = (p : ℂ) := by
    dsimp [u, v]
    calc
      (-(k : ℂ) + d) / 2 * ((-(k : ℂ) - d) / 2) =
          ((k : ℂ) ^ 2 - d ^ 2) / 4 := by ring
      _ = (p : ℂ) := by rw [hd]; ring
  have hu : u ^ 2 + (k : ℂ) * u + (p : ℂ) = 0 := by
    calc
      u ^ 2 + (k : ℂ) * u + (p : ℂ) =
          u * (u + v + (k : ℂ)) + ((p : ℂ) - u * v) := by ring
      _ = 0 := by rw [hsum, hprod]; ring
  have hv : v ^ 2 + (k : ℂ) * v + (p : ℂ) = 0 := by
    calc
      v ^ 2 + (k : ℂ) * v + (p : ℂ) =
          v * (u + v + (k : ℂ)) + ((p : ℂ) - u * v) := by ring
      _ = 0 := by rw [hsum, hprod]; ring
  have hub := quadratic_root_norm_le_of_quartic_disk k p hroots u hu
  have hvb := quadratic_root_norm_le_of_quartic_disk k p hroots v hv
  have hpabs : |p| = ‖u‖ * ‖v‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real p, ← hprod, norm_mul]
  rw [hpabs]
  rw [pow_two]
  exact mul_le_mul hub hvb (norm_nonneg _) (by norm_num)

private theorem quadratic_real_root_abs_le_of_quartic_disk (k p r : ℝ)
    (hroots : ∀ c : ℂ,
      ((X ^ 4 + C k * X ^ 2 + C p : ℝ[X]).map (algebraMap ℝ ℂ)).eval c = 0 →
        Complex.normSq c ≤ 13 / 3)
    (hr : r ^ 2 + k * r + p = 0) : |r| ≤ 13 / 3 := by
  have hrc : (r : ℂ) ^ 2 + (k : ℂ) * (r : ℂ) + (p : ℂ) = 0 := by
    exact_mod_cast hr
  have hb := quadratic_root_norm_le_of_quartic_disk k p hroots (r : ℂ) hrc
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hb

/-- The quadratic discriminant cannot exceed four times the disk radius squared. -/
theorem quartic_discriminant_le_of_disk (k p : ℝ)
    (hroots : ∀ c : ℂ,
      ((X ^ 4 + C k * X ^ 2 + C p : ℝ[X]).map (algebraMap ℝ ℂ)).eval c = 0 →
        Complex.normSq c ≤ 13 / 3) :
    k ^ 2 - 4 * p ≤ 4 * (13 / 3 : ℝ) ^ 2 := by
  by_cases hneg : k ^ 2 - 4 * p < 0
  · nlinarith
  let s := Real.sqrt (k ^ 2 - 4 * p)
  have hs : s ^ 2 = k ^ 2 - 4 * p := Real.sq_sqrt (le_of_not_gt hneg)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  let a := (-k + s) / 2
  let b := (-k - s) / 2
  have ha : a ^ 2 + k * a + p = 0 := by dsimp [a]; nlinarith [hs]
  have hb : b ^ 2 + k * b + p = 0 := by dsimp [b]; nlinarith [hs]
  have hab := quadratic_real_root_abs_le_of_quartic_disk k p a hroots ha
  have hbb := quadratic_real_root_abs_le_of_quartic_disk k p b hroots hb
  have has : a - b = s := by dsimp [a, b]; ring
  have ha_le := (abs_le.mp hab).2
  have hb_ge := (abs_le.mp hbb).1
  have hs_le : s ≤ 2 * (13 / 3 : ℝ) := by linarith
  nlinarith [sq_nonneg (s - 2 * (13 / 3 : ℝ))]

/-- Appendix C.3's quadratic lower bound, derived from the actual quartic disk. -/
theorem quartic_quadratic_lower_bound_of_disk (k p x : ℝ)
    (hroots : ∀ c : ℂ,
      ((X ^ 4 + C k * X ^ 2 + C p : ℝ[X]).map (algebraMap ℝ ℂ)).eval c = 0 →
        Complex.normSq c ≤ 13 / 3) :
    -(13 / 3 : ℝ) ^ 2 ≤ x ^ 2 + k * x + p := by
  have hdisc := quartic_discriminant_le_of_disk k p hroots
  nlinarith [sq_nonneg (x + k / 2)]

/-- The quadratic factor is strictly positive beyond the disk radius. -/
theorem quartic_quadratic_eval_nine_pos_of_disk (k p : ℝ)
    (hroots : ∀ c : ℂ,
      ((X ^ 4 + C k * X ^ 2 + C p : ℝ[X]).map (algebraMap ℝ ℂ)).eval c = 0 →
        Complex.normSq c ≤ 13 / 3) :
    0 < 81 + 9 * k + p := by
  by_cases hneg : k ^ 2 - 4 * p < 0
  · nlinarith [sq_nonneg (9 + k / 2)]
  let s := Real.sqrt (k ^ 2 - 4 * p)
  have hs : s ^ 2 = k ^ 2 - 4 * p := Real.sq_sqrt (le_of_not_gt hneg)
  let a := (-k + s) / 2
  let b := (-k - s) / 2
  have ha : a ^ 2 + k * a + p = 0 := by dsimp [a]; nlinarith [hs]
  have hb : b ^ 2 + k * b + p = 0 := by dsimp [b]; nlinarith [hs]
  have hab := quadratic_real_root_abs_le_of_quartic_disk k p a hroots ha
  have hbb := quadratic_real_root_abs_le_of_quartic_disk k p b hroots hb
  have ha9 : 0 < 9 - a := by have := (abs_le.mp hab).2; linarith
  have hb9 : 0 < 9 - b := by have := (abs_le.mp hbb).2; linarith
  have hfactor : 81 + 9 * k + p = (9 - a) * (9 - b) := by
    dsimp [a, b]
    nlinarith [hs]
  rw [hfactor]
  exact mul_pos ha9 hb9

/-- The three scalar hypotheses of the checked quartic seed follow from the disk. -/
theorem quartic_seed_scalar_bounds_of_disk (k p : ℝ)
    (hroots : ∀ c : ℂ,
      ((X ^ 4 + C k * X ^ 2 + C p : ℝ[X]).map (algebraMap ℝ ℂ)).eval c = 0 →
        Complex.normSq c ≤ 13 / 3) :
    0 < 33 - 3 * k + p ∧ p < 45 / 2 ∧ 0 < 81 + 9 * k + p := by
  have hlow := quartic_quadratic_lower_bound_of_disk k p (-3) hroots
  have hp := quartic_constant_abs_le_of_disk k p hroots
  have hlast := quartic_quadratic_eval_nine_pos_of_disk k p hroots
  constructor
  · nlinarith
  constructor
  · have := (abs_le.mp hp).2
    nlinarith
  · exact hlast

/-- Every transformed quartic satisfying the actual complex disk condition
has four simple roots strictly inside `(-1, 1)`. -/
theorem zigzagTransform_quartic_roots_of_disk (k p : ℝ)
    (hroots : ∀ c : ℂ,
      ((X ^ 4 + C k * X ^ 2 + C p : ℝ[X]).map (algebraMap ℝ ℂ)).eval c = 0 →
        Complex.normSq c ≤ 13 / 3) :
    (zigzagTransform (X ^ 4 + C k * X ^ 2 + C p)).Splits ∧
      (zigzagTransform (X ^ 4 + C k * X ^ 2 + C p)).roots.Nodup ∧
      ∀ r ∈ (zigzagTransform (X ^ 4 + C k * X ^ 2 + C p)).roots,
        -1 < r ∧ r < 1 := by
  obtain ⟨hzero, hmid, hone⟩ := quartic_seed_scalar_bounds_of_disk k p hroots
  exact zigzagTransform_quartic_roots_of_signs k p hzero hmid hone

end RealRooted.IntervalDifferential
