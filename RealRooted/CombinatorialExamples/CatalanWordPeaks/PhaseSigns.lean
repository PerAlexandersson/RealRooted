/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.RayMeans
public import RealRooted.CombinatorialExamples.CatalanWordPeaks.Phase
import Mathlib.Tactic

/-!
# The actual near-ray phase and its checkpoint signs

We identify the explicit angular phase using Mathlib's principal logarithm
and argument. Root selection belongs to the standard sign-change interface.

Source: ProgramComputer, *Strict peaks in Catalan words*, analytic proof,
ISC license. Copyright 2026 ProgramComputer

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
-/

public noncomputable section

namespace RealRooted.CatalanWordPeaks.CutGeometry

open Set Real
open scoped ComplexConjugate

private def unitOf (x : ℂ) : ℂ := x / (‖x‖ : ℂ)

private theorem unitOf_mul (x y : ℂ) : unitOf (x * y) = unitOf x * unitOf y := by
  simp only [unitOf, norm_mul, Complex.ofReal_mul, div_mul_div_comm]

private theorem unitOf_div (x y : ℂ) : unitOf (x / y) = unitOf x / unitOf y := by
  simp only [unitOf, norm_div, Complex.ofReal_div]
  ring

private theorem unitOf_pow (x : ℂ) (n : ℕ) : unitOf (x ^ n) = unitOf x ^ n := by
  simp only [unitOf, norm_pow, Complex.ofReal_pow, div_pow]

private theorem unitOf_inv (x : ℂ) : unitOf x⁻¹ = (unitOf x)⁻¹ := by
  simp only [unitOf, norm_inv, Complex.ofReal_inv, inv_div, div_inv_eq_mul]
  rw [div_eq_mul_inv, mul_comm]

private theorem unitOf_positive {r : ℝ} (hr : 0 < r) : unitOf (r : ℂ) = 1 := by
  rw [unitOf, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  exact div_self (Complex.ofReal_ne_zero.mpr hr.ne')

private theorem unitOf_exp (z : ℂ) :
    unitOf (Complex.exp z) = Complex.exp ((z.im : ℂ) * Complex.I) := by
  rw [unitOf, Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_sub]
  congr 1
  linear_combination -(Complex.re_add_im z)

private theorem unitOf_principalRoot {z : ℂ} (h : z ≠ 0) :
    unitOf (principalRoot z) = Complex.exp (((z.arg / 2 : ℝ) : ℂ) * Complex.I) := by
  rw [principalRoot, Complex.cpow_def_of_ne_zero h, ← div_eq_mul_inv, unitOf_exp,
    Complex.div_ofNat_im, Complex.log_im]

private theorem arg_eq_arctan {z : ℂ} (h : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  rw [← Complex.tan_arg, Real.arctan_tan
    (Complex.neg_pi_div_two_lt_arg_iff.2 (.inl h)) (Complex.arg_lt_pi_div_two_iff.2 (.inl h))]

private theorem unitOf_arg {z : ℂ} (hz : z ≠ 0) :
    unitOf z = Complex.exp ((z.arg : ℂ) * Complex.I) := by
  apply (div_eq_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))).2
  simpa only [mul_comm] using (Complex.norm_mul_exp_arg_mul_I z).symm

private theorem sin_eq_sqrt_cos {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    Real.sqrt (1 - Real.cos θ ^ 2) = Real.sin θ := by
  have hp : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, hθ.2.trans (by linarith [Real.pi_pos])⟩
  rw [show 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 by linarith [Real.sin_sq_add_cos_sq θ],
    Real.sqrt_sq hp]

private theorem nearPoint_polar_angle {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    nearPoint (Real.cos θ) = (radius (Real.cos θ) : ℂ) *
      Complex.exp ((θ : ℂ) * Complex.I) := by
  have hd : 0 < Real.cos θ := (cosine_in_unit hθ).1
  apply Complex.ext
  · change radius (Real.cos θ) * Real.cos θ =
      ((radius (Real.cos θ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  · rw [nearPoint_im_eq hd, sin_eq_sqrt_cos ⟨hθ.1.le, hθ.2.le⟩,
      Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- The conjugate near factor has an explicit argument in the lower half-plane. -/
private theorem near_conjugate_argument {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (1 - nearPoint (Real.cos θ) / conj (nearPoint (Real.cos θ)) : ℂ) ≠ 0 ∧
      (1 - nearPoint (Real.cos θ) / conj (nearPoint (Real.cos θ)) : ℂ).arg =
        θ - Real.pi / 2 := by
  let d := Real.cos θ
  let s := Real.sin θ
  let a := radius d
  let z := nearPoint d
  let q : ℂ := 1 - z / conj z
  have ⟨hd, hD⟩ : 0 < d ∧ d < 1 := cosine_in_unit hθ
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hθ.1 (hθ.2.trans (by linarith [Real.pi_pos]))
  have ha : 0 < a := radius_pos hd.le
  have haz : ‖z‖ = a := nearPoint_norm hd hD
  have hz : z ≠ 0 := norm_pos_iff.mp (by rw [haz]; exact ha)
  have hzc : conj z ≠ 0 := fun h => hz (by simpa using congrArg (fun x : ℂ => conj x) h)
  have hzr : z.re = a * d := rfl
  have hzi : z.im = a * s := by
    rw [show z.im = a * Real.sqrt (1 - d ^ 2) from nearPoint_im_eq hd]
    rw [show Real.sqrt (1 - d ^ 2) = s from sin_eq_sqrt_cos ⟨hθ.1.le, hθ.2.le⟩]
  have htrig : s ^ 2 + d ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hzz : z * conj z = ((a ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, haz]
  have hq_form : q = (↑(2 * s) : ℂ) * Complex.exp (((θ - Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    have hrat : z / conj z = z ^ 2 / ((a ^ 2 : ℝ) : ℂ) := by
      rw [← hzz]
      field_simp [hz, hzc]
    rw [show q = 1 - z / conj z by rfl, hrat]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.div_ofReal_re, pow_two, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Real.cos_sub,
        Real.cos_pi_div_two,
        Real.sin_pi_div_two, mul_zero, mul_one, zero_add, hzr, hzi]
      field_simp [ha.ne']
      nlinarith only [htrig]
    · simp only [Complex.sub_im, Complex.one_im, Complex.div_ofReal_im, pow_two, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im, Real.sin_sub,
        Real.cos_pi_div_two,
        Real.sin_pi_div_two, mul_zero, mul_one, zero_sub, hzr, hzi]
      field_simp [ha.ne']
      ring
  have hq0 : q ≠ 0 := by
    rw [hq_form]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) (Complex.exp_ne_zero _)
  have hq_arg : q.arg = θ - Real.pi / 2 := by
    rw [hq_form, Complex.exp_mul_I]
    apply Complex.arg_mul_cos_add_sin_mul_I (by positivity)
    exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  exact ⟨hq0, hq_arg⟩

/-- The product of the two cross factors has positive real part and explicit components. -/
private theorem near_cross_parts {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    let d := Real.cos θ
    let a := radius d
    let z := nearPoint d
    let w := farPoint d
    let x := (1 - z / w) * (1 - z / conj w)
    x.re = 4 * a ^ 2 * d ∧ x.im = 4 * a ^ 4 * d * Real.sin θ := by
  let d := Real.cos θ
  let s := Real.sin θ
  let a := radius d
  let z := nearPoint d
  let w := farPoint d
  let u : ℂ := 1 - z / w
  let v : ℂ := 1 - z / conj w
  have ⟨hd, hD⟩ : 0 < d ∧ d < 1 := cosine_in_unit hθ
  have ha : 0 < a := radius_pos hd.le
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have haz : ‖z‖ = a := nearPoint_norm hd hD
  have haw : ‖w‖ = a⁻¹ := farPoint_norm hd hD
  have hw : w ≠ 0 := norm_pos_iff.mp (by rw [haw]; exact inv_pos.2 ha)
  have hwc : conj w ≠ 0 := fun h => hw (by simpa using congrArg (fun x : ℂ => conj x) h)
  have hzr : z.re = a * d := rfl
  have hzi : z.im = a * s := by
    rw [show z.im = a * Real.sqrt (1 - d ^ 2) from nearPoint_im_eq hd]
    rw [show Real.sqrt (1 - d ^ 2) = s from sin_eq_sqrt_cos ⟨hθ.1.le, hθ.2.le⟩]
  have htrig : s ^ 2 + d ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have har : a ^ 2 * (1 + 2 * d) = 1 := radius_relation hd.le
  have hww : w * conj w = ((a⁻¹ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, haw]
  have hws : w + conj w = ((-(2 * a * d) : ℝ) : ℂ) := by
    rw [Complex.add_conj]
    change ((2 * (-(a * d)) : ℝ) : ℂ) = _
    push_cast
    ring
  have hx_form : u * v = 1 + ((2 * a ^ 3 * d : ℝ) : ℂ) * z + ((a ^ 2 : ℝ) : ℂ) * z ^ 2 := by
    calc
      _ = 1 - z * (w + conj w) / (w * conj w) + z ^ 2 / (w * conj w) := by
        dsimp only [u, v]
        field_simp [hw, hwc]
        ring
      _ = _ := by
        rw [hws, hww]
        push_cast
        field_simp [haC]
        ring
  have hxr : (u * v).re = 4 * a ^ 2 * d := by
    calc
      _ = 1 + (a ^ 2) ^ 2 * (4 * d ^ 2 - (s ^ 2 + d ^ 2)) := by
        rw [hx_form]
        simp only [Complex.add_re, Complex.one_re, pow_two, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, hzr, hzi]
        ring
      _ = (a ^ 2 * (1 + 2 * d)) ^ 2 + (a ^ 2) ^ 2 * (4 * d ^ 2 - 1) := by rw [htrig, har, one_pow]
      _ = (4 * a ^ 2 * d) * (a ^ 2 * (1 + 2 * d)) := by ring
      _ = _ := by rw [har, mul_one]
  have hxi : (u * v).im = 4 * a ^ 4 * d * s := by
    rw [hx_form]
    simp only [Complex.add_im, Complex.one_im, pow_two, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, zero_add, add_zero, hzr, hzi]
    ring
  exact ⟨hxr, hxi⟩

/-- Principal roots of right-half-plane factors add their half arguments without wrapping. -/
private theorem unitOf_principalRoot_mul {u v : ℂ} (hur : 0 < u.re) (hvr : 0 < v.re) :
    unitOf (principalRoot u) * unitOf (principalRoot v) =
      Complex.exp (((u * v).arg / 2 : ℝ) * Complex.I) := by
  have hu : u ≠ 0 := fun h => by simp [h] at hur
  have hv : v ≠ 0 := fun h => by simp [h] at hvr
  have harg : (u * v).arg = u.arg + v.arg := by
    apply Complex.arg_mul hu hv
    have hU := Complex.neg_pi_div_two_lt_arg_iff.2 (.inl hur)
    have hV := Complex.neg_pi_div_two_lt_arg_iff.2 (.inl hvr)
    have hU' := Complex.arg_lt_pi_div_two_iff.2 (.inl hur)
    have hV' := Complex.arg_lt_pi_div_two_iff.2 (.inl hvr)
    exact ⟨by linarith, by linarith⟩
  rw [unitOf_principalRoot hu, unitOf_principalRoot hv, ← Complex.exp_add, ← add_mul,
    ← Complex.ofReal_add, ← add_div, ← harg]

private theorem phase_algebra {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    unitOf (-rayPrefactor (Real.cos θ) 0 (nearPoint (Real.cos θ))) =
      Complex.exp ((phaseCorrection θ : ℂ) * Complex.I) := by
  let d := Real.cos θ
  let s := Real.sin θ
  let a := radius d
  let z := nearPoint d
  let w := farPoint d
  let k : ℂ := 1 - z ^ 2
  let u : ℂ := 1 - z / w
  let v : ℂ := 1 - z / conj w
  let q : ℂ := 1 - z / conj z
  have ⟨hd, hD⟩ : 0 < d ∧ d < 1 := cosine_in_unit hθ
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hθ.1 (hθ.2.trans (by linarith [Real.pi_pos]))
  have ha : 0 < a := radius_pos hd.le
  have haz : ‖z‖ = a := nearPoint_norm hd hD
  have haw : ‖w‖ = a⁻¹ := farPoint_norm hd hD
  have hzr : z.re = a * d := rfl
  have hzi : z.im = a * s := by
    rw [show z.im = a * Real.sqrt (1 - d ^ 2) from nearPoint_im_eq hd]
    rw [show Real.sqrt (1 - d ^ 2) = s from sin_eq_sqrt_cos ⟨hθ.1.le, hθ.2.le⟩]
  have htrig : s ^ 2 + d ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have har : a ^ 2 * (1 + 2 * d) = 1 := radius_relation hd.le
  obtain ⟨hq0, hq_arg⟩ := near_conjugate_argument hθ
  obtain ⟨hxr, hxi⟩ := near_cross_parts hθ
  have hcross_arg : (u * v).arg = Real.arctan (s / (1 + 2 * d)) := by
    rw [arg_eq_arctan (z := u * v) (by rw [hxr]; positivity), hxr, hxi]
    congr 1
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    linear_combination (4 * a ^ 2 * d * s) * har
  have hzw : ‖z / w‖ < 1 := by
    rw [norm_div, haz, haw, div_inv_eq_mul, ← pow_two]
    exact radius_sq_lt_one hd
  have hzwc : ‖z / conj w‖ < 1 := by
    simpa only [norm_div, Complex.norm_conj] using hzw
  have hur : 0 < u.re := by
    dsimp only [u]
    rw [Complex.sub_re, Complex.one_re, sub_pos]
    exact (Complex.re_le_norm _).trans_lt hzw
  have hvr : 0 < v.re := by
    dsimp only [v]
    rw [Complex.sub_re, Complex.one_re, sub_pos]
    exact (Complex.re_le_norm _).trans_lt hzwc
  have hkr : k.re = 2 * a ^ 2 * (1 + d - d ^ 2) := by
    dsimp only [k]
    simp only [Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re, hzr, hzi]
    linear_combination -har + a ^ 2 * htrig
  have hki : k.im = -(2 * a ^ 2 * d * s) := by
    dsimp only [k]
    simp only [Complex.sub_im, Complex.one_im, pow_two, Complex.mul_im, hzr, hzi]
    ring
  have hD0 : 0 < 1 + d - d ^ 2 := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hD.le)]
  have hkr0 : 0 < k.re := by rw [hkr]; positivity
  have hk : k ≠ 0 := fun h => by simp [h] at hkr0
  have hk_arg : k.arg = -Real.arctan (d * s / (1 + d - d ^ 2)) := by
    rw [arg_eq_arctan hkr0, hkr, hki, ← Real.arctan_neg]
    congr 1
    field_simp [ha.ne', hD0.ne']
  have hquartic : quartic (scale d) z = 0 :=
    (quartic_zero_iff hd hD z).2 (.inl rfl)
  have hden : 2 * z * ((scale d : ℂ) - z) = k ^ 2 / 2 := by
    dsimp only [k]
    unfold quartic at hquartic
    linear_combination -(1 / 2 : ℂ) * hquartic
  have hB : -rayPrefactor d 0 z =
      2 * (principalRoot q * (principalRoot u * principalRoot v)) / k ^ 2 := by
    rw [rayPrefactor_near_form, neg_div, neg_neg, hden, div_div_eq_mul_div]
    dsimp only [cutFactor, q, u, v]
    ring
  have hx_phase := unitOf_principalRoot_mul hur hvr
  rw [hcross_arg] at hx_phase
  change unitOf (-rayPrefactor d 0 z) = _
  rw [hB, unitOf_div, unitOf_mul, unitOf_mul, unitOf_mul, unitOf_pow,
    show unitOf (2 : ℂ) = 1 from unitOf_positive (by norm_num : (0 : ℝ) < 2), one_mul,
    unitOf_principalRoot hq0, hx_phase, unitOf_arg hk, ← Complex.exp_nat_mul,
    ← Complex.exp_add, ← Complex.exp_sub, hq_arg, hk_arg]
  congr 1
  simp only [phaseCorrection, d, s, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_one,
    Nat.cast_ofNat]
  ring

/-- The actual upper near-ray factor is the exponential of the paper's
explicit phase at the cosine parameter. -/
theorem nearPhaseUnit_eq_exp {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (n : ℕ) :
    nearPhaseUnit (Real.cos θ) n =
      Complex.exp (-(checkpointPhase n θ : ℂ) * Complex.I) := by
  let d := Real.cos θ
  have ⟨hd, hD⟩ : 0 < d ∧ d < 1 := cosine_in_unit hθ
  have hz : unitOf (nearPoint d) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [show nearPoint d = (radius d : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) from
      nearPoint_polar_angle hθ, unitOf_mul, unitOf_positive (radius_pos hd.le), one_mul,
      unitOf, Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one, div_one]
  have hnorm : ‖nearPoint d‖ = radius d := nearPoint_norm hd hD
  have hunit : nearPhaseUnit d n =
      unitOf ((nearPoint d)⁻¹ ^ n * (-rayPrefactor d 0 (nearPoint d))) := by
    rw [nearPhaseUnit, unitOf, norm_mul, norm_pow, norm_inv, norm_neg, hnorm]
    ring
  change nearPhaseUnit d n = _
  rw [hunit, unitOf_mul, unitOf_pow, unitOf_inv, hz, phase_algebra hθ, ← Complex.exp_neg,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  unfold checkpointPhase
  push_cast
  ring

/-- At a phase level, the real part of the actual phase factor is the
alternating sign for that level. -/
theorem nearPhaseUnit_re_at_level {θ : ℝ} {n k : ℕ} (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hk : checkpointPhase n θ = (k : ℝ) * Real.pi) :
    (nearPhaseUnit (Real.cos θ) n).re = (-1 : ℝ) ^ k := by
  rw [nearPhaseUnit_eq_exp hθ, hk,
    show -(↑((k : ℝ) * Real.pi) : ℂ) * Complex.I =
      (k : ℂ) * (-(Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_nat_mul, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  rw [show ((-1 : ℂ)⁻¹) = ((-1 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- The actual strict-peak polynomial has the sign prescribed by each
interior level of the explicit phase. -/
theorem eval_sign_at_checkpoint {θ : ℝ} {n k : ℕ} (hn : 150 ≤ n)
    (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hk : 0 < k) (hkm : k < rowDegree n)
    (hphase : checkpointPhase n θ = (k : ℝ) * Real.pi) :
    0 < (-1 : ℝ) ^ k * (polynomial n).eval (-modulus θ) := by
  have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by lia)
  have hkr' : (k : ℝ) + 1 ≤ (rowDegree n : ℝ) := by
    exact_mod_cast (show k + 1 ≤ rowDegree n from hkm)
  have h₁ : Real.pi ≤ checkpointPhase n θ := by
    rw [hphase]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hkr Real.pi_pos.le
  have h₂ : checkpointPhase n θ ≤ ((((n - 1) / 2 : ℕ) : ℝ) - 1) * Real.pi := by
    rw [hphase]
    apply mul_le_mul_of_nonneg_right _ Real.pi_pos.le
    unfold rowDegree at hkr'
    linarith
  obtain ⟨hd, hD⟩ := cosine_in_unit hθ
  obtain ⟨hnd, hsin⟩ := checkpointPhase_interior hn ⟨hθ.1.le, hθ.2.le⟩ h₁ h₂
  rw [← sin_eq_sqrt_cos ⟨hθ.1.le, hθ.2.le⟩] at hsin
  simpa only [modulus, neg_sub] using
    eval_sign_of_nearPhaseUnit hd hD hn hnd hsin (nearPhaseUnit_re_at_level hθ hphase)

/-- The imaginary part of the actual phase factor has the sign for the
zero-based middle rank between the two levels. -/
theorem nearPhaseUnit_im_sign_between {θ : ℝ} {n j : ℕ}
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (hlo : (j : ℝ) * π < checkpointPhase n θ)
    (hhi : checkpointPhase n θ < ((j : ℝ) + 1) * π) :
    0 < (-1 : ℝ) ^ (j + 1) * (nearPhaseUnit (cos θ) n).im := by
  let δ := checkpointPhase n θ - (j : ℝ) * π
  have hδ : 0 < δ := sub_pos.mpr hlo
  have hδ' : δ < π := by dsimp [δ]; linarith
  have happ : checkpointPhase n θ = δ + (j : ℝ) * π := by dsimp [δ]; ring
  have h : sin (checkpointPhase n θ) = (-1 : ℝ) ^ j * sin δ := by
    rw [happ, sin_add_nat_mul_pi]
  have hsign : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [nearPhaseUnit_eq_exp hθ, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_im,
    sin_neg, h, pow_succ]
  calc
    (0 : ℝ) < sin δ := sin_pos_of_pos_of_lt_pi hδ hδ'
    _ = ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) * sin δ := by rw [hsign, one_mul]
    _ = _ := by ring

end RealRooted.CatalanWordPeaks.CutGeometry
