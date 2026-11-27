/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# The four branch points and their angular parameter

We merge the cut geometry and parameter conversion, reusing Mathlib's complex
conjugation identities and monotonicity of cosine.

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

@[expose] public noncomputable section

namespace RealRooted.CatalanWordPeaks.CutGeometry

open scoped ComplexConjugate

/-- The dominant radius when d is the cosine of the dominant angle. -/
def radius (d : ℝ) : ℝ := (Real.sqrt (1 + 2 * d))⁻¹

/-- The scaled length parameter used by the analytic discriminant. -/
def scale (d : ℝ) : ℝ := 2 * d ^ 2 * (1 + d) * radius d ^ 3

/-- The dominant radius is positive for nonnegative cosine. -/
theorem radius_pos {d : ℝ} (hd : 0 ≤ d) : 0 < radius d :=
  inv_pos.mpr (Real.sqrt_pos.2 (by linarith))

/-- The radius satisfies its defining quadratic identity. -/
theorem radius_relation {d : ℝ} (hd : 0 ≤ d) : radius d ^ 2 * (1 + 2 * d) = 1 := by
  have h : 0 < 1 + 2 * d := by linarith
  rw [radius, inv_pow, Real.sq_sqrt h.le, inv_mul_cancel₀ h.ne']

/-- The dominant radius lies inside the unit circle. -/
theorem radius_sq_lt_one {d : ℝ} (hd : 0 < d) : radius d ^ 2 < 1 := by
  have hr := radius_pos hd.le
  have hrel := radius_relation hd.le
  nlinarith [mul_pos (pow_pos hr 2) hd]

/-- The length scale is positive for positive cosine. -/
theorem scale_pos {d : ℝ} (hd : 0 < d) : 0 < scale d := by
  unfold scale
  have h := radius_pos hd.le
  positivity

private theorem quartic_algebra {K : Type*} [CommRing K] (a d x : K)
    (ha : a ^ 2 * (1 + 2 * d) = 1) :
    (1 + x ^ 2) ^ 2 - 4 * (2 * d ^ 2 * (1 + d) * a ^ 3) * x =
      (x ^ 2 - 2 * a * d * x + a ^ 2) *
        (x ^ 2 + 2 * a * d * x + (1 + 2 * d)) := by
  have h₂ : a ^ 2 + (1 + 2 * d) - 4 * a ^ 2 * d ^ 2 = 2 := by
    calc
      _ = a ^ 2 * (1 + 2 * d) * (1 - 2 * d) + (1 + 2 * d) := by ring
      _ = _ := by rw [ha]; ring
  have h₁ : a ^ 2 - (1 + 2 * d) = -4 * d * (1 + d) * a ^ 2 := by
    calc
      _ = a ^ 2 - a ^ 2 * (1 + 2 * d) * (1 + 2 * d) := by rw [ha, one_mul]
      _ = _ := by ring
  symm
  calc
    _ = x ^ 4 + (a ^ 2 + (1 + 2 * d) - 4 * a ^ 2 * d ^ 2) * x ^ 2 +
        2 * a * d * (a ^ 2 - (1 + 2 * d)) * x + a ^ 2 * (1 + 2 * d) := by ring
    _ = _ := by rw [h₂, h₁, ha]; ring

/-- The quartic discriminant evaluated in the complex plane. -/
def quartic (c : ℝ) (x : ℂ) : ℂ := (1 + x ^ 2) ^ 2 - 4 * (c : ℂ) * x

/-- Upper branch point at the dominant radius. -/
def nearPoint (d : ℝ) : ℂ :=
  ⟨radius d * d, Real.sqrt ((radius d) ^ 2 - (radius d * d) ^ 2)⟩

/-- Upper branch point at the farther radius. -/
def farPoint (d : ℝ) : ℂ :=
  ⟨-(radius d * d), Real.sqrt (1 + 2 * d - (radius d * d) ^ 2)⟩

private theorem near_radicand_pos {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    radius d ^ 2 - (radius d * d) ^ 2 > 0 := by
  have ha := radius_pos h₀.le
  have hd : 0 < 1 - d ^ 2 := by nlinarith [mul_pos (sub_pos.mpr h₁) (add_pos zero_lt_one h₀)]
  calc
    _ = radius d ^ 2 * (1 - d ^ 2) := by ring
    _ > 0 := mul_pos (pow_pos ha 2) hd

private theorem far_radicand_pos {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    1 + 2 * d - (radius d * d) ^ 2 > 0 := by
  have hnear := near_radicand_pos h₀ h₁
  have ha := radius_sq_lt_one h₀
  linarith

/-- The near branch point lies in the upper half-plane. -/
theorem nearPoint_im_pos {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) : 0 < (nearPoint d).im :=
  Real.sqrt_pos.2 (near_radicand_pos h₀ h₁)

/-- The far branch point lies in the upper half-plane. -/
theorem farPoint_im_pos {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) : 0 < (farPoint d).im :=
  Real.sqrt_pos.2 (far_radicand_pos h₀ h₁)

/-- The near branch point lies to the right of the imaginary axis. -/
theorem nearPoint_re_pos {d : ℝ} (h₀ : 0 < d) : 0 < (nearPoint d).re :=
  mul_pos (radius_pos h₀.le) h₀

/-- The far branch point lies to the left of the imaginary axis. -/
theorem farPoint_re_neg {d : ℝ} (h₀ : 0 < d) : (farPoint d).re < 0 :=
  neg_lt_zero.mpr (mul_pos (radius_pos h₀.le) h₀)

private theorem nearPoint_normSq {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    Complex.normSq (nearPoint d) = radius d ^ 2 := by
  rw [Complex.normSq_apply]
  change radius d * d * (radius d * d) +
      Real.sqrt (radius d ^ 2 - (radius d * d) ^ 2) *
        Real.sqrt (radius d ^ 2 - (radius d * d) ^ 2) = radius d ^ 2
  rw [Real.mul_self_sqrt (near_radicand_pos h₀ h₁).le]
  ring

private theorem farPoint_normSq {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    Complex.normSq (farPoint d) = 1 + 2 * d := by
  rw [Complex.normSq_apply]
  change -(radius d * d) * -(radius d * d) +
      Real.sqrt (1 + 2 * d - (radius d * d) ^ 2) *
        Real.sqrt (1 + 2 * d - (radius d * d) ^ 2) = 1 + 2 * d
  rw [Real.mul_self_sqrt (far_radicand_pos h₀ h₁).le]
  ring

/-- The near branch point has the dominant radius. -/
theorem nearPoint_norm {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    ‖nearPoint d‖ = radius d := by
  have h := nearPoint_normSq h₀ h₁
  rw [Complex.normSq_eq_norm_sq] at h
  have hr := radius_pos h₀.le
  have hn : 0 ≤ ‖nearPoint d‖ := norm_nonneg _
  nlinarith

/-- The far branch point has the reciprocal radius. -/
theorem farPoint_norm {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    ‖farPoint d‖ = (radius d)⁻¹ := by
  have h := farPoint_normSq h₀ h₁
  rw [Complex.normSq_eq_norm_sq] at h
  have hval : (radius d)⁻¹ ^ 2 = 1 + 2 * d := by
    rw [radius, inv_inv, Real.sq_sqrt (by linarith)]
  rw [← hval] at h
  have hr := inv_pos.mpr (radius_pos h₀.le)
  have hn : 0 ≤ ‖farPoint d‖ := norm_nonneg _
  nlinarith

/-- The near pair has strictly smaller radius than the far pair. -/
theorem norm_order {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    ‖nearPoint d‖ < ‖farPoint d‖ := by
  rw [nearPoint_norm h₀ h₁, farPoint_norm h₀ h₁]
  rw [inv_eq_one_div, lt_div_iff₀ (radius_pos h₀.le), ← pow_two]
  exact radius_sq_lt_one h₀

private theorem conjugate_quadratic (z x : ℂ) :
    (x - z) * (x - conj z) = x ^ 2 - 2 * (z.re : ℂ) * x + (Complex.normSq z : ℂ) := by
  calc
    _ = x ^ 2 - (z + conj z) * x + z * conj z := by ring
    _ = _ := by rw [Complex.add_conj, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.mul_conj]

/-- The exact factorization used for the four radial cuts. -/
theorem quartic_factor {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) (x : ℂ) :
    quartic (scale d) x =
      (x - nearPoint d) * (x - conj (nearPoint d)) *
        ((x - farPoint d) * (x - conj (farPoint d))) := by
  have h : ((radius d : ℂ) ^ 2) * (1 + 2 * (d : ℂ)) = 1 := by
    exact_mod_cast radius_relation h₀.le
  rw [conjugate_quadratic, conjugate_quadratic, nearPoint_normSq h₀ h₁, farPoint_normSq h₀ h₁]
  change quartic (scale d) x =
    (x ^ 2 - 2 * ((radius d * d : ℝ) : ℂ) * x + ((radius d ^ 2 : ℝ) : ℂ)) *
      (x ^ 2 - 2 * ((-(radius d * d) : ℝ) : ℂ) * x + ((1 + 2 * d : ℝ) : ℂ))
  unfold quartic scale
  push_cast
  convert quartic_algebra (radius d : ℂ) (d : ℂ) x h using 1
  ring

/-- The branch-point list exhausts the zeros of the quartic. -/
theorem quartic_zero_iff {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) (x : ℂ) :
    quartic (scale d) x = 0 ↔
      x = nearPoint d ∨ x = conj (nearPoint d) ∨
        x = farPoint d ∨ x = conj (farPoint d) := by
  rw [quartic_factor h₀ h₁]
  simp only [mul_eq_zero, sub_eq_zero]
  tauto

/-- The reciprocal radius is a simple multiple of the radius. -/
theorem radius_inverse_eq {d : ℝ} (h₀ : 0 < d) : (radius d)⁻¹ = radius d * (1 + 2 * d) := by
  rw [inv_eq_one_div, div_eq_iff (radius_pos h₀.le).ne']
  have h := radius_relation h₀.le
  nlinarith

/-- Reverse triangle inequality with the exact radial gap. -/
theorem direct_gap {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    2 * radius d * d ≤ ‖farPoint d - nearPoint d‖ := by
  have h := norm_sub_norm_le (farPoint d) (nearPoint d)
  rw [nearPoint_norm h₀ h₁, farPoint_norm h₀ h₁, radius_inverse_eq h₀] at h
  linarith

/-- Direct cross-pair coefficient on the near ray. -/
theorem near_to_far_bound {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    ‖nearPoint d / (nearPoint d - farPoint d)‖ ≤ 1 / (2 * d) := by
  have hgap := direct_gap h₀ h₁
  have hden : 0 < ‖farPoint d - nearPoint d‖ :=
    (mul_pos (mul_pos (by norm_num) (radius_pos h₀.le)) h₀).trans_le hgap
  rw [norm_div, norm_sub_rev, nearPoint_norm h₀ h₁]
  apply (div_le_div_iff₀ hden (mul_pos (by norm_num) h₀)).mpr
  nlinarith

/-- Direct cross-pair coefficient on the far ray. -/
theorem far_to_near_bound {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    ‖farPoint d / (farPoint d - nearPoint d)‖ ≤ 1 + 1 / (2 * d) := by
  have hgap := direct_gap h₀ h₁
  have hden : 0 < ‖farPoint d - nearPoint d‖ :=
    (mul_pos (mul_pos (by norm_num) (radius_pos h₀.le)) h₀).trans_le hgap
  rw [norm_div, farPoint_norm h₀ h₁]
  apply (div_le_iff₀ hden).mpr
  calc
    _ = (1 + 1 / (2 * d)) * (2 * radius d * d) := by
      rw [radius_inverse_eq h₀]
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgap (by positivity)

private theorem cross_product_re_neg {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    (nearPoint d * farPoint d).re < 0 := by
  rw [Complex.mul_re]
  exact sub_neg.mpr ((mul_neg_of_pos_of_neg (nearPoint_re_pos h₀) (farPoint_re_neg h₀)).trans
    (mul_pos (nearPoint_im_pos h₀ h₁) (farPoint_im_pos h₀ h₁)))

private theorem cross_gap (z w : ℂ) (h : (z * w).re < 0) :
    ‖z‖ < ‖z - conj w‖ := by
  have hnorm := Complex.normSq_sub z (conj w)
  rw [Complex.conj_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hnorm
  have hw : 0 ≤ Complex.normSq (conj w) := Complex.normSq_nonneg _
  have hsq : ‖z‖ ^ 2 < ‖z - conj w‖ ^ 2 := by linarith
  exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Both opposite cross-pair coefficients have absolute value at most one. -/
theorem opposite_cross_bounds {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    ‖nearPoint d / (nearPoint d - conj (farPoint d))‖ ≤ 1 ∧
      ‖farPoint d / (farPoint d - conj (nearPoint d))‖ ≤ 1 := by
  have h := cross_product_re_neg h₀ h₁
  have hnear := cross_gap (nearPoint d) (farPoint d) h
  have hfar := cross_gap (farPoint d) (nearPoint d) (by simpa only [mul_comm] using h)
  constructor
  · rw [norm_div]
    exact (div_le_one ((norm_nonneg _).trans_lt hnear)).mpr hnear.le
  · rw [norm_div]
    exact (div_le_one ((norm_nonneg _).trans_lt hfar)).mpr hfar.le

/-- The distance of a point in the upper half-plane from its conjugate. -/
theorem norm_sub_conjugate (z : ℂ) (h : 0 ≤ z.im) :
    ‖z - conj z‖ = 2 * z.im := by
  rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by norm_num) h)]

/-- The height of the near point in terms of its radius and cosine parameter. -/
theorem nearPoint_im_eq {d : ℝ} (h₀ : 0 < d) :
    (nearPoint d).im = radius d * Real.sqrt (1 - d ^ 2) := by
  change Real.sqrt (radius d ^ 2 - (radius d * d) ^ 2) = _
  rw [show radius d ^ 2 - (radius d * d) ^ 2 = radius d ^ 2 * (1 - d ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (radius_pos h₀.le).le]

/-- The coefficient from the near point's conjugate. -/
theorem near_conjugate_coefficient {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    ‖nearPoint d / (nearPoint d - conj (nearPoint d))‖ =
      1 / (2 * Real.sqrt (1 - d ^ 2)) := by
  rw [norm_div, nearPoint_norm h₀ h₁, norm_sub_conjugate _ (nearPoint_im_pos h₀ h₁).le,
    nearPoint_im_eq h₀]
  have ha := radius_pos h₀.le
  have hsin : 0 < Real.sqrt (1 - d ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  field_simp

/-- The coefficient from the far point's conjugate has magnitude at most one. -/
theorem far_conjugate_bound {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    ‖farPoint d / (farPoint d - conj (farPoint d))‖ ≤ 1 := by
  rw [norm_div, norm_sub_conjugate _ (farPoint_im_pos h₀ h₁).le]
  have himPos := farPoint_im_pos h₀ h₁
  apply (div_le_one (by positivity)).mpr
  have him : (farPoint d).im ^ 2 = 1 + 2 * d - (radius d * d) ^ 2 :=
    Real.sq_sqrt (far_radicand_pos h₀ h₁).le
  have hn : ‖farPoint d‖ ^ 2 = 1 + 2 * d := by
    rw [Complex.sq_norm, farPoint_normSq h₀ h₁]
  have ha : radius d ^ 2 * d ^ 2 ≤ d ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg d) (radius_sq_lt_one h₀).le
  have hd : d ^ 2 ≤ d := by nlinarith [mul_nonneg h₀.le (sub_nonneg.mpr h₁.le)]
  have hsq : ‖farPoint d‖ ^ 2 ≤ (2 * (farPoint d).im) ^ 2 := by
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

private theorem norm_one_sub_near_sq {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    ‖1 - (nearPoint d) ^ 2‖ ^ 2 = 1 + radius d ^ 4 - 2 *
      (2 * (radius d * d) ^ 2 - radius d ^ 2) := by
  have hIm : (nearPoint d).im ^ 2 = radius d ^ 2 - (radius d * d) ^ 2 :=
    Real.sq_sqrt (near_radicand_pos h₀ h₁).le
  have hRe : ((nearPoint d) ^ 2).re = 2 * (radius d * d) ^ 2 - radius d ^ 2 := by
    rw [pow_two, Complex.mul_re]
    change radius d * d * (radius d * d) - (nearPoint d).im * (nearPoint d).im = _
    nlinarith
  rw [Complex.sq_norm, Complex.normSq_sub, map_one, one_mul, Complex.conj_re, map_pow,
    nearPoint_normSq h₀ h₁, hRe]
  ring

private theorem norm_one_sub_near_sq_lower {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    (4 / 3) * radius d ^ 2 < ‖1 - (nearPoint d) ^ 2‖ ^ 2 := by
  let a := radius d
  have hRel : a ^ 2 * (1 + 2 * d) = 1 := radius_relation h₀.le
  have ha : 0 < a := radius_pos h₀.le
  have hd : 0 < 1 - d := sub_pos.mpr h₁
  have hdiff : ‖1 - (nearPoint d) ^ 2‖ ^ 2 - (4 / 3) * a ^ 2 =
      (8 / 3) * a ^ 4 * (1 - d) * (3 * d ^ 2 + 3 * d + 1) := by
    rw [norm_one_sub_near_sq h₀ h₁]
    change 1 + a ^ 4 - 2 * (2 * (a * d) ^ 2 - a ^ 2) - 4 / 3 * a ^ 2 = _
    calc
      _ = (8 / 3) * a ^ 4 * (1 - d) * (3 * d ^ 2 + 3 * d + 1) +
          (1 - a ^ 2 * (1 + 2 * d)) * (1 + a ^ 2 * (1 + 2 * d + 2 / 3 - 4 * d ^ 2)) := by ring
      _ = _ := by rw [hRel]; ring
  have hpos : 0 < (8 / 3) * a ^ 4 * (1 - d) * (3 * d ^ 2 + 3 * d + 1) := by positivity
  linarith

/-- The near-ray factor from the removable denominator has |b₀| < 3. -/
theorem denominator_near_bound {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) :
    ‖nearPoint d / (nearPoint d - (scale d : ℂ))‖ < 3 := by
  let z := nearPoint d
  let c := scale d
  let a := radius d
  have hz : quartic c z = 0 := (quartic_zero_iff h₀ h₁ _).mpr (Or.inl rfl)
  have hpol : (1 - z ^ 2) ^ 2 = 4 * z * ((c : ℂ) - z) := by
    calc
      _ = quartic c z + 4 * z * ((c : ℂ) - z) := by unfold quartic; ring
      _ = _ := by rw [hz, zero_add]
  have hnorm : ‖1 - z ^ 2‖ ^ 2 = 4 * a * ‖z - (c : ℂ)‖ := by
    have h := congrArg norm hpol
    simp only [norm_pow, norm_mul, Complex.norm_ofNat] at h
    rw [norm_sub_rev z (c : ℂ)]
    have hNear : ‖z‖ = a := nearPoint_norm h₀ h₁
    simpa only [hNear] using h
  have hlt : (4 / 3) * a ^ 2 < ‖1 - z ^ 2‖ ^ 2 := norm_one_sub_near_sq_lower h₀ h₁
  rw [hnorm] at hlt
  have ha : 0 < a := radius_pos h₀.le
  have hd : a < 3 * ‖z - (c : ℂ)‖ := by
    have hh : 0 < a * (3 * ‖z - (c : ℂ)‖ - a) := by linarith
    exact sub_pos.mp (pos_of_mul_pos_right hh ha.le)
  have hden : 0 < ‖z - (c : ℂ)‖ := by linarith
  change ‖z / (z - (c : ℂ))‖ < 3
  rw [norm_div, div_lt_iff₀ hden]
  exact (nearPoint_norm h₀ h₁).trans_lt hd

end RealRooted.CatalanWordPeaks.CutGeometry

namespace RealRooted.CatalanWordPeaks.CutGeometry

open Set

/-- The product form used to compare the scale with its transition value. -/
theorem scale_eq_product {d : ℝ} (hd : 0 < d) :
    scale d = 2 * (d / (1 + 2 * d)) ^ 2 * (1 + d) * Real.sqrt (1 + 2 * d) := by
  let r := Real.sqrt (1 + 2 * d)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hsq : r ^ 2 = 1 + 2 * d := Real.sq_sqrt (by linarith)
  change 2 * d ^ 2 * (1 + d) * (r⁻¹) ^ 3 = 2 * (d / (1 + 2 * d)) ^ 2 * (1 + d) * r
  rw [← hsq]
  field_simp

/-- The length parameter increases with the cosine. -/
theorem strictMonoOn_scale : StrictMonoOn scale (Ioi (0 : ℝ)) := by
  intro d hd e he hde
  have hd₀ : 0 < d := hd
  have he₀ : 0 < e := he
  have hpD : 0 < 1 + 2 * d := by linarith
  have hpE : 0 < 1 + 2 * e := by linarith
  have hf : d / (1 + 2 * d) < e / (1 + 2 * e) := by
    apply (div_lt_div_iff₀ hpD hpE).mpr
    nlinarith
  have hs : (d / (1 + 2 * d)) ^ 2 < (e / (1 + 2 * e)) ^ 2 :=
    (sq_lt_sq₀ (by positivity) (by positivity)).mpr hf
  rw [scale_eq_product hd₀, scale_eq_product he₀]
  have hpre : 2 * (d / (1 + 2 * d)) ^ 2 * (1 + d) * Real.sqrt (1 + 2 * d) <
      2 * (e / (1 + 2 * e)) ^ 2 * (1 + d) * Real.sqrt (1 + 2 * d) := by
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_left hs (by norm_num)) (by positivity)) (Real.sqrt_pos.2 hpD)
  have hsqrt : Real.sqrt (1 + 2 * d) ≤ Real.sqrt (1 + 2 * e) :=
    Real.sqrt_le_sqrt (by linarith)
  exact hpre.trans_le (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    hsqrt (Real.sqrt_nonneg _) (by positivity))

/-- The square of the scale at the coalescing near pair. -/
theorem scale_one_sq : scale 1 ^ 2 = 16 / 27 := by
  have hr := radius_relation (d := 1) (by norm_num)
  norm_num at hr
  calc
    _ = 16 * (radius 1 ^ 2) ^ 3 := by unfold scale; ring
    _ = _ := by rw [show radius 1 ^ 2 = 1 / 3 by linarith]; norm_num

/-- The scale remains below one throughout the four-cut regime. -/
theorem scale_sq_lt_one {d : ℝ} (h₀ : 0 < d) (h₁ : d < 1) : (scale d) ^ 2 < 1 := by
  have hscale := scale_one_sq
  have hx : scale d < scale 1 := strictMonoOn_scale h₀ (by norm_num : (1 : ℝ) ∈ Ioi 0) h₁
  have hy := (sq_lt_sq₀ (scale_pos h₀).le (scale_pos (by norm_num : (0 : ℝ) < 1)).le).mpr hx
  linarith

/-- An acute angle has cosine strictly between zero and one. -/
theorem cosine_in_unit {θ : ℝ} (h : θ ∈ Ioo 0 (Real.pi / 2)) :
    0 < Real.cos θ ∧ Real.cos θ < 1 := by
  have hp := Real.pi_pos
  constructor
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1], h.2⟩
  · have hmem : θ ∈ Icc 0 Real.pi := ⟨h.1.le, by linarith [h.2]⟩
    have hzero : (0 : ℝ) ∈ Icc 0 Real.pi := ⟨le_rfl, hp.le⟩
    simpa using Real.strictAntiOn_cos hzero hmem h.1

/-- The positive modulus −t at the scaled value t = 1-c⁻². -/
def modulus (θ : ℝ) : ℝ := ((scale (Real.cos θ)) ^ 2)⁻¹ - 1

/-- The angular order matches increasing positive moduli of negative t. -/
theorem strictMonoOn_modulus : StrictMonoOn modulus (Ioo 0 (Real.pi / 2)) := by
  intro θ hθ φ hφ hθφ
  have hp := Real.pi_pos
  have hθ' : θ ∈ Icc 0 Real.pi := ⟨hθ.1.le, by linarith [hθ.2]⟩
  have hφ' : φ ∈ Icc 0 Real.pi := ⟨hφ.1.le, by linarith [hφ.2]⟩
  have hc := Real.strictAntiOn_cos hθ' hφ' hθφ
  have hθc := (cosine_in_unit hθ).1
  have hφc := (cosine_in_unit hφ).1
  have hs := strictMonoOn_scale hφc hθc hc
  have hθp := scale_pos hθc
  have hφp := scale_pos hφc
  have hpows := (sq_lt_sq₀ hφp.le hθp.le).mpr hs
  unfold modulus
  apply sub_lt_sub_right
  rw [inv_eq_one_div, inv_eq_one_div,
    div_lt_div_iff₀ (pow_pos hθp 2) (pow_pos hφp 2), one_mul, one_mul]
  exact hpows

end RealRooted.CatalanWordPeaks.CutGeometry
