/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Lower bounds for the real part from the square

For `z : ℂ` and `h > 0`, the condition `h < |Re z|` can be read off `z ^ 2` by a polynomial
inequality, which avoids square roots.  This lets one track the real part of a continuous family
of complex numbers across a preconnected set without choosing branches of the square root.

## Main statements

* `Complex.lt_abs_re_iff_sq`: `h < |z.re|` iff `0 < (z ^ 2).im ^ 2 + 4 * h ^ 2 * (z ^ 2).re
  - 4 * h ^ 4`.
* `Complex.lt_abs_re_of_sq_mul_eq`: the same test for `z ^ 2 = N / D`, cleared of denominators.
* `IsPreconnected.lt_re_of_sq_pos`: on a preconnected set where the squared test holds, a
  continuous real part that is positive at one point stays above `h`.
-/

@[expose] public section

open Complex

namespace Complex

/-- `h < |Re z|` can be read off `z²`: with `z = x + iy`,
`(z²).im² + 4h²(z²).re - 4h⁴ = 4(x² - h²)(y² + h²)`. -/
theorem lt_abs_re_iff_sq (z : ℂ) {h : ℝ} (hh : 0 < h) :
    h < |z.re| ↔ 0 < ((z ^ 2).im) ^ 2 + 4 * h ^ 2 * (z ^ 2).re - 4 * h ^ 4 := by
  have key : ((z ^ 2).im) ^ 2 + 4 * h ^ 2 * (z ^ 2).re - 4 * h ^ 4
      = 4 * (z.re ^ 2 - h ^ 2) * (z.im ^ 2 + h ^ 2) := by
    simp only [pow_two, mul_re, mul_im]; ring
  rw [key]
  have hp : 0 < z.im ^ 2 + h ^ 2 := by positivity
  constructor
  · intro H
    have : h ^ 2 < z.re ^ 2 := by
      rw [← sq_abs z.re]; exact pow_lt_pow_left₀ H hh.le two_ne_zero
    have : 0 < z.re ^ 2 - h ^ 2 := by linarith
    positivity
  · intro H
    have h1 : 0 < z.re ^ 2 - h ^ 2 := by
      by_contra hc
      push Not at hc
      have : 4 * (z.re ^ 2 - h ^ 2) * (z.im ^ 2 + h ^ 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hp.le
      linarith
    rw [← sq_abs z.re] at h1
    nlinarith [abs_nonneg z.re]

/-- The same test for `z² = N / D`, cleared of denominators. -/
theorem lt_abs_re_of_sq_mul_eq (z N D : ℂ) {h : ℝ} (hh : 0 < h) (hzD : z ^ 2 * D = N)
    (hpos : 0 < (N * (starRingEnd ℂ) D).im ^ 2
      + 4 * h ^ 2 * (N * (starRingEnd ℂ) D).re * Complex.normSq D
      - 4 * h ^ 4 * (Complex.normSq D) ^ 2) :
    h < |z.re| := by
  have hN : N * (starRingEnd ℂ) D = z ^ 2 * (Complex.normSq D : ℂ) := by
    rw [← hzD, mul_assoc, Complex.mul_conj]
  rw [hN, Complex.re_mul_ofReal, Complex.im_mul_ofReal] at hpos
  rw [Complex.lt_abs_re_iff_sq z hh]
  set n := Complex.normSq D
  have hn : 0 ≤ n := Complex.normSq_nonneg D
  have key : ((z ^ 2).im * n) ^ 2 + 4 * h ^ 2 * ((z ^ 2).re * n) * n - 4 * h ^ 4 * n ^ 2
      = n ^ 2 * (((z ^ 2).im) ^ 2 + 4 * h ^ 2 * (z ^ 2).re - 4 * h ^ 4) := by ring
  rw [key] at hpos
  by_contra hc
  push Not at hc
  have : n ^ 2 * (((z ^ 2).im) ^ 2 + 4 * h ^ 2 * (z ^ 2).re - 4 * h ^ 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
  linarith

end Complex

/-- On a preconnected set where the squared test holds everywhere, a continuous real part that
is positive at one point stays above `h` (it cannot cross `[-h, h]`). -/
theorem IsPreconnected.lt_re_of_sq_pos {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {H : X → ℂ} {h : ℝ} (hh : 0 < h)
    (hc : ContinuousOn (fun x => (H x).re) S)
    (hpos : ∀ x ∈ S, 0 < ((H x ^ 2).im) ^ 2 + 4 * h ^ 2 * (H x ^ 2).re - 4 * h ^ 4)
    {x₀ : X} (hx₀ : x₀ ∈ S) (h0 : 0 < (H x₀).re) :
    ∀ x ∈ S, h < (H x).re := by
  intro x hx
  have habs := (Complex.lt_abs_re_iff_sq (H x) hh).2 (hpos x hx)
  by_contra hle
  push Not at hle
  have hneg : (H x).re < 0 := by
    rcases lt_abs.1 habs with h1 | h1 <;> linarith
  obtain ⟨y, hy, hy0⟩ := hS.intermediate_value hx hx₀ hc ⟨hneg.le, h0.le⟩
  have := (Complex.lt_abs_re_iff_sq (H y) hh).2 (hpos y hy)
  simp only at hy0
  rw [hy0, abs_zero] at this
  linarith
