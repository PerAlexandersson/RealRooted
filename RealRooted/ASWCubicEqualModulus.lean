import RealRooted.ASWCubicDominance
import RealRooted.ComplexPowers

/-!
# The equal-modulus cubic ASW branch

This file studies the remaining case where the real and nonreal roots of the
cubic shift-one minor recurrence have equal modulus. It reduces the closed
form to the unit circle and expresses the gap minors through real parts of
powers on that circle.
-/

noncomputable section

namespace RealRooted

open Complex
open scoped ComplexConjugate

/-- Scaling all three characteristic roots by a nonzero real number scales
the degree-`n` closed form by its `n`th power. -/
theorem aswCubicClosedForm_scale (r : ℝ) {w : ℂ}
    (hr : r ≠ 0) (him : w.im ≠ 0) (n : ℕ) :
    aswCubicClosedForm r ((r : ℂ) * w) n =
      (r : ℂ) ^ n * aswCubicClosedForm 1 w n := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have h1w : (1 : ℂ) ≠ w := by
    intro h
    apply him
    rw [← h]
    simp
  have h1c : (1 : ℂ) ≠ conj w := by
    intro h
    apply him
    have hi := congrArg Complex.im h
    simp only [conj_im, one_im] at hi
    linarith
  have hwc : w ≠ conj w := by
    intro h
    apply him
    have hi := congrArg Complex.im h
    simp only [conj_im] at hi
    linarith
  have hrealWeight :
      aswCubicRealModeWeight r ((r : ℂ) * w) = aswCubicRealModeWeight 1 w := by
    simp only [aswCubicRealModeWeight, map_mul, conj_ofReal, Complex.ofReal_one,
      one_pow]
    field_simp [hrC, sub_ne_zero.mpr h1w, sub_ne_zero.mpr h1c]
  have hcomplexWeight :
      aswCubicComplexModeWeight r ((r : ℂ) * w) =
        aswCubicComplexModeWeight 1 w := by
    simp only [aswCubicComplexModeWeight, map_mul, conj_ofReal, Complex.ofReal_one]
    field_simp [hrC, sub_ne_zero.mpr h1w.symm, sub_ne_zero.mpr hwc]
  rw [aswCubicClosedForm_eq_geometricModes,
    aswCubicClosedForm_eq_geometricModes]
  rw [hrealWeight, hcomplexWeight]
  simp only [map_mul, conj_ofReal, mul_pow, Complex.ofReal_one, one_pow]
  ring

private lemma unit_real_weight {w : ℂ} (hunit : w * conj w = 1) :
    aswCubicRealModeWeight 1 w = 1 / (2 - (w + conj w)) := by
  simp only [aswCubicRealModeWeight, Complex.ofReal_one, one_pow]
  congr 1
  linear_combination hunit

private lemma unit_complex_weight_mul {w : ℂ}
    (him : w.im ≠ 0) (hunit : w * conj w = 1) :
    aswCubicComplexModeWeight 1 w * (1 + conj w) =
      -w / (2 - (w + conj w)) := by
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hunit
  have h1w : (1 : ℂ) ≠ w := by
    intro h
    apply him
    rw [← h]
    simp
  have hwc : w ≠ conj w := by
    intro h
    apply him
    have hi := congrArg Complex.im h
    simp only [conj_im] at hi
    linarith
  have hden : (2 : ℂ) - (w + conj w) ≠ 0 := by
    intro h
    have hs : w + conj w = 2 := by linear_combination -h
    have hsquare : (w - 1) ^ 2 = 0 := by linear_combination w * hs - hunit
    exact h1w (sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)).symm
  simp only [aswCubicComplexModeWeight, Complex.ofReal_one]
  field_simp [hw0, sub_ne_zero.mpr h1w.symm, sub_ne_zero.mpr hwc, hden]
  have hmul := congrArg (fun x : ℂ ↦ -(w ^ 2 + conj w) * x) hunit
  linear_combination hmul - w * (1 - w) * hunit

private lemma unit_conj_weight_mul {w : ℂ}
    (him : w.im ≠ 0) (hunit : w * conj w = 1) :
    conj (aswCubicComplexModeWeight 1 w) * (1 + w) =
      -(conj w) / (2 - (w + conj w)) := by
  have h := congrArg conj (unit_complex_weight_mul him hunit)
  simp only [map_mul, map_add, map_one, map_neg, map_div₀, map_sub,
    conj_conj] at h
  have hconjTwo : conj (2 : ℂ) = 2 := by norm_num [Complex.ext_iff]
  rw [hconjTwo] at h
  simpa [add_comm] using h

/-- On the unit circle, the difference controlled by the gap minor is an
explicit quotient of differences of real parts of powers. -/
theorem aswCubicClosedForm_unit_gap_re {w : ℂ}
    (him : w.im ≠ 0) (hunit : w * conj w = 1) (n : ℕ) :
    ((1 : ℂ) + w + conj w) * aswCubicClosedForm 1 w n -
        aswCubicClosedForm 1 w (n + 1) =
      ((w.re - (w ^ (n + 1)).re) / (1 - w.re) : ℝ) := by
  have hnorm : ‖w‖ = 1 := by
    have hn := congrArg norm hunit
    rw [norm_mul, norm_conj, norm_one] at hn
    nlinarith [norm_nonneg w]
  have hrelt : w.re < 1 := by
    calc
      w.re ≤ |w.re| := le_abs_self _
      _ < ‖w‖ := Complex.abs_re_lt_norm.mpr him
      _ = 1 := hnorm
  rw [aswCubicClosedForm_eq_geometricModes 1 w n,
    aswCubicClosedForm_eq_geometricModes 1 w (n + 1)]
  simp only [Complex.ofReal_one, one_pow, pow_succ, mul_one]
  rw [show
    (1 + w + conj w) *
          (aswCubicRealModeWeight 1 w + aswCubicComplexModeWeight 1 w * w ^ n +
            conj (aswCubicComplexModeWeight 1 w) * (conj w) ^ n) -
        (aswCubicRealModeWeight 1 w +
          aswCubicComplexModeWeight 1 w * (w ^ n * w) +
            conj (aswCubicComplexModeWeight 1 w) * ((conj w) ^ n * conj w)) =
      aswCubicRealModeWeight 1 w * (w + conj w) +
        (aswCubicComplexModeWeight 1 w * (1 + conj w)) * w ^ n +
          (conj (aswCubicComplexModeWeight 1 w) * (1 + w)) * (conj w) ^ n by ring]
  rw [unit_real_weight hunit, unit_complex_weight_mul him hunit,
    unit_conj_weight_mul him hunit]
  rw [show
      1 / (2 - (w + conj w)) * (w + conj w) +
          (-w / (2 - (w + conj w))) * w ^ n +
            (-conj w / (2 - (w + conj w))) * (conj w) ^ n =
        ((w + conj w) - (w ^ (n + 1) + (conj w) ^ (n + 1))) /
          (2 - (w + conj w)) by ring]
  simp only [← map_pow, Complex.add_conj, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_one]
  have hden1C : (1 : ℂ) - (w.re : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (sub_pos.mpr hrelt))
  have hden2C : (2 : ℂ) - ((2 * w.re : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith : (2 : ℝ) - 2 * w.re ≠ 0)
  field_simp [hden1C, hden2C]
  push_cast
  ring_nf

/-- A positive-constant cubic with nonnegative ASW gap minors cannot have a
nonreal shift-one characteristic root with the same modulus as its positive
real characteristic root. -/
theorem false_of_aswCubicCharacteristicRoots_equalNorm
    (u : ℕ → ℝ) (hu : ∀ j, 4 ≤ j → u j = 0)
    (r : ℝ) {z : ℂ} (hr : 0 < r) (hz : z.im ≠ 0)
    (hsum : (r : ℂ) + z + conj z = u 1)
    (hpairs : (r : ℂ) * z + (r : ℂ) * conj z + z * conj z = u 0 * u 2)
    (hprod : (r : ℂ) * z * conj z = u 0 ^ 2 * u 3)
    (hnorm : ‖z‖ = r) (hconst : 0 < u 0)
    (hgap : ∀ n, 0 ≤ aswGapToeplitzMinor u n) :
    False := by
  let w : ℂ := z / r
  have hwim : w.im ≠ 0 := by
    simp only [w, Complex.div_im, ofReal_re, ofReal_im, mul_zero, sub_zero,
      zero_div, Complex.normSq_ofReal]
    exact div_ne_zero (mul_ne_zero hz hr.ne') (mul_ne_zero hr.ne' hr.ne')
  have hzw : (r : ℂ) * w = z := by
    dsimp [w]
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ z (Complex.ofReal_ne_zero.mpr hr.ne')
  have hwnorm : ‖w‖ = 1 := by
    simp only [w]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, hnorm,
      div_self hr.ne']
  have hwunit : w * conj w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hwnorm, one_pow]
    norm_num
  obtain ⟨m, hmpos, hmgt⟩ :=
    Complex.exists_pos_pow_re_gt_of_norm_eq_one hwnorm hwim
  have hmneone : m ≠ 1 := by
    intro h
    subst m
    simp at hmgt
  have hm2 : 2 ≤ m := by lia
  let k := m - 2
  have hkm : k + 2 = m := Nat.sub_add_cancel hm2
  have hdiff :
      0 ≤ u 1 * aswShiftedToeplitzMinor u 1 (k + 1) -
        aswShiftedToeplitzMinor u 1 (k + 2) := by
    rw [← aswGapToeplitzMinor_identity u k]
    exact mul_nonneg hconst.le (hgap (k + 1))
  have hclosed :=
    aswShiftedToeplitzMinor_one_eq_closedForm u hu r hz hsum hpairs hprod
  have hdiffC :
      ((u 1 * aswShiftedToeplitzMinor u 1 (k + 1) -
          aswShiftedToeplitzMinor u 1 (k + 2) : ℝ) : ℂ) =
        ((r ^ (k + 2) *
          ((w.re - (w ^ (k + 2)).re) / (1 - w.re) : ℝ) : ℝ) : ℂ) := by
    push_cast
    rw [← hsum, congrFun hclosed (k + 1), congrFun hclosed (k + 2)]
    rw [← hzw]
    simp only [map_mul, conj_ofReal]
    rw [aswCubicClosedForm_scale r hr.ne' hwim (k + 1),
      aswCubicClosedForm_scale r hr.ne' hwim (k + 2)]
    rw [show
      ((r : ℂ) + (r : ℂ) * w + (r : ℂ) * conj w) *
            ((r : ℂ) ^ (k + 1) * aswCubicClosedForm 1 w (k + 1)) -
          (r : ℂ) ^ (k + 2) * aswCubicClosedForm 1 w (k + 2) =
        (r : ℂ) ^ (k + 2) *
          (((1 : ℂ) + w + conj w) * aswCubicClosedForm 1 w (k + 1) -
            aswCubicClosedForm 1 w (k + 2)) by
      simp only [pow_succ]
      ring]
    rw [show k + 2 = (k + 1) + 1 by lia,
      aswCubicClosedForm_unit_gap_re hwim hwunit (k + 1)]
    push_cast
    simp only [pow_succ]
  have hdiffR :
      u 1 * aswShiftedToeplitzMinor u 1 (k + 1) -
          aswShiftedToeplitzMinor u 1 (k + 2) =
        r ^ (k + 2) * ((w.re - (w ^ (k + 2)).re) / (1 - w.re)) := by
    exact_mod_cast hdiffC
  rw [hdiffR] at hdiff
  have hrelt : w.re < 1 := by
    calc
      w.re ≤ |w.re| := le_abs_self _
      _ < ‖w‖ := Complex.abs_re_lt_norm.mpr hwim
      _ = 1 := hwnorm
  have hquot : 0 ≤ (w.re - (w ^ (k + 2)).re) / (1 - w.re) :=
    nonneg_of_mul_nonneg_right hdiff (pow_pos hr (k + 2))
  have hle : (w ^ (k + 2)).re ≤ w.re := by
    rcases div_nonneg_iff.mp hquot with h | h
    · exact sub_nonneg.mp h.1
    · linarith
  rw [hkm] at hle
  exact (not_lt_of_ge hle) hmgt

/-- The three nonnegative cubic minor families rule out a positive real
characteristic root together with a nonreal conjugate pair. -/
theorem false_of_nonreal_aswCubicCharacteristicRoots
    (u : ℕ → ℝ) (hu : ∀ j, 4 ≤ j → u j = 0)
    (r : ℝ) {z : ℂ} (hr : 0 < r) (hz : z.im ≠ 0)
    (hsum : (r : ℂ) + z + conj z = u 1)
    (hpairs : (r : ℂ) * z + (r : ℂ) * conj z + z * conj z = u 0 * u 2)
    (hprod : (r : ℂ) * z * conj z = u 0 ^ 2 * u 3)
    (hconst : 0 < u 0)
    (hone : ∀ n, 0 ≤ aswShiftedToeplitzMinor u 1 n)
    (htwo : ∀ n, 0 ≤ aswShiftedToeplitzMinor u 2 n)
    (hgap : ∀ n, 0 ≤ aswGapToeplitzMinor u n) :
    False := by
  have hle := norm_le_of_aswShiftedToeplitzMinor_one_nonneg
    u hu r hr.le hz hsum hpairs hprod hone
  have hge := le_norm_of_aswShiftedToeplitzMinor_two_nonneg
    u hu (u 0) r hconst hr hz hsum hpairs hprod rfl htwo
  exact false_of_aswCubicCharacteristicRoots_equalNorm
    u hu r hr hz hsum hpairs hprod (hle.antisymm hge) hconst hgap

end RealRooted
