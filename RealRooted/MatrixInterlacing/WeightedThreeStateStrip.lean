module

public import RealRooted.MatrixInterlacing.WeightedThreeState
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The weighted three-state half-height strip

This file formalizes the algebraic and inverse-function stages of the
characteristic-root proof in RealRooted issue #2089.  The normalized rows are
those with recurrence parameters `(rho, 0, 1, e)`.  We prove the exact row
recurrence, the bijective positive characteristic parametrization, the three
characteristic roots, and the two amplitude inequalities used later in the
phase-count and strict-interlacing arguments.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The normalized row polynomial `Q_n` from RealRooted issue #2089. -/
def weightedStripRow (rho e : ℝ) (n : ℕ) : ℝ[X] :=
  (weightedThreeState rho 0 1 e n).P

/-- The first three normalized rows are `1`, `1`, and `1 + (1-e)X`. -/
theorem weightedStripRow_initial (rho e : ℝ) :
    weightedStripRow rho e 0 = 1 ∧
      weightedStripRow rho e 1 = 1 ∧
      weightedStripRow rho e 2 = 1 + C (1 - e) * X := by
  simpa [weightedStripRow] using weightedThreeState_P_initial rho 0 1 e

/-- The normalized rows obey the third-order recurrence in issue #2089. -/
theorem weightedStripRow_add_three (rho e : ℝ) (n : ℕ) :
    weightedStripRow rho e (n + 3) =
      3 * weightedStripRow rho e (n + 2) +
        (X - 3) * weightedStripRow rho e (n + 1) +
        (1 + C (rho - 1) * X) * weightedStripRow rho e n := by
  simpa [weightedStripRow] using weightedThreeState_P_add_three rho 0 1 e n

/-- The positive characteristic scale `s = r^3 / (rho-r)` from issue #2089. -/
def characteristicScale (rho r : ℝ) : ℝ := r ^ 3 / (rho - r)

/-- The characteristic scale is positive on `0 < r < rho`. -/
theorem characteristicScale_pos {rho r : ℝ} (hr : 0 < r) (hrrho : r < rho) :
    0 < characteristicScale rho r := by
  exact div_pos (pow_pos hr 3) (sub_pos.mpr hrrho)

/-- The characteristic scale is strictly increasing on `(0,rho)`. -/
theorem characteristicScale_strictMonoOn {rho : ℝ} :
    StrictMonoOn (characteristicScale rho) (Set.Ioo 0 rho) := by
  intro x hx y hy hxy
  rw [characteristicScale, characteristicScale,
    div_lt_div_iff₀ (sub_pos.mpr hx.2) (sub_pos.mpr hy.2)]
  rw [← sub_pos]
  have hfactor :
      y ^ 3 * (rho - x) - x ^ 3 * (rho - y) =
        (y - x) * (rho * (y ^ 2 + x * y + x ^ 2) - x * y * (x + y)) := by
    ring
  rw [hfactor]
  have hxypos : 0 < x * y := mul_pos hx.1 hy.1
  have hsum : 0 < y ^ 2 + x * y + x ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hupper :
      y * (y ^ 2 + x * y + x ^ 2) <
        rho * (y ^ 2 + x * y + x ^ 2) :=
    mul_lt_mul_of_pos_right hy.2 hsum
  have hlower : x * y * (x + y) < y * (y ^ 2 + x * y + x ^ 2) := by
    nlinarith [pow_pos hy.1 3]
  exact mul_pos (sub_pos.mpr hxy) (sub_pos.mpr (hlower.trans hupper))

/-- Every `s > 0` has a unique characteristic parameter `r` in `(0,rho)`.

This is the inverse/criterion step in the characteristic-root proof of
RealRooted issue #2089.
-/
theorem existsUnique_characteristicScale_eq {rho s : ℝ}
    (hrho : 0 < rho) (hs : 0 < s) :
    ∃! r, 0 < r ∧ r < rho ∧ characteristicScale rho r = s := by
  let f : ℝ → ℝ := fun r ↦ r ^ 3 + s * r - s * rho
  have hf : Continuous f := by
    fun_prop
  have hzero : 0 ∈ Set.Icc (f 0) (f rho) := by
    dsimp [f]
    constructor <;> nlinarith [mul_pos hs hrho, pow_pos hrho 3]
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc hrho.le hf.continuousOn hzero
  have hrpos : 0 < r := by
    rcases hr.1.eq_or_lt with rfl | hrpos
    · dsimp [f] at hfr
      nlinarith [mul_pos hs hrho]
    · exact hrpos
  have hrrho : r < rho := by
    rcases hr.2.eq_or_lt with h | h
    · subst r
      dsimp [f] at hfr
      nlinarith [pow_pos hrho 3]
    · exact h
  have hscale : characteristicScale rho r = s := by
    rw [characteristicScale, div_eq_iff (sub_ne_zero.mpr hrrho.ne')]
    dsimp [f] at hfr
    nlinarith
  refine ⟨r, ⟨hrpos, hrrho, hscale⟩, ?_⟩
  intro y hy
  exact (characteristicScale_strictMonoOn.injOn
    ⟨hrpos, hrrho⟩ ⟨hy.1, hy.2.1⟩ (hscale.trans hy.2.2.symm)).symm

/-- The characteristic cubic for a negative argument `x = -s`. -/
def weightedThreeStateCharacteristic (rho s : ℝ) (lambda : ℂ) : ℂ :=
  (lambda - 1) ^ 3 + s * (lambda - 1) + s * rho

/-- The real characteristic root is `1-r` when `s = r^3/(rho-r)`. -/
theorem weightedThreeStateCharacteristic_realRoot {rho r : ℝ}
    (hrrho : r < rho) :
    weightedThreeStateCharacteristic rho (characteristicScale rho r) (1 - r) = 0 := by
  have hreal :
      (-r) ^ 3 - characteristicScale rho r * r +
        characteristicScale rho r * rho = 0 := by
    rw [characteristicScale]
    field_simp [sub_ne_zero.mpr hrrho.ne']
    ring
  norm_num [weightedThreeStateCharacteristic]
  exact_mod_cast hreal

/-- The conjugate pair `1+r/2 ± iv` solves the characteristic cubic. -/
theorem weightedThreeStateCharacteristic_complexRoot {rho r s v : ℝ}
    (hcubic : r ^ 3 = s * (rho - r))
    (hv : v ^ 2 = s + 3 * r ^ 2 / 4) :
    weightedThreeStateCharacteristic rho s (1 + r / 2 + v * Complex.I) = 0 := by
  have hrv := congrArg (fun x : ℝ ↦ r * x) hv
  have hvv := congrArg (fun x : ℝ ↦ v * x) hv
  apply Complex.ext <;>
    norm_num [weightedThreeStateCharacteristic, pow_succ] <;>
    ring_nf at * <;>
    nlinarith [hrv, hvv]

/-- The squared modulus of a nonreal characteristic root has the paper's
closed form `1+r+r^2+s`. -/
theorem normSq_weightedThreeStateCharacteristicRoot {r s v : ℝ}
    (hv : v ^ 2 = s + 3 * r ^ 2 / 4) :
    Complex.normSq (1 + r / 2 + v * Complex.I) = 1 + r + r ^ 2 + s := by
  simp [Complex.normSq_apply]
  nlinarith

/-- The upper characteristic root has phase strictly between `0` and `pi/2`. -/
theorem weightedThreeStateCharacteristicRoot_arg_mem {r v : ℝ}
    (hr : 0 < r) (hv : 0 < v) :
    0 < Complex.arg (1 + r / 2 + v * Complex.I) ∧
      Complex.arg (1 + r / 2 + v * Complex.I) < Real.pi / 2 := by
  let z : ℂ := 1 + r / 2 + v * Complex.I
  have hzre : 0 < z.re := by
    dsimp [z]
    norm_num
    linarith
  have hzim : 0 < z.im := by
    simpa [z] using hv
  have hnonneg : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr hzim.le
  have hne : Complex.arg z ≠ 0 := by
    intro h
    exact hzim.ne' (Complex.arg_eq_zero_iff.mp h).2
  exact ⟨lt_of_le_of_ne hnonneg (Ne.symm hne),
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hzre)⟩

/-- The residue of the normalized row generating function at a characteristic
root, as used in RealRooted issue #2089. -/
def weightedThreeStateResidue (e s : ℝ) (lambda : ℂ) : ℂ :=
  ((lambda - 1) ^ 2 + e * s) / (3 * (lambda - 1) ^ 2 + s)

/-- The real-root residue has the claimed elementary closed form. -/
theorem weightedThreeStateResidue_realRoot {e r s : ℝ} :
    weightedThreeStateResidue e s (1 - r) =
      (r ^ 2 + e * s) / (3 * r ^ 2 + s) := by
  apply Complex.ext <;>
    norm_num [weightedThreeStateResidue, Complex.div_re, Complex.div_im,
      Complex.normSq_apply]

/-- The normalized real characteristic root has modulus less than one. -/
theorem abs_characteristicRatio_lt_one {r s R : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hR : 0 < R)
    (hRsq : R ^ 2 = 1 + r + r ^ 2 + s) :
    |(1 - r) / R| < 1 := by
  rw [abs_div, abs_of_pos hR, div_lt_one hR]
  apply abs_lt_of_sq_lt_sq
  · nlinarith
  · exact hR.le

/-- The real amplitude `A = (1+ek)/(3+k)` from issue #2089. -/
def weightedThreeStateAmplitudeA (e k : ℝ) : ℝ := (1 + e * k) / (3 + k)

/-- The `k`-amplitude equals the real-root residue when `k=s/r^2`. -/
theorem weightedThreeStateAmplitudeA_eq_residue {e r s : ℝ} (hr : r ≠ 0) :
    weightedThreeStateAmplitudeA e (s / r ^ 2) =
      (r ^ 2 + e * s) / (3 * r ^ 2 + s) := by
  simp only [weightedThreeStateAmplitudeA]
  field_simp [hr]

/-- The complex amplitude with the real and imaginary parts in issue #2089. -/
def weightedThreeStateAmplitudeB (r v A : ℝ) : ℂ :=
  ⟨(1 - A) / 2, r * (1 - 3 * A) / (4 * v)⟩

/-- If `A < 1`, the amplitude phase lies strictly between `-pi/2` and `pi/2`. -/
theorem weightedThreeStateAmplitudeB_arg_mem {r v A : ℝ} (hA : A < 1) :
    -(Real.pi / 2) < Complex.arg (weightedThreeStateAmplitudeB r v A) ∧
      Complex.arg (weightedThreeStateAmplitudeB r v A) < Real.pi / 2 := by
  rw [← abs_lt]
  apply Complex.abs_arg_lt_pi_div_two_iff.mpr
  left
  simp [weightedThreeStateAmplitudeB]
  linarith

/-- The residue at the upper characteristic root is exactly the complex
amplitude `B` of RealRooted issue #2089. -/
theorem weightedThreeStateResidue_complexRoot {e r s v : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hv : 0 < v)
    (hvsq : v ^ 2 = s + 3 * r ^ 2 / 4) :
    weightedThreeStateResidue e s (1 + r / 2 + v * Complex.I) =
      weightedThreeStateAmplitudeB r v
        ((r ^ 2 + e * s) / (3 * r ^ 2 + s)) := by
  let lambda : ℂ := 1 + r / 2 + v * Complex.I
  let D : ℂ := 3 * (lambda - 1) ^ 2 + s
  have hD : D ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    dsimp [D, lambda] at him
    norm_num [pow_succ] at him
    nlinarith [mul_pos hr hv]
  have hnorm : Complex.normSq D ≠ 0 := by
    intro h
    exact hD (Complex.normSq_eq_zero.mp h)
  have hv0 : v ≠ 0 := hv.ne'
  have hAden : 3 * r ^ 2 + s ≠ 0 := by positivity
  change weightedThreeStateResidue e s lambda = _
  apply Complex.ext <;>
    norm_num [weightedThreeStateResidue, weightedThreeStateAmplitudeB,
      Complex.div_re, Complex.div_im, Complex.normSq_apply, D, lambda, pow_succ] <;>
    field_simp [hv0, hAden, hnorm] <;>
    ring_nf at hvsq ⊢ <;>
    nlinarith [congrArg (fun x : ℝ ↦ r ^ 2 * x) hvsq,
      congrArg (fun x : ℝ ↦ s * x) hvsq,
      congrArg (fun x : ℝ ↦ e * s * x) hvsq]

/-- The residue at the lower characteristic root is the conjugate amplitude. -/
theorem weightedThreeStateResidue_conjRoot {e r s v : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hv : 0 < v)
    (hvsq : v ^ 2 = s + 3 * r ^ 2 / 4) :
    weightedThreeStateResidue e s (1 + r / 2 - v * Complex.I) =
      star (weightedThreeStateAmplitudeB r v
        ((r ^ 2 + e * s) / (3 * r ^ 2 + s))) := by
  have h := congrArg star
    (weightedThreeStateResidue_complexRoot (e := e) hr hs hv hvsq)
  convert h using 1
  simp [weightedThreeStateResidue, pow_two]
  ring

/-- The exact three-mode characteristic expression for the normalized row. -/
def weightedThreeStateExpansion (e r s v : ℝ) (n : ℕ) : ℂ :=
  let A : ℝ := (r ^ 2 + e * s) / (3 * r ^ 2 + s)
  let B : ℂ := weightedThreeStateAmplitudeB r v A
  (A : ℂ) * (1 - r) ^ n + B * (1 + r / 2 + v * Complex.I) ^ n +
    star B * (1 + r / 2 - v * Complex.I) ^ n

/-- The characteristic expression has the required first three values. -/
theorem weightedThreeStateExpansion_initial {e r s v : ℝ}
    (hs : 0 < s) (hv : 0 < v)
    (hvsq : v ^ 2 = s + 3 * r ^ 2 / 4) :
    weightedThreeStateExpansion e r s v 0 = 1 ∧
      weightedThreeStateExpansion e r s v 1 = 1 ∧
      weightedThreeStateExpansion e r s v 2 = 1 - (1 - e) * s := by
  let A : ℝ := (r ^ 2 + e * s) / (3 * r ^ 2 + s)
  let B : ℂ := weightedThreeStateAmplitudeB r v A
  have hv0 : v ≠ 0 := hv.ne'
  have hden : 3 * r ^ 2 + s ≠ 0 := by positivity
  have hA : A * (3 * r ^ 2 + s) = r ^ 2 + e * s := by
    dsimp [A]
    exact div_mul_cancel₀ _ hden
  constructor
  · change (A : ℂ) * (1 - r) ^ 0 +
        B * (1 + r / 2 + v * Complex.I) ^ 0 +
        star B * (1 + r / 2 - v * Complex.I) ^ 0 = 1
    apply Complex.ext
    · norm_num [B, weightedThreeStateAmplitudeB]
      ring
    · norm_num [B, weightedThreeStateAmplitudeB]
  constructor
  · change (A : ℂ) * (1 - r) ^ 1 +
        B * (1 + r / 2 + v * Complex.I) ^ 1 +
        star B * (1 + r / 2 - v * Complex.I) ^ 1 = 1
    apply Complex.ext <;>
      norm_num [B, weightedThreeStateAmplitudeB, pow_succ] <;>
      field_simp [hv0] <;>
      ring_nf at hA ⊢
  · change (A : ℂ) * (1 - r) ^ 2 +
        B * (1 + r / 2 + v * Complex.I) ^ 2 +
        star B * (1 + r / 2 - v * Complex.I) ^ 2 = 1 - (1 - e) * s
    apply Complex.ext <;>
      norm_num [B, weightedThreeStateAmplitudeB, pow_succ] <;>
      field_simp [hv0] <;>
      ring_nf at hA hvsq ⊢;
      nlinarith [congrArg (fun x : ℝ ↦ A * x) hvsq]

/-- Powers of any characteristic root satisfy the evaluated row recurrence. -/
theorem weightedThreeStateCharacteristic_pow_add_three {rho s : ℝ} {lambda : ℂ}
    (hroot : weightedThreeStateCharacteristic rho s lambda = 0) (n : ℕ) :
    lambda ^ (n + 3) = 3 * lambda ^ (n + 2) +
      (-s - 3) * lambda ^ (n + 1) + (1 - (rho - 1) * s) * lambda ^ n := by
  have hcubic :
      lambda ^ 3 = 3 * lambda ^ 2 + (-s - 3) * lambda +
        (1 - (rho - 1) * s) := by
    rw [weightedThreeStateCharacteristic] at hroot
    linear_combination hroot
  calc
    lambda ^ (n + 3) = lambda ^ n * lambda ^ 3 := by ring
    _ = lambda ^ n * (3 * lambda ^ 2 + (-s - 3) * lambda +
        (1 - (rho - 1) * s)) := by rw [hcubic]
    _ = _ := by ring

/-- The three-mode expression satisfies the normalized row recurrence. -/
theorem weightedThreeStateExpansion_add_three {rho e r s v : ℝ}
    (hcubic : r ^ 3 = s * (rho - r))
    (hvsq : v ^ 2 = s + 3 * r ^ 2 / 4) (n : ℕ) :
    weightedThreeStateExpansion e r s v (n + 3) =
      3 * weightedThreeStateExpansion e r s v (n + 2) +
        (-s - 3) * weightedThreeStateExpansion e r s v (n + 1) +
        (1 - (rho - 1) * s) * weightedThreeStateExpansion e r s v n := by
  have hreal : weightedThreeStateCharacteristic rho s (1 - r) = 0 := by
    apply Complex.ext
    · norm_num [weightedThreeStateCharacteristic, pow_succ]
      ring_nf at hcubic ⊢
      nlinarith
    · norm_num [weightedThreeStateCharacteristic, pow_succ]
  have hplus :
      weightedThreeStateCharacteristic rho s (1 + r / 2 + v * Complex.I) = 0 :=
    weightedThreeStateCharacteristic_complexRoot hcubic hvsq
  have hminus :
      weightedThreeStateCharacteristic rho s (1 + r / 2 - v * Complex.I) = 0 := by
    have h := weightedThreeStateCharacteristic_complexRoot hcubic
      (v := -v) (by nlinarith [hvsq])
    rw [show (1 + r / 2 - v * Complex.I : ℂ) =
      1 + r / 2 + (-v) * Complex.I by ring]
    push_cast at h
    exact h
  have hrealPow := weightedThreeStateCharacteristic_pow_add_three hreal n
  have hplusPow := weightedThreeStateCharacteristic_pow_add_three hplus n
  have hminusPow := weightedThreeStateCharacteristic_pow_add_three hminus n
  simp only [weightedThreeStateExpansion]
  rw [hrealPow, hplusPow, hminusPow]
  ring

private theorem nat_threeStepInduction {motive : ℕ → Prop}
    (zero : motive 0) (one : motive 1) (two : motive 2)
    (more : ∀ n, motive n → motive (n + 1) → motive (n + 2) → motive (n + 3)) :
    ∀ n, motive n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · exact zero
      rcases n with _ | n
      · exact one
      rcases n with _ | n
      · exact two
      exact more n (ih n (by lia)) (ih (n + 1) (by lia)) (ih (n + 2) (by lia))

/-- Exact characteristic-root expansion of every normalized row at `-s`.

This completes the recurrence-and-residue stage of the proof in RealRooted
issue #2089; the remaining global theorem needs the continuous phase count.
-/
theorem weightedStripRow_eval_eq_expansion {rho e r s v : ℝ}
    (hs : 0 < s) (hv : 0 < v)
    (hcubic : r ^ 3 = s * (rho - r))
    (hvsq : v ^ 2 = s + 3 * r ^ 2 / 4) (n : ℕ) :
    (((weightedStripRow rho e n).eval (-s : ℝ) : ℝ) : ℂ) =
      weightedThreeStateExpansion e r s v n := by
  have hrows := weightedStripRow_initial rho e
  have hexp := weightedThreeStateExpansion_initial (e := e) hs hv hvsq
  induction n using nat_threeStepInduction with
  | zero =>
      rw [hrows.1]
      norm_num
      exact hexp.1.symm
  | one =>
      rw [hrows.2.1]
      norm_num
      exact hexp.2.1.symm
  | two =>
      rw [hrows.2.2]
      norm_num [eval_add, eval_mul]
      exact hexp.2.2.symm
  | more n hn hn1 hn2 =>
      have heval := congrArg
        (fun p : ℝ[X] ↦ ((p.eval (-s : ℝ) : ℝ) : ℂ))
        (weightedStripRow_add_three rho e n)
      norm_num [eval_add, eval_mul] at heval
      rw [hn, hn1, hn2] at heval
      exact heval.trans (weightedThreeStateExpansion_add_three hcubic hvsq n).symm

/-- On the half-height strip, the real amplitude satisfies `0 < A < 1/2`. -/
theorem weightedThreeStateAmplitudeA_mem {e k : ℝ}
    (he : 0 ≤ e) (hehalf : e ≤ 1 / 2) (hk : 0 < k) :
    0 < weightedThreeStateAmplitudeA e k ∧
      weightedThreeStateAmplitudeA e k < 1 / 2 := by
  have hden : 0 < 3 + k := by positivity
  constructor
  · exact div_pos (by positivity) hden
  · rw [weightedThreeStateAmplitudeA, div_lt_iff₀ hden]
    nlinarith [mul_nonneg he hk.le, mul_le_mul_of_nonneg_right hehalf hk.le]

/-- The `k`-form of `A` agrees with the characteristic-parameter form in
RealRooted issue #2089. -/
theorem weightedThreeStateAmplitudeA_eq_characteristic {rho e r : ℝ}
    (hr : 0 < r) (hrrho : r < rho) :
    weightedThreeStateAmplitudeA e (characteristicScale rho r / r ^ 2) =
      (rho - (1 - e) * r) / (3 * rho - 2 * r) := by
  have hr0 : r ≠ 0 := hr.ne'
  have hsub : rho - r ≠ 0 := sub_ne_zero.mpr hrrho.ne'
  have hden : 3 * rho - 2 * r ≠ 0 := by nlinarith
  have hden' : rho * 3 - r * 2 ≠ 0 := by nlinarith
  simp only [weightedThreeStateAmplitudeA, characteristicScale]
  field_simp [hr0, hsub, hden, hden']
  ring

/-- Twice the norm of `B` dominates `1-A`, using only its real part. -/
theorem one_sub_le_two_norm_weightedThreeStateAmplitudeB {r v A : ℝ}
    (hA : A ≤ 1) :
    1 - A ≤ 2 * ‖weightedThreeStateAmplitudeB r v A‖ := by
  have hre : (weightedThreeStateAmplitudeB r v A).re = (1 - A) / 2 := by
    simp [weightedThreeStateAmplitudeB]
  have habs := Complex.abs_re_le_norm (weightedThreeStateAmplitudeB r v A)
  rw [hre, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at habs
  rw [abs_of_nonneg (sub_nonneg.mpr hA)] at habs
  linarith

/-- The unspecialized squared-amplitude identity underlying equation (5) in
RealRooted issue #2089. -/
theorem weightedThreeStateAmplitude_gap_eq {r v A k : ℝ}
    (hr : 0 < r) (hv : 0 < v) (hk : 0 < k)
    (hvk : v ^ 2 = r ^ 2 * (k + 3 / 4)) :
    4 * Complex.normSq (weightedThreeStateAmplitudeB r v A) -
        A ^ 2 * (1 + 9 * r ^ 2 / (4 * v ^ 2)) =
      1 - 2 * A + (1 - 6 * A) / (4 * k + 3) := by
  have hr0 : r ≠ 0 := hr.ne'
  have hv0 : v ≠ 0 := hv.ne'
  have hkden : 4 * k + 3 ≠ 0 := by positivity
  simp [weightedThreeStateAmplitudeB, Complex.normSq_apply]
  field_simp [hr0, hv0, hkden]
  ring_nf at hvk ⊢
  nlinarith [congrArg (fun x : ℝ ↦ 16 * A ^ 2 * x) hvk,
    congrArg (fun x : ℝ ↦ 4 * x) hvk]

/-- Substituting `A = (1+ek)/(3+k)` gives the positive rational expression in
equation (5) of RealRooted issue #2089. -/
theorem weightedThreeStateAmplitude_gap_closedForm {e k : ℝ} (hk : 0 < k) :
    1 - 2 * weightedThreeStateAmplitudeA e k +
        (1 - 6 * weightedThreeStateAmplitudeA e k) / (4 * k + 3) =
      4 * k * ((2 - 3 * e) + k * (1 - 2 * e)) /
        ((3 + k) * (4 * k + 3)) := by
  have hk3 : 3 + k ≠ 0 := by positivity
  have hk4 : 4 * k + 3 ≠ 0 := by positivity
  rw [weightedThreeStateAmplitudeA]
  field_simp [hk3, hk4]
  ring

/-- The strengthened amplitude gap is strictly positive throughout the
half-height strip.  This is equation (5) of RealRooted issue #2089. -/
theorem weightedThreeStateAmplitude_gap_pos {r v e k : ℝ}
    (hr : 0 < r) (hv : 0 < v) (hk : 0 < k)
    (hehalf : e ≤ 1 / 2)
    (hvk : v ^ 2 = r ^ 2 * (k + 3 / 4)) :
    0 < 4 * Complex.normSq
        (weightedThreeStateAmplitudeB r v (weightedThreeStateAmplitudeA e k)) -
      weightedThreeStateAmplitudeA e k ^ 2 *
        (1 + 9 * r ^ 2 / (4 * v ^ 2)) := by
  rw [weightedThreeStateAmplitude_gap_eq hr hv hk hvk,
    weightedThreeStateAmplitude_gap_closedForm hk]
  have hfirst : 0 < 2 - 3 * e := by nlinarith
  have hsecond : 0 ≤ 1 - 2 * e := by nlinarith
  have hsum : 0 < (2 - 3 * e) + k * (1 - 2 * e) := by positivity
  exact div_pos (mul_pos (mul_pos (by norm_num) hk) hsum) (by positivity)

/-- The real mode is strictly dominated by the complex pair for every
positive row index. -/
theorem abs_realMode_lt_two_norm_amplitude {A kappa : ℝ} {B : ℂ} {n : ℕ}
    (hA : 0 < A) (hAhalf : A ≤ 1 / 2) (hkappa : |kappa| < 1)
    (hn : n ≠ 0) (hB : 1 - A ≤ 2 * ‖B‖) :
    |A * kappa ^ n| < 2 * ‖B‖ := by
  rw [abs_mul, abs_of_pos hA, abs_pow]
  have hpow : |kappa| ^ n < 1 := pow_lt_one₀ (abs_nonneg kappa) hkappa hn
  calc
    A * |kappa| ^ n < A := by nlinarith [mul_lt_mul_of_pos_left hpow hA]
    _ ≤ 1 - A := by linarith
    _ ≤ 2 * ‖B‖ := hB

/-- The concrete rows highlighted in issue #2089, outside the earlier matrix
region, are `2Q_4 = 2+8X+X^2` and `8Q_5 = 8+60X+23X^2`. -/
theorem weightedStripRow_one_fourth_half_example :
    2 * weightedStripRow (1 / 4) (1 / 2) 4 = 2 + 8 * X + X ^ 2 ∧
      8 * weightedStripRow (1 / 4) (1 / 2) 5 = 8 + 60 * X + 23 * X ^ 2 := by
  norm_num [weightedStripRow, weightedThreeState, weightedThreeStateStep]
  constructor
  · have hx :
        (12 : ℝ[X]) * C (1 / 2 : ℝ) + 8 * C (1 / 4 : ℝ) = 8 := by
      change C (12 : ℝ) * C (1 / 2 : ℝ) + C 8 * C (1 / 4 : ℝ) = C 8
      rw [← C_mul, ← C_mul, ← C_add]
      norm_num
    have hx2 : (2 : ℝ[X]) * C (1 / 2 : ℝ) = 1 := by
      change C (2 : ℝ) * C (1 / 2 : ℝ) = C 1
      rw [← C_mul]
      norm_num
    calc
      _ = 2 + X * (12 * C (1 / 2 : ℝ) + 8 * C (1 / 4 : ℝ)) +
          X ^ 2 * (2 * C (1 / 2 : ℝ)) := by ring
      _ = _ := by
        rw [hx, hx2]
        ring
  · have hx :
        (80 : ℝ[X]) * C (1 / 2 : ℝ) + 80 * C (1 / 4 : ℝ) = 60 := by
      change C (80 : ℝ) * C (1 / 2 : ℝ) + C 80 * C (1 / 4 : ℝ) = C 60
      rw [← C_mul, ← C_mul, ← C_add]
      norm_num
    have hx2 :
        (40 : ℝ[X]) * C (1 / 2 : ℝ) +
            8 * C (1 / 2 : ℝ) * C (1 / 4 : ℝ) +
          8 * C (1 / 4 : ℝ) = 23 := by
      change C (40 : ℝ) * C (1 / 2 : ℝ) +
          C 8 * C (1 / 2 : ℝ) * C (1 / 4 : ℝ) +
        C 8 * C (1 / 4 : ℝ) = C 23
      rw [← C_mul, ← C_mul, ← C_mul, ← C_mul, ← C_add, ← C_add]
      norm_num
    calc
      _ = 8 + X * (80 * C (1 / 2 : ℝ) + 80 * C (1 / 4 : ℝ)) +
          X ^ 2 * (40 * C (1 / 2 : ℝ) +
            8 * C (1 / 2 : ℝ) * C (1 / 4 : ℝ) + 8 * C (1 / 4 : ℝ)) := by
        ring
      _ = _ := by
        rw [hx, hx2]
        ring

end RealRooted
