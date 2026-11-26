/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Structural.ShortTailSoundness
import RealRooted.IntervalDifferential.ConvolutionTail
import RealRooted.IntervalDifferential.EulerNorm
import Mathlib.Tactic

/-!
# Coefficient dominance from a finite short-kernel certificate

A checked anchor controls every subsequent alphabet row by the Euler tail bound.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

noncomputable section

open Polynomial Finset

namespace RealRooted.LongCycleDescents.Structural

open IntervalDifferential

/-- A finite tail check proves strict coefficient dominance at every subsequent rank. -/
theorem coefficientNorm_lt_of_shortTailCertificate {k H n : ℕ} (hk : k ≤ 66)
    (hH : H ≤ 64) (hn : H ≤ n) (hc : shortTailCertificate k H = true) :
    coefficientNorm (4 / 5 : ℚ) (lossRow k n - C ((lossRow k n).coeff 0)) <
      (lossRow k n).coeff 0 := by
  have hchecked := shortTailCertificate_sound hk hc
  let e i := coefficientNorm (4 / 5 : ℚ) (differenceRow k i)
  have he i : 0 ≤ e i := coefficientNorm_nonneg (by norm_num) _
  have hrec (i : ℕ) (hi : i ≠ 0) : (i : ℚ) * e i ≤
      ∑ j ∈ range i, shortKernelNorm k (i - j) * e j := by
    have hh := coefficientNorm_eulerCoeff_equation (by norm_num : (0 : ℚ) ≤ 4 / 5)
      (-shortKernel k) hi
    simpa only [e, differenceRow, Pi.neg_apply, coefficientNorm_neg, shortKernelNorm_eq] using hh
  have htail := sum_euler_tail_bound (shortKernelNorm k) e (shortTailBound k) he hrec
    (by lia : 0 < H + 1) (by lia : H + 1 ≤ n + 1) (by
      intro l _ hl B
      exact sum_shortKernelNorm_le (by lia : l ≤ 65) k B)
  have hpos : (0 : ℚ) < ((H + 1 : ℕ) : ℚ) - shortTailBound k 1 :=
    sub_pos.mpr hchecked.1
  have hb : (∑ i ∈ Ico (H + 1) (n + 1), e i) < (lossRow k H).coeff 0 -
      coefficientNorm (4 / 5 : ℚ) (lossRow k H - C ((lossRow k H).coeff 0)) := by
    apply (mul_lt_mul_iff_right₀ hpos).mp
    convert htail.trans_lt hchecked.2 using 1
  let R := ∑ i ∈ Ico (H + 1) (n + 1), differenceRow k i
  have hR : coefficientNorm (4 / 5 : ℚ) R < (lossRow k H).coeff 0 -
      coefficientNorm (4 / 5 : ℚ) (lossRow k H - C ((lossRow k H).coeff 0)) :=
    (coefficientNorm_sum_le (by norm_num) _ _).trans_lt hb
  have hrow : lossRow k n = lossRow k H + R := by
    rw [lossRow_eq_sum_differenceRow k n, lossRow_eq_sum_differenceRow k H,
      ← sum_range_add_sum_Ico (differenceRow k) (by lia : H + 1 ≤ n + 1)]
  rw [hrow]
  exact coefficientNorm_add_sub_constant_lt (by norm_num) _ _ hR

end RealRooted.LongCycleDescents.Structural
