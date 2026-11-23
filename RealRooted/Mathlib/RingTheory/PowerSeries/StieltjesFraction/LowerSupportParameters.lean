/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Contraction
public import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialTransform
import RealRooted.Mathlib.RingTheory.PowerSeries.JacobiFraction.Translation
public import Mathlib.Basic.Real.Basic

/-!
# Stieltjes parameters for a lower support bound

The sequences `u k` and `v k` are the even and odd parameters `g_(2k)` and
`g_(2k+1)` in Sokal-Walrad, arXiv:2404.12131v1, Theorem 2. Pairing their
numerators contracts to a translated Jacobi fraction. The numerator sequence
is existential; its inactive tail is not required to be standardized.
-/

public section

namespace PowerSeries

/-- Numerators parametrizing a Stieltjes moment measure with lower support bound `c`. -/
@[expose] noncomputable def shiftedStieltjesNumerators
    (c : ℝ) (u v : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n % 2 = 0 then c * (1 + u (n / 2)) + v (n / 2)
  else v (n / 2) * u (n / 2 + 1) / (1 + u (n / 2))

/-- The nonnegative numerator data before translating the support by `c`. -/
@[expose] noncomputable def stieltjesNumeratorsBeforeShift
    (c : ℝ) (u v : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n % 2 = 0 then v (n / 2)
  else u (n / 2 + 1) * (c * (1 + u (n / 2)) + v (n / 2)) / (1 + u (n / 2))

/-- The even-indexed numerator is the odd-indexed numerator in classical indexing. -/
@[simp] theorem shiftedStieltjesNumerators_even (c : ℝ) (u v : ℕ → ℝ) (k : ℕ) :
    shiftedStieltjesNumerators c u v (2 * k) = c * (1 + u k) + v k := by
  simp [shiftedStieltjesNumerators, Nat.mul_comm]

/-- The odd-indexed numerator joins two successive even parameters. -/
@[simp] theorem shiftedStieltjesNumerators_odd (c : ℝ) (u v : ℕ → ℝ) (k : ℕ) :
    shiftedStieltjesNumerators c u v (2 * k + 1) = v k * u (k + 1) / (1 + u k) := by
  simp [shiftedStieltjesNumerators, Nat.add_div, Nat.mul_comm]

/-- The even-indexed numerator before translation is `v k`. -/
@[simp] theorem stieltjesNumeratorsBeforeShift_even (c : ℝ) (u v : ℕ → ℝ) (k : ℕ) :
    stieltjesNumeratorsBeforeShift c u v (2 * k) = v k := by
  simp [stieltjesNumeratorsBeforeShift, Nat.mul_comm]

/-- The odd-indexed numerator before translation. -/
@[simp] theorem stieltjesNumeratorsBeforeShift_odd (c : ℝ) (u v : ℕ → ℝ) (k : ℕ) :
    stieltjesNumeratorsBeforeShift c u v (2 * k + 1) =
      u (k + 1) * (c * (1 + u k) + v k) / (1 + u k) := by
  simp [stieltjesNumeratorsBeforeShift, Nat.add_div, Nat.mul_comm]

/-- Nonnegative parameters give nonnegative numerator data before translation. -/
theorem stieltjesNumeratorsBeforeShift_nonneg {c : ℝ} (hc : 0 ≤ c)
    {u v : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k) (n : ℕ) :
    0 ≤ stieltjesNumeratorsBeforeShift c u v n := by
  unfold stieltjesNumeratorsBeforeShift
  split_ifs
  · exact hv _
  · exact div_nonneg (mul_nonneg (hu _)
      (add_nonneg (mul_nonneg hc (add_nonneg zero_le_one (hu _))) (hv _)))
      (add_nonneg zero_le_one (hu _))

/-- The displayed lower-support parameters give nonnegative Stieltjes numerators. -/
theorem shiftedStieltjesNumerators_nonneg {c : ℝ} (hc : 0 ≤ c)
    {u v : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k) (n : ℕ) :
    0 ≤ shiftedStieltjesNumerators c u v n := by
  unfold shiftedStieltjesNumerators
  split_ifs
  · exact add_nonneg (mul_nonneg hc (add_nonneg zero_le_one (hu _))) (hv _)
  · exact div_nonneg (mul_nonneg (hv _) (hu _)) (add_nonneg zero_le_one (hu _))

/-- Classical odd numerators of the existential parametrization are at least the shift. -/
theorem le_shiftedStieltjesNumerators_even {c : ℝ} (hc : 0 ≤ c)
    {u v : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k) (k : ℕ) :
    c ≤ shiftedStieltjesNumerators c u v (2 * k) := by
  rw [shiftedStieltjesNumerators_even, mul_add, mul_one]
  simpa only [add_assoc] using
    (le_add_of_nonneg_right (add_nonneg (mul_nonneg hc (hu k)) (hv k)) :
      c ≤ c + (c * u k + v k))

/-- Contraction shifts the Jacobi diagonal by `c` when the initial even parameter is zero. -/
theorem stieltjesJacobiDiagonal_shifted {c : ℝ} {u v : ℕ → ℝ}
    (hu : ∀ k, 0 ≤ u k) (hu0 : u 0 = 0) (n : ℕ) :
    stieltjesJacobiDiagonal (shiftedStieltjesNumerators c u v) n =
      stieltjesJacobiDiagonal (stieltjesNumeratorsBeforeShift c u v) n + c := by
  cases n with
  | zero => simp [stieltjesJacobiDiagonal, shiftedStieltjesNumerators,
      stieltjesNumeratorsBeforeShift, hu0, add_comm]
  | succ n =>
      change shiftedStieltjesNumerators c u v (2 * n + 1) +
          shiftedStieltjesNumerators c u v (2 * n + 2) =
        stieltjesNumeratorsBeforeShift c u v (2 * n + 1) +
          stieltjesNumeratorsBeforeShift c u v (2 * n + 2) + c
      rw [show 2 * n + 2 = 2 * (n + 1) by ring,
        shiftedStieltjesNumerators_odd, shiftedStieltjesNumerators_even,
        stieltjesNumeratorsBeforeShift_odd, stieltjesNumeratorsBeforeShift_even]
      have hden : 1 + u n ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (hu n))
      field_simp [hden]
      ring

/-- Contraction preserves the outgoing Jacobi numerator. -/
theorem stieltjesJacobiNumerator_shifted (c : ℝ) (u v : ℕ → ℝ) (n : ℕ) :
    stieltjesJacobiNumerator (shiftedStieltjesNumerators c u v) n =
      stieltjesJacobiNumerator (stieltjesNumeratorsBeforeShift c u v) n := by
  simp only [stieltjesJacobiNumerator, shiftedStieltjesNumerators_even,
    shiftedStieltjesNumerators_odd, stieltjesNumeratorsBeforeShift_even,
    stieltjesNumeratorsBeforeShift_odd, div_eq_mul_inv]
  ring

/-- The parametrized fraction is the binomial transform of its unshifted data. -/
theorem binomialTransform_beforeShift {c : ℝ} {u v : ℕ → ℝ}
    (hu : ∀ k, 0 ≤ u k) (hu0 : u 0 = 0) :
    binomialTransform c (stieltjesTail (stieltjesNumeratorsBeforeShift c u v) 0) =
      stieltjesTail (shiftedStieltjesNumerators c u v) 0 :=
  binomialTransform_stieltjesTail_eq c (stieltjesJacobiDiagonal_shifted hu hu0)
    (stieltjesJacobiNumerator_shifted c u v)

end PowerSeries
