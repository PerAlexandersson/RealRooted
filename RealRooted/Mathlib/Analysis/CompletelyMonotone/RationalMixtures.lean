/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Basic
import TauCeti.Analysis.CompletelyMonotone.Closure
import TauCeti.Analysis.CompletelyMonotone.Reciprocal
import TauCeti.Analysis.CompletelyMonotone.Reparametrization
import TauCeti.Analysis.CompletelyMonotone.Limits
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Positive mixtures of affine reciprocal powers

Summable nonnegative masses give completely monotone mixtures of the kernels
`(1 + a * x)⁻ʳ`, with arbitrary nonnegative slopes. The slope powers occurring
in logarithmic derivatives of convergent linear products are a specialization.
No order or zero-enumeration assumption is needed for this kernel statement.
-/

public section

open Filter Topology

/-- Every positive natural power of a summable real family is summable. -/
theorem Summable.pow_succ {ι : Type*} {a : ι → ℝ} (hs : Summable a) (m : ℕ) :
    Summable (fun i ↦ a i ^ (m + 1)) := by
  convert hs.norm.mul_tendsto_const (hs.tendsto_cofinite_zero.pow m) using 1
  funext i
  ring

namespace TauCeti

/-- Every nonnegative multiple of a natural reciprocal power of a positive
affine function is completely monotone on the closed nonnegative half-line. -/
theorem isCompletelyMonotone_const_div_one_add_mul_pow
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℕ) :
    IsCompletelyMonotone (fun x : ℝ ↦ b / (1 + a * x) ^ r) := by
  have h := ((isCompletelyMonotone_one_div_one_add.comp_const_mul ha).pow r).smul hb
  apply h.congr
  intro x _
  simp only [Pi.smul_apply, smul_eq_mul, Pi.pow_apply, inv_pow,
    div_eq_mul_inv, one_mul]

/-- Summable nonnegative masses dominate their affine reciprocal mixtures
at every nonnegative argument, including the endpoint zero. -/
theorem summable_const_div_one_add_mul_pow {ι : Type*} {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hs : Summable b)
    (r : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun i ↦ b i / (1 + a i * x) ^ r) := by
  apply Summable.of_nonneg_of_le
    (fun i ↦ div_nonneg (hb i)
      (pow_nonneg (add_nonneg zero_le_one (mul_nonneg (ha i) hx)) _)) ?_ hs
  intro i
  apply div_le_self (hb i)
  exact one_le_pow₀ (le_add_of_nonneg_right (mul_nonneg (ha i) hx))

/-- Arbitrary positive summable mixtures of natural reciprocal powers are
completely monotone on the open half-line. Zero slopes and repeated slopes
are allowed, and the exponent may be zero. -/
theorem isCompletelyMonotoneOnIoi_tsum_const_div_one_add_mul_pow
    {a b : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hs : Summable b) (r : ℕ) :
    IsCompletelyMonotoneOnIoi (fun x : ℝ ↦ ∑' i, b i / (1 + a i * x) ^ r) := by
  apply isCompletelyMonotoneOnIoi_of_tendsto (L := atTop)
    (F := fun n x ↦ ∑ i ∈ Finset.range n, b i / (1 + a i * x) ^ r)
  · exact Filter.Eventually.of_forall fun n ↦
      (IsCompletelyMonotone.sum (s := Finset.range n) fun i _ ↦
        isCompletelyMonotone_const_div_one_add_mul_pow (ha i) (hb i) r).isCompletelyMonotoneOnIoi
  · intro x hx
    exact (summable_const_div_one_add_mul_pow ha hb hs r hx.le).hasSum.tendsto_sum_nat

/-- Every positive-index slope-power mixture of a summable nonnegative
linear product is completely monotone. -/
theorem isCompletelyMonotoneOnIoi_tsum_pow_div_one_add_mul_pow
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (m r : ℕ) :
    IsCompletelyMonotoneOnIoi
      (fun x : ℝ ↦ ∑' i, a i ^ (m + 1) / (1 + a i * x) ^ r) := by
  exact isCompletelyMonotoneOnIoi_tsum_const_div_one_add_mul_pow
    ha (fun i ↦ pow_nonneg (ha i) _) (hs.pow_succ m) r

/-- The rational-kernel side of the two-index logarithmic-derivative
hierarchy is completely monotone. The constant term retains the exponential
factor, including the `m = 0` boundary. -/
theorem isCompletelyMonotoneOnIoi_factorial_resolvent_sum
    {a : ℕ → ℝ} {gamma : ℝ} (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (hg : 0 ≤ gamma) (k m : ℕ) :
    IsCompletelyMonotoneOnIoi (fun x : ℝ ↦
      (k.factorial : ℝ) * gamma * 0 ^ m +
        ((k + m).factorial : ℝ) *
          ∑' i, a i ^ (m + 1) / (1 + a i * x) ^ (k + m + 1)) := by
  have hc := (isCompletelyMonotone_const
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg k.factorial) hg)
      (pow_nonneg (show (0 : ℝ) ≤ 0 from le_rfl) m))).isCompletelyMonotoneOnIoi
  have hp := (isCompletelyMonotoneOnIoi_tsum_pow_div_one_add_mul_pow ha hs m
    (k + m + 1)).smul (Nat.cast_nonneg (k + m).factorial : (0 : ℝ) ≤ _)
  apply (hc.add hp).congr
  intro x _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

end TauCeti
