/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Ring

/-!
# Bounds for positive spectral exponential sums

A summable inverse power of positive rates dominates every exponentially
damped natural moment. This is the scalar estimate underlying Lemma 2 of
R. Zhang, `Complete Monotonicity of Special Functions`, arXiv:1506.07012v13,
equations (2.3) and (2.8). Arbitrary index types and nonnegative exponents
include finite and empty spectra.
-/

public section

open Filter Topology

namespace Real

/-- Exponential damping dominates a natural power, with a bound adapted to
an inverse spectral moment. The constant is independent of both variables. -/
theorem exists_pow_mul_exp_neg_mul_le_rpow {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r t : ℝ, 0 < r → 0 < t →
      r ^ k * exp (-r * t) ≤ C * t ^ (-(a + (k : ℝ))) * r ^ (-a) := by
  obtain ⟨C, hC, hbound⟩ := TauCeti.exists_rpow_mul_exp_neg_mul_le
    (add_nonneg ha (Nat.cast_nonneg k)) (show (0 : ℝ) < 1 by norm_num)
  refine ⟨C, hC, fun r t hr ht ↦ ?_⟩
  have hrpow : r ^ (a + (k : ℝ)) * r ^ (-a) = r ^ k := by
    rw [← rpow_add hr, show a + (k : ℝ) + -a = (k : ℝ) by ring, rpow_natCast]
  have htpow : t ^ (a + (k : ℝ)) * t ^ (-(a + (k : ℝ))) = 1 := by
    rw [← rpow_add ht, add_neg_cancel, rpow_zero]
  have hid : r ^ k * exp (-r * t) =
      ((r * t) ^ (a + (k : ℝ)) * exp (-(r * t))) *
        (r ^ (-a) * t ^ (-(a + (k : ℝ)))) := by
    rw [mul_rpow hr.le ht.le]
    calc r ^ k * exp (-r * t)
        = (r ^ (a + (k : ℝ)) * r ^ (-a)) *
            (t ^ (a + (k : ℝ)) * t ^ (-(a + (k : ℝ)))) * exp (-(r * t)) := by
              rw [hrpow, htpow]
              simp only [mul_one, neg_mul]
      _ = _ := by ring
  rw [hid]
  calc _ ≤ C * (r ^ (-a) * t ^ (-(a + (k : ℝ)))) :=
      mul_le_mul_of_nonneg_right
        (by simpa only [one_mul] using hbound (r * t) (mul_nonneg hr.le ht.le))
        (by positivity)
    _ = _ := by ring

/-- Any natural moment of positive rates is summable after exponential
damping, provided one inverse spectral moment is summable. -/
theorem summable_pow_mul_exp_neg_mul {ι : Type*} {r : ι → ℝ} {a : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (hs : Summable (fun i ↦ r i ^ (-a)))
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun i ↦ r i ^ k * exp (-r i * t)) := by
  obtain ⟨C, _, hC⟩ := exists_pow_mul_exp_neg_mul_le_rpow ha k
  exact Summable.of_nonneg_of_le
    (fun i ↦ mul_nonneg (pow_nonneg (hr i).le _) (exp_nonneg _))
    (fun i ↦ hC (r i) t (hr i) ht) (hs.mul_left (C * t ^ (-(a + (k : ℝ)))))

/-- An inverse spectral moment gives a global power bound for the
corresponding exponentially damped natural moment on the open half-line. -/
theorem exists_tsum_pow_mul_exp_neg_mul_le {ι : Type*} {r : ι → ℝ} {a : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (hs : Summable (fun i ↦ r i ^ (-a)))
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      (∑' i, r i ^ k * exp (-r i * t)) ≤ C * t ^ (-(a + (k : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_pow_mul_exp_neg_mul_le_rpow ha k
  refine ⟨C * ∑' i, r i ^ (-a),
    mul_nonneg hC (tsum_nonneg fun i ↦ (rpow_pos_of_pos (hr i) (-a)).le),
    fun t ht ↦ ?_⟩
  calc (∑' i, r i ^ k * exp (-r i * t))
      ≤ ∑' i, C * t ^ (-(a + (k : ℝ))) * r i ^ (-a) :=
        Summable.tsum_le_tsum (fun i ↦ hbound (r i) t (hr i) ht)
          (summable_pow_mul_exp_neg_mul hr ha hs k ht)
          (hs.mul_left (C * t ^ (-(a + (k : ℝ)))))
    _ = _ := by rw [tsum_mul_left]; ring

/-- Larger inverse powers of positive rates are summable whenever a
nonnegative inverse power is summable. Finite exceptional small rates do
not require a uniform lower bound in the hypotheses. -/
theorem summable_rpow_neg_of_le {ι : Type*} {r : ι → ℝ} {a p : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (hs : Summable (fun i ↦ r i ^ (-a)))
    (hap : a ≤ p) : Summable (fun i ↦ r i ^ (-p)) := by
  apply Summable.of_norm_bounded_eventually hs
  filter_upwards [hs.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)] with i hi
  have hri : 1 ≤ r i := by
    rcases (rpow_lt_one_iff_of_pos (hr i)).mp hi with h | h
    · exact h.1.le
    · linarith [h.2]
  rw [Real.norm_eq_abs, abs_of_pos (rpow_pos_of_pos (hr i) _)]
  exact rpow_le_rpow_of_exponent_le hri (neg_le_neg hap)

/-- In particular, Zhang's exponent below one controls every reciprocal
natural power appearing in the Laplace transform, including the endpoint. -/
theorem summable_inv_pow_of_inverse_moment {ι : Type*} {r : ι → ℝ} {a : ℝ}
    (hr : ∀ i, 0 < r i) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hs : Summable (fun i ↦ r i ^ (-a))) (k : ℕ) :
    Summable (fun i ↦ (r i ^ (k + 1))⁻¹) := by
  have h := summable_rpow_neg_of_le hr ha hs
    (ha1.trans (show (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)))
  apply h.congr
  intro i
  rw [rpow_neg (hr i).le, rpow_natCast]

end Real
