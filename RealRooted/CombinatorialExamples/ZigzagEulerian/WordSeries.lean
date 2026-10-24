/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.ZigzagEulerian.WordRecurrence
public import RealRooted.CenteredEulerian.Riccati
public import Mathlib.Tactic

/-!
# Odd evaluations of the centered zig-zag polynomials

Appendix A.1. The first-maximum recurrence gives a Möbius recurrence for the
word generating series; the reusable Riccati uniqueness theorem identifies it
with the centered Eulerian series.
-/

@[expose] public section

open PowerSeries
open RealRooted.CenteredEulerian

noncomputable section
namespace RealRooted.ZigzagEulerian

/-- `F_k(2s) = ∑ 2ⁿ Ω_n(k) sⁿ`. -/
noncomputable def weakUpDownWordSeries (k : ℕ) : ℝ⟦X⟧ :=
  mk (fun n => (2 : ℝ) ^ n * weakUpDownWordCount n k)

/-- The empty alphabet contributes only the constant term to the word series. -/
lemma weakUpDownWordSeries_zero : weakUpDownWordSeries 0 = 1 := by
  ext n
  rw [weakUpDownWordSeries, coeff_mk, coeff_one]
  rcases n with _ | n
  · simp [weakUpDownWordCount_zero]
  · rw [weakUpDownWordCount_zero_alphabet _ (by lia)]; simp

/-- The first-maximum recurrence yields the Möbius relation for the word series. -/
lemma weakUpDownWordSeries_step (k : ℕ) :
    weakUpDownWordSeries (k + 1) *
        (1 - 2 * X ^ 2 - X * weakUpDownWordSeries k) =
      weakUpDownWordSeries k + X := by
  ext n
  have hA := weakUpDownWordCount_recurrence n k
  have hAR : (2 : ℝ) * weakUpDownWordCount n (k + 1) = 2 * weakUpDownWordCount n k +
      ∑ p ∈ Finset.range n,
        (weakUpDownWordCount p k : ℝ) * weakUpDownWordCount (n - 1 - p) (k + 1) +
      (if n = 1 then 1 else 0) +
        (if 2 ≤ n then (weakUpDownWordCount (n - 2) (k + 1) : ℝ) else 0) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hA
    push_cast at h
    split_ifs at h ⊢ <;> linarith
  have e1 :
      (weakUpDownWordSeries (k + 1) *
        (1 - 2 * X ^ 2 - X * weakUpDownWordSeries k) : ℝ⟦X⟧) =
      weakUpDownWordSeries (k + 1) - 2 * (X ^ 2 * weakUpDownWordSeries (k + 1)) -
        X * (weakUpDownWordSeries k * weakUpDownWordSeries (k + 1)) := by ring
  rw [e1, map_sub, map_sub, map_add, coeff_X_mul', coeff_X]
  rw [show (2 : ℝ⟦X⟧) * (X ^ 2 * weakUpDownWordSeries (k + 1)) =
      C (2 : ℝ) * (X ^ 2 * weakUpDownWordSeries (k + 1))
    by rw [map_ofNat], coeff_C_mul, coeff_X_pow_mul']
  simp only [weakUpDownWordSeries, coeff_mk]
  rcases n with _ | n
  · simp [weakUpDownWordCount_zero]
  · rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_mk, Nat.add_sub_cancel, show 1 ≤ n + 1 by lia, ite_true]
    have hconv : ∑ p ∈ Finset.range (n + 1), (2 : ℝ) ^ p * (weakUpDownWordCount p k : ℝ) *
        ((2 : ℝ) ^ (n - p) * weakUpDownWordCount (n - p) (k + 1)) =
        2 ^ n * ∑ p ∈ Finset.range (n + 1), (weakUpDownWordCount p k : ℝ) *
          weakUpDownWordCount (n + 1 - 1 - p) (k + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro p hp
      have hp' := Finset.mem_range.mp hp
      rw [show n + 1 - 1 - p = n - p by lia]
      rw [show (2 : ℝ) ^ n = 2 ^ p * 2 ^ (n - p) by rw [← pow_add]; congr 1; lia]
      ring
    rw [hconv]
    rcases n with _ | n
    · simp at hAR ⊢; linarith
    · simp only [show ¬ (n + 1 + 1 = 1) by lia, ite_false, show 2 ≤ n + 1 + 1 by lia,
        ite_true, show n + 1 + 1 - 2 = n by lia, add_zero] at hAR ⊢
      linear_combination (2 : ℝ) ^ n * 2 * hAR

/-- (A.3): `p_n(2k+1) = 2ⁿ Ω_n(k)` for `n ≥ 2`. -/
theorem polynomial_eval_odd_weakWordCount {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    (polynomial n).eval (2 * (k : ℝ) + 1) =
      2 ^ n * weakUpDownWordCount n k := by
  have h := eq_gSeries_of_mobius (fun k => weakUpDownWordSeries k + X) (by
    show weakUpDownWordSeries 0 + X = 1 + X; rw [weakUpDownWordSeries_zero])
    (fun k => by linear_combination weakUpDownWordSeries_step k) k
  have hc := congrArg (coeff n) h
  rw [coeff_gSeries, map_add, coeff_X, ite_eq_right (by lia), add_zero,
    weakUpDownWordSeries, coeff_mk] at hc
  exact hc.symm

end RealRooted.ZigzagEulerian
