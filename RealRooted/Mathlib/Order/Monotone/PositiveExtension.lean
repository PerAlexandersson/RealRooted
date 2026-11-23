/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Basic.NNReal.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Positive summable extensions of decreasing finite sequences

A strictly decreasing finite family of positive nonnegative reals extends to
a strictly decreasing positive summable sequence. A geometric tail starts below
the final entry. The empty family has a separate geometric extension.
-/

public section

open scoped NNReal ENNReal

namespace StrictAnti

/-- Extend a finite positive decreasing family by a summable geometric tail.
The result includes `Fin 0`, without selecting a nonexistent final entry. -/
theorem exists_pos_summable_nat_extension {n : ℕ} {a : Fin n → ℝ≥0}
    (ha : StrictAnti a) (hpos : ∀ i, 0 < a i) :
    ∃ b : ℕ → ℝ≥0, StrictAnti b ∧ (∀ i, 0 < b i) ∧
      Summable (fun i ↦ (b i : ℝ)) ∧ ∀ i : Fin n, b i.val = a i := by
  cases n with
  | zero =>
    refine ⟨fun i ↦ (1 / 2 : ℝ≥0) ^ i, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hij
    · intro i
      positivity
    · simpa only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
        summable_geometric_two
    · intro i
      exact Fin.elim0 i
  | succ n =>
    let c : ℝ≥0 := a (Fin.last n) / 2
    have hc : 0 < c := div_pos (hpos _) (by norm_num)
    have hclt : c < a (Fin.last n) := by
      exact div_lt_self (hpos _) (by norm_num)
    let b : ℕ → ℝ≥0 := fun i ↦
      if h : i < n + 1 then a ⟨i, h⟩ else c * (1 / 2) ^ (i - (n + 1))
    have hmono : StrictAnti b := by
      intro i j hij
      dsimp only [b]
      by_cases hi : i < n + 1
      · by_cases hj : j < n + 1
        · rw [dite_eq_left hi, dite_eq_left hj]
          exact ha hij
        · rw [dite_eq_left hi, dite_eq_right hj]
          have htail : c * (1 / 2 : ℝ≥0) ^ (j - (n + 1)) ≤ c :=
            mul_le_of_le_one_right hc.le (pow_le_one₀ (by positivity) (by norm_num))
          exact htail.trans_lt (hclt.trans_le (ha.antitone (Fin.le_last _)))
      · have hj : ¬ j < n + 1 := fun hj ↦ hi (hij.trans hj)
        rw [dite_eq_right hi, dite_eq_right hj]
        apply mul_lt_mul_of_pos_left _ hc
        apply pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num)
        lia
    refine ⟨b, hmono, ?_, ?_, ?_⟩
    · intro i
      dsimp only [b]
      split_ifs with hi
      · exact hpos _
      · exact mul_pos hc (pow_pos (by norm_num) _)
    · apply (summable_nat_add_iff (n + 1)).mp
      have heq (i : ℕ) : (b (i + (n + 1)) : ℝ) = (c : ℝ) * (1 / 2 : ℝ) ^ i := by
        simp only [b, dite_eq_right (show ¬ i + (n + 1) < n + 1 by lia),
          Nat.add_sub_cancel, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div,
          NNReal.coe_one, NNReal.coe_ofNat]
      simp_rw [heq]
      exact summable_geometric_two.mul_left _
    · intro i
      simp only [b, dite_eq_left i.isLt]

end StrictAnti
