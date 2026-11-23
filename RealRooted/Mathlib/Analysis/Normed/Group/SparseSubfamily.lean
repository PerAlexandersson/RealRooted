/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Summable sparse subfamilies of square-summable real families

Infinite nonzero support contains a sequence with strictly decreasing absolute
values and summable absolute values. In particular the selected values are
distinct, not merely their indices.
-/

public section

open Filter Topology

namespace Real

/-- Infinite support of a square-summable family has arbitrarily small nonzero terms. -/
private theorem exists_abs_lt_of_infinite_support {ι : Type*} {a : ι → ℝ}
    (hs : Summable (fun i ↦ a i ^ 2)) (hi : (Function.support a).Infinite)
    {ε : ℝ} (hε : 0 < ε) : ∃ i, a i ≠ 0 ∧ |a i| < ε := by
  have he : ∀ᶠ i in cofinite, a i ^ 2 < ε ^ 2 :=
    hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  obtain ⟨i, hi, hsmall⟩ := (hi.frequently_cofinite.and_eventually he).exists
  refine ⟨i, hi, ?_⟩
  nlinarith [sq_abs (a i), abs_nonneg (a i)]

/-- Infinite nonzero support of a square-summable real family contains an
injectively indexed, absolutely summable subfamily with distinct values. -/
theorem exists_summable_subfamily_of_summable_sq {ι : Type*} {a : ι → ℝ}
    (hs : Summable (fun i ↦ a i ^ 2)) (hi : (Function.support a).Infinite) :
    ∃ e : ℕ ↪ ι, (∀ n, a (e n) ≠ 0) ∧ Function.Injective (fun n ↦ a (e n)) ∧
      StrictAnti (fun n ↦ |a (e n)|) ∧ Summable (fun n ↦ a (e n)) := by
  classical
  have hnext (i : Function.support a) :
      ∃ j : Function.support a, |a j| < |a i| / 2 := by
    obtain ⟨j, hj, hsmall⟩ := exists_abs_lt_of_infinite_support hs hi
      (half_pos (abs_pos.mpr i.property))
    exact ⟨⟨j, hj⟩, hsmall⟩
  choose next hn using hnext
  obtain ⟨i₀, hi₀⟩ := hi.nonempty
  let u : ℕ → Function.support a :=
    fun n ↦ Nat.rec (⟨i₀, hi₀⟩ : Function.support a) (fun _ i ↦ next i) n
  have hstep (n : ℕ) : |a (u (n + 1)).val| < |a (u n).val| / 2 := by
    simpa only [u] using hn (u n)
  have hanti : StrictAnti (fun n ↦ |a (u n).val|) := by
    apply strictAnti_nat_of_succ_lt
    intro n
    exact (hstep n).trans (half_lt_self (abs_pos.mpr (u n).property))
  have hval : Function.Injective (fun n ↦ a (u n).val) := by
    intro n m h
    exact hanti.injective (congrArg abs h)
  let e : ℕ ↪ ι := ⟨fun n ↦ (u n).val, fun n m h ↦ hval (congrArg a h)⟩
  refine ⟨e, fun n ↦ (u n).property, hval, hanti, ?_⟩
  have hbound (n : ℕ) : |a (u n).val| ≤ |a i₀| * (1 / 2 : ℝ) ^ n := by
    induction n with
    | zero => simp [u]
    | succ n ih =>
        calc
          _ ≤ |a (u n).val| / 2 := (hstep n).le
          _ ≤ (|a i₀| * (1 / 2 : ℝ) ^ n) / 2 := by linarith
          _ = _ := by rw [pow_succ]; ring
  exact (summable_geometric_two.mul_left |a i₀|).of_norm_bounded
    (fun n ↦ by
      rw [Real.norm_eq_abs]
      change |a (u n).val| ≤ _
      exact hbound n)

end Real
