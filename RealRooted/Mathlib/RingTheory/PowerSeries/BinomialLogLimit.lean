/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.RingTheory.Binomial
import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialPositive
public import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

/-! # The logarithmic limit of normalized multichoose coefficients -/

public section

open Filter Polynomial Topology

namespace Ring

/-- Cancelling the initial factor of a positive-degree rising factorial gives
a polynomial formula for the normalized multichoose coefficient away from zero. -/
theorem multichoose_succ_div {a : ℝ} (ha : a ≠ 0) (n : ℕ) :
    multichoose a (n + 1) / a =
      (ascPochhammer ℝ n).eval (a + 1) / ((n + 1).factorial : ℝ) := by
  have hfact : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  have h := factorial_mul_multichoose a (n + 1)
  rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp,
    eval_add, eval_X, eval_one] at h
  apply (div_eq_div_iff ha hfact).2
  calc
    _ = ((n + 1).factorial : ℝ) * multichoose a (n + 1) := mul_comm _ _
    _ = a * (ascPochhammer ℝ n).eval (a + 1) := h
    _ = _ := mul_comm _ _

/-- The positive-degree multichoose coefficient divided by its parameter
has a removable singularity at zero, with logarithmic value `1/k`. -/
theorem tendsto_multichoose_succ_div (n : ℕ) :
    Tendsto (fun a : ℝ ↦ multichoose a (n + 1) / a) (𝓝[≠] 0)
      (𝓝 (1 / (n + 1 : ℝ))) := by
  have hc : Continuous (fun a : ℝ ↦
      (ascPochhammer ℝ n).eval (a + 1) / ((n + 1).factorial : ℝ)) :=
    ((ascPochhammer ℝ n).continuous.comp (continuous_id.add continuous_const)).div_const _
  have hfac : (n.factorial : ℝ) / ((n + 1).factorial : ℝ) = 1 / (n + 1 : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    ring
  have hlim : Tendsto (fun a : ℝ ↦
      (ascPochhammer ℝ n).eval (a + 1) / ((n + 1).factorial : ℝ))
      (𝓝[≠] 0) (𝓝 (1 / (n + 1 : ℝ))) := by
    simpa only [zero_add, ascPochhammer_eval_one, hfac] using
      ((hc.tendsto 0).mono_left nhdsWithin_le_nhds)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (multichoose_succ_div (by simpa using ha) n).symm

/-- The logarithmic multichoose limit along strictly positive parameters. -/
theorem tendsto_multichoose_succ_div_nhdsGT (n : ℕ) :
    Tendsto (fun a : ℝ ↦ multichoose a (n + 1) / a) (𝓝[>] 0)
      (𝓝 (1 / (n + 1 : ℝ))) := by
  apply (tendsto_multichoose_succ_div n).mono_left
  apply nhdsWithin_mono
  intro a ha
  exact ne_of_gt ha

/-- The normalized multichoose limit for an arbitrary positive degree. -/
theorem tendsto_multichoose_div_nhdsGT (k : ℕ) (hk : k ≠ 0) :
    Tendsto (fun a : ℝ ↦ multichoose a k / a) (𝓝[>] 0) (𝓝 (1 / (k : ℝ))) := by
  cases k with
  | zero => exact (hk rfl).elim
  | succ n => simpa only [Nat.cast_add, Nat.cast_one] using
      tendsto_multichoose_succ_div_nhdsGT n

/-- Finite linear combinations of normalized multichoose coefficients
converge to the corresponding logarithmic coefficients. -/
theorem tendsto_sum_multichoose_div_nhdsGT (s : Finset ℕ)
    (hs : ∀ k ∈ s, k ≠ 0) (c : ℕ → ℝ) :
    Tendsto (fun a : ℝ ↦ ∑ k ∈ s, multichoose a k / a * c k) (𝓝[>] 0)
      (𝓝 (∑ k ∈ s, c k / (k : ℝ))) := by
  have h := tendsto_finsetSum s (fun k hk ↦
    (tendsto_multichoose_div_nhdsGT k (hs k hk)).mul_const (c k))
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h

end Ring
