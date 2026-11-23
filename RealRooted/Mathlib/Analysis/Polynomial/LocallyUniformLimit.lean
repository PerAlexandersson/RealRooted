/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.MulAction
import RealRooted.Mathlib.Topology.Algebra.IsUniformGroup.FiniteSum
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Operations

import Mathlib.Tactic.TypeStar

/-!
# Locally uniform polynomial limits from a common finite degree bound
-/

public section

open Filter Topology

namespace Polynomial

/-- Coefficientwise convergence in a fixed finite degree range gives locally
uniform convergence of polynomial evaluations. Zero and constant limits are allowed. -/
theorem tendstoLocallyUniformly_eval_of_coeff_tendsto
    {K ι : Type*} [SeminormedRing K] {l : Filter ι}
    {P : ι → K[X]} {Q : K[X]} {N : ℕ}
    (hP : ∀ i, (P i).natDegree ≤ N) (hQ : Q.natDegree ≤ N)
    (hcoeff : ∀ k ≤ N, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k))) :
    TendstoLocallyUniformly (fun i z ↦ (P i).eval z) (fun z ↦ Q.eval z) l := by
  have heqP : (fun i z ↦ (P i).eval z) =
      (fun i z ↦ ∑ k ∈ Finset.range (N + 1), (P i).coeff k * z ^ k) := by
    funext i z
    exact eval_eq_sum_range' (Nat.lt_succ_of_le (hP i)) z
  have heqQ : (fun z ↦ Q.eval z) =
      (fun z ↦ ∑ k ∈ Finset.range (N + 1), Q.coeff k * z ^ k) := by
    funext z
    exact eval_eq_sum_range' (Nat.lt_succ_of_le hQ) z
  rw [heqP, heqQ]
  apply TendstoLocallyUniformly.finset_sum
  intro k hk
  have hconst : TendstoUniformly (fun i ↦ fun _ : K ↦ (P i).coeff k)
      (fun _ : K ↦ Q.coeff k) l :=
    (hcoeff k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).tendstoUniformly_const
  have hpow := tendstoLocallyUniformly_const_family (fun z : K ↦ z ^ k) l
  simpa only [Pi.mul_def] using hconst.tendstoLocallyUniformly.mul₀
    hpow continuous_const (continuous_id.pow k)

end Polynomial
