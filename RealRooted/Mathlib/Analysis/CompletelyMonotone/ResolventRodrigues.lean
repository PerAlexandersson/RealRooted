/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.EulerRodrigues
public import RealRooted.Mathlib.Analysis.CompletelyMonotone.ResolventHierarchy
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Ring

/-!
# Rodrigues derivatives of positive resolvent sums

The Euler recurrence identifies monomial-normalized derivatives with the
positive factorial resolvent hierarchy. A separate algebraic identity puts
the result in the original signed weighted-derivative form.
-/

public section

open Filter Topology
open scoped ContDiff

namespace Real

/-- A smooth function agreeing with the zeroth resolvent row has the whole
resolvent hierarchy as its normalized Rodrigues derivatives. -/
theorem eulerRodrigues_eq_weightedResolventSum
    {a : ℕ → ℝ} {gamma : ℝ} {g : ℝ → ℝ} {m : ℕ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (hg : ContDiffOn ℝ ∞ g (Set.Ioi 0))
    (hbase : Set.EqOn g (weightedResolventSum a gamma 0 m) (Set.Ioi 0))
    (k : ℕ) {x : ℝ} (hx : 0 < x) :
    eulerRodrigues g m k x = weightedResolventSum a gamma k m x := by
  induction k generalizing x with
  | zero => rw [eulerRodrigues_zero g m hx.ne']; exact hbase hx
  | succ k ih =>
      have heq : eulerRodrigues g m k =ᶠ[𝓝 x] weightedResolventSum a gamma k m :=
        Filter.Eventually.mono
          (isOpen_Ioi.mem_nhds (show x ∈ Set.Ioi (0 : ℝ) from hx)) fun y hy ↦ ih hy
      rw [eulerRodrigues_succ hg m k hx, ih hx, heq.deriv_eq]
      simpa only [Nat.cast_add, Nat.cast_one] using
        mul_weightedResolventSum_add_mul_deriv ha hs gamma k m hx

/-- Moving the constant alternating sign through Rodrigues differentiation
gives the original weighted-derivative expression. This algebraic identity
also holds at zero with Lean's usual totalized division convention. -/
theorem eulerRodrigues_signed_iteratedDeriv (L : ℝ → ℝ) (m k : ℕ) (x : ℝ) :
    eulerRodrigues (fun y : ℝ ↦ (-1 : ℝ) ^ m * iteratedDeriv m L y) m k x =
      (-1 / x) ^ m * iteratedDeriv k (fun y : ℝ ↦
        y ^ (k + m) * iteratedDeriv m L y) x := by
  have heq : (fun y : ℝ ↦ y ^ (m + k) * ((-1 : ℝ) ^ m * iteratedDeriv m L y)) =
      (fun y : ℝ ↦ (-1 : ℝ) ^ m * (y ^ (k + m) * iteratedDeriv m L y)) := by
    funext y
    rw [Nat.add_comm m k]
    ring
  rw [eulerRodrigues, heq, iteratedDeriv_const_mul_field, div_pow]
  ring

end Real
