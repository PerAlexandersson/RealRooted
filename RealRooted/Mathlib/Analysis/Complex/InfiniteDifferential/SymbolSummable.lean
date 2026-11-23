/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.EulerRodrigues

/-!
# Algebra of summable infinite differential symbols
-/

public section

namespace Complex

/-- Addition of entire symbols is linear whenever both actual differential
series are summable. The target need not be analytic for this identity. -/
theorem infiniteDifferentialApply_add_symbol_of_summable {φ ψ f : ℂ → ℂ}
    (hφ : Differentiable ℂ φ) (hψ : Differentiable ℂ ψ)
    (hsφ : ∀ z, Summable (fun n : ℕ ↦
      iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ)))
    (hsψ : ∀ z, Summable (fun n : ℕ ↦
      iteratedDeriv n ψ 0 * iteratedDeriv n f z / (n.factorial : ℂ))) :
    infiniteDifferentialApply (fun z ↦ φ z + ψ z) f =
      infiniteDifferentialApply φ f + infiniteDifferentialApply ψ f := by
  ext z
  simp only [infiniteDifferentialApply, Pi.add_apply,
    iteratedDeriv_fun_add hφ.contDiff.contDiffAt hψ.contDiff.contDiffAt, add_mul, add_div]
  exact (hsφ z).tsum_add (hsψ z)

/-- A variable factor shifts an actually summable differential series.
Only the shifted target's series is required to be summable. -/
theorem infiniteDifferentialApply_id_mul_of_summable {φ f : ℂ → ℂ}
    (hφ : Differentiable ℂ φ)
    (hs : ∀ z, Summable (fun n : ℕ ↦
      iteratedDeriv n φ 0 * iteratedDeriv n (deriv f) z / (n.factorial : ℂ))) :
    infiniteDifferentialApply (fun z ↦ z * φ z) f =
      infiniteDifferentialApply φ (deriv f) := by
  ext z
  let u : ℕ → ℂ := fun n ↦
    iteratedDeriv n (fun w ↦ w * φ w) 0 * iteratedDeriv n f z / (n.factorial : ℂ)
  have hterm (n : ℕ) : u (n + 1) =
      iteratedDeriv n φ 0 * iteratedDeriv n (deriv f) z / (n.factorial : ℂ) := by
    dsimp only [u]
    rw [iteratedDeriv_succ_id_mul hφ.contDiff.contDiffAt]
    simp only [zero_mul, zero_add, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, ← iteratedDeriv_succ']
    have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hnf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    field_simp [hn, hnf]
  have htail : HasSum (fun n ↦ u (n + 1))
      (infiniteDifferentialApply φ (deriv f) z) := by
    simpa only [hterm, infiniteDifferentialApply] using (hs z).hasSum
  have hall := htail.zero_add
  simpa only [u, iteratedDeriv_zero, zero_mul, zero_div, zero_add,
    infiniteDifferentialApply] using hall.tsum_eq

end Complex
