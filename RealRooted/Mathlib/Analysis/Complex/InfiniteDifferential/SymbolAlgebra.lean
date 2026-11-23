/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.OrderConvergence
import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.OrderDerivative
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.Derivative
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.EulerRodrigues

/-!
# Scalar and linear factors of infinite differential symbols

Multiplying an entire symbol by the variable differentiates its differential
image. The proof shifts an actually convergent series, so zero coefficients
and zero outputs cause no exception.
-/

public section

namespace Complex

/-- Scalar multiplication of an infinite differential symbol acts by the same
scalar on its output. This identity holds even for the totalized series. -/
theorem infiniteDifferentialApply_const_mul_symbol (c : ℂ) (φ f : ℂ → ℂ) :
    infiniteDifferentialApply (fun z => c * φ z) f =
      fun z => c * infiniteDifferentialApply φ f z := by
  ext z
  simp only [infiniteDifferentialApply, iteratedDeriv_const_mul_field]
  simp_rw [mul_assoc, mul_div_assoc]
  exact tsum_mul_left

/-- Addition of entire symbols is linear when both differential series satisfy
the reciprocal growth-order criterion. -/
theorem infiniteDifferentialApply_add_symbol {φ ψ f : ℂ → ℂ} {ρ σ p q : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ)
    (hψ : Differentiable ℂ ψ) (hoψ : TauCeti.OrderLE ψ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q)
    (hsum : 1 < p⁻¹ + q⁻¹) :
    infiniteDifferentialApply (fun z => φ z + ψ z) f =
      infiniteDifferentialApply φ f + infiniteDifferentialApply ψ f := by
  ext z
  have hleft := (summable_norm_infiniteDifferentialApply_of_order
    hφ hoφ hp hρ hf hof hq hσ hsum z).of_norm
  have hright := (summable_norm_infiniteDifferentialApply_of_order
    hψ hoψ hp hρ hf hof hq hσ hsum z).of_norm
  simp only [infiniteDifferentialApply, Pi.add_apply,
    iteratedDeriv_fun_add hφ.contDiff.contDiffAt hψ.contDiff.contDiffAt, add_mul, add_div]
  exact hleft.tsum_add hright

/-- Multiplying an entire symbol by the variable applies one more derivative
to the target. Only the unmultiplied symbol's growth bound is required. -/
theorem infiniteDifferentialApply_id_mul {φ f : ℂ → ℂ} {ρ σ p q : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q)
    (hsum : 1 < p⁻¹ + q⁻¹) :
    infiniteDifferentialApply (fun z => z * φ z) f =
      infiniteDifferentialApply φ (deriv f) := by
  ext z
  let u : ℕ → ℂ := fun n =>
    iteratedDeriv n (fun w => w * φ w) 0 * iteratedDeriv n f z / (n.factorial : ℂ)
  have hterm (n : ℕ) : u (n + 1) =
      iteratedDeriv n φ 0 * iteratedDeriv n (deriv f) z / (n.factorial : ℂ) := by
    dsimp only [u]
    rw [iteratedDeriv_succ_id_mul hφ.contDiff.contDiffAt]
    simp only [zero_mul, zero_add, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, ← iteratedDeriv_succ']
    have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hnf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    field_simp [hn, hnf]
  have hs := (summable_norm_infiniteDifferentialApply_of_order
    hφ hoφ hp hρ hf.deriv (hof.deriv hf) hq hσ hsum z).of_norm.hasSum
  have htail : HasSum (fun n => u (n + 1))
      (infiniteDifferentialApply φ (deriv f) z) := by
    simpa only [hterm, infiniteDifferentialApply] using hs
  have hall := htail.zero_add
  simpa only [u, iteratedDeriv_zero, zero_mul, zero_div, zero_add,
    infiniteDifferentialApply] using hall.tsum_eq

/-- A variable factor in the symbol differentiates the actual entire output. -/
theorem infiniteDifferentialApply_id_mul_eq_deriv {φ f : ℂ → ℂ} {ρ σ p q : ℝ}
    (hφ : Differentiable ℂ φ) (hoφ : TauCeti.OrderLE φ ρ) (hp : 0 < p) (hρ : ρ < p)
    (hf : Differentiable ℂ f) (hof : TauCeti.OrderLE f σ) (hq : 0 < q) (hσ : σ < q)
    (hsum : 1 < p⁻¹ + q⁻¹) :
    infiniteDifferentialApply (fun z => z * φ z) f =
      deriv (infiniteDifferentialApply φ f) := by
  rw [infiniteDifferentialApply_id_mul hφ hoφ hp hρ hf hof hq hσ hsum]
  simpa only [iteratedDeriv_one] using
    (iteratedDeriv_infiniteDifferentialApply_of_order
      hφ hoφ hp hρ hf hof hq hσ hsum 1).symm

end Complex
