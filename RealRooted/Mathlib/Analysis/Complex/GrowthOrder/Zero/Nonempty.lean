/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
import TauCeti.Analysis.Complex.GrowthOrder.Exponential

/-!
# A zero of a nonconstant entire function below order one

The zero-free finite-order factorization writes the function as the
exponential of a polynomial of degree at most the natural floor of its
order. Below order one that polynomial is constant. No reality or
real-zero assumption enters this argument.
-/

public section

namespace TauCeti

/-- A nonconstant entire function of order below one has a zero. -/
theorem OrderLE.exists_zero_of_nonconstant {f : ℂ → ℂ} {rho : ℝ}
    (horder : OrderLE f rho) (hrho : rho < 1) (hf : Differentiable ℂ f)
    (hnc : f ≠ fun _ : ℂ ↦ f 0) : ∃ z : ℂ, f z = 0 := by
  by_contra hno
  have hnz : ∀ z : ℂ, f z ≠ 0 := by simpa using hno
  obtain ⟨p, hp, heq⟩ := horder.exists_eq_cexp_polynomial_eval_of_forall_ne_zero hf hnz
  have hd : p.natDegree = 0 := by
    rw [Nat.floor_eq_zero.mpr hrho] at hp
    exact Nat.eq_zero_of_le_zero hp
  apply hnc
  funext z
  rw [heq z, heq 0, Polynomial.eq_C_of_natDegree_eq_zero hd]
  simp only [Polynomial.eval_C]

end TauCeti
