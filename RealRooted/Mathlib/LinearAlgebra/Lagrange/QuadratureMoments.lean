/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.LinearAlgebra.Lagrange.Quadrature
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Moment equations for Lagrange quadrature weights

The existing Lagrange weights integrate every polynomial of degree below the
number of distinct nodes. Consequently they solve the transposed Vandermonde
moment system. These statements require neither positivity nor orthogonality.
-/

public section

open Finset Polynomial Matrix

namespace Matrix

/-- Distinct nodes make the transposed Vandermonde moment matrix invertible. -/
theorem isUnit_det_transpose_vandermonde {K : Type*} [Field K] {n : ℕ} {x : Fin n → K}
    (hx : Function.Injective x) : IsUnit ((vandermonde x)ᵀ).det := by
  rw [det_transpose, isUnit_iff_ne_zero]
  exact det_vandermonde_ne_zero_iff.mpr hx

end Matrix

namespace Lagrange

/-- Lagrange quadrature is exact below the number of distinct nodes. The
degree formulation includes the empty rule, which is exact on the zero polynomial. -/
theorem quadrature_exact_of_degree_lt {n : ℕ}
    (L : ℝ[X] →ₗ[ℝ] ℝ) (x : Fin n → ℝ) (hx : Function.Injective x)
    {p : ℝ[X]} (hp : p.degree < (n : WithBot ℕ)) :
    L p = ∑ i : Fin n, quadratureWeight L x i * p.eval (x i) := by
  have hinterp : p = Lagrange.interpolate univ x (fun i ↦ p.eval (x i)) := by
    apply Lagrange.eq_interpolate hx.injOn
    simpa only [card_univ, Fintype.card_fin] using hp
  calc
    L p = L (Lagrange.interpolate univ x (fun i ↦ p.eval (x i))) := congrArg L hinterp
    _ = ∑ i : Fin n, quadratureWeight L x i * p.eval (x i) := by
      rw [Lagrange.interpolate_apply, map_sum]
      apply sum_congr rfl
      intro i _
      rw [← smul_eq_C_mul, map_smul]
      simp only [smul_eq_mul, quadratureWeight]
      ring

/-- Lagrange weights solve the first `n` moment equations. -/
theorem transpose_vandermonde_mulVec_quadratureWeight {n : ℕ}
    (L : ℝ[X] →ₗ[ℝ] ℝ) (x : Fin n → ℝ) (hx : Function.Injective x) :
    (vandermonde x)ᵀ *ᵥ quadratureWeight L x = fun i : Fin n ↦ L (X ^ i.val) := by
  funext i
  change (∑ j : Fin n, x j ^ i.val * quadratureWeight L x j) = L (X ^ i.val)
  symm
  have hdeg : (X ^ i.val : ℝ[X]).degree < (n : WithBot ℕ) := by
    rw [degree_X_pow]
    exact_mod_cast i.is_lt
  simpa only [eval_pow, eval_X, mul_comm] using
    quadrature_exact_of_degree_lt L x hx hdeg

/-- The existing Lagrange weights are the inverse Vandermonde moment solve. -/
theorem quadratureWeight_eq_inv_mulVec {n : ℕ}
    (L : ℝ[X] →ₗ[ℝ] ℝ) (x : Fin n → ℝ) (hx : Function.Injective x) :
    quadratureWeight L x = ((vandermonde x)ᵀ)⁻¹ *ᵥ
      (fun i : Fin n ↦ L (X ^ i.val)) := by
  symm
  rw [← transpose_vandermonde_mulVec_quadratureWeight L x hx,
    mulVec_mulVec, nonsing_inv_mul _ (isUnit_det_transpose_vandermonde hx), one_mulVec]

end Lagrange
