/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Moment
public import RealRooted.Mathlib.LinearAlgebra.Lagrange.Quadrature
import RealRooted.Mathlib.LinearAlgebra.Lagrange.GaussianQuadrature

/-!
# Gaussian rules from a nonsingular finite moment system

The roots of the monic moment polynomial provide Gaussian nodes. Orthogonality
proves exactness below degree `2 * n`; positive definiteness of the finite
moment matrix proves positivity of the existing Lagrange quadrature weights.
-/

public section

open Polynomial Finset

namespace Polynomial

/-- A monic degree-`n` polynomial is the nodal polynomial of any `n` distinct roots. -/
theorem IsMonicOfDegree.eq_nodal {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} {p : R[X]} (hp : IsMonicOfDegree p n)
    {x : Fin n → R} (hx : Function.Injective x) (hroots : ∀ i, p.IsRoot (x i)) :
    p = Lagrange.nodal univ x := by
  apply eq_of_degree_le_of_eval_index_eq univ hx.injOn
  · simp only [degree_eq_natDegree hp.monic.ne_zero, hp.natDegree_eq,
      card_univ, Fintype.card_fin, le_refl]
  · simp only [degree_eq_natDegree hp.monic.ne_zero, hp.natDegree_eq,
      Lagrange.degree_nodal, card_univ, Fintype.card_fin]
  · rw [hp.leadingCoeff_eq,
      show (Lagrange.nodal univ x).leadingCoeff = 1 from Lagrange.nodal_monic]
  · intro i _
    rw [show p.eval (x i) = 0 from hroots i,
      Lagrange.eval_nodal_at_node (mem_univ i)]

/-- Positive definiteness of the finite Hankel matrix gives strict positivity
on every nonzero square of degree below its size. -/
theorem momentPairing_self_pos_of_hankel_posDef (μ : ℕ → ℝ) {n : ℕ}
    (hpos : (momentHankelMatrix μ n).PosDef) {p : ℝ[X]}
    (hp : p ≠ 0) (hdeg : p.degree < n) : 0 < momentPairing μ p p := by
  have hpdeg : p.natDegree < n := (natDegree_lt_iff_degree_lt hp).mpr hdeg
  have hpfn : ofFn n (toFn n p) = p := ofFn_comp_toFn_eq_id_of_natDegree_lt hpdeg
  have hv : toFn n p ≠ 0 := by
    intro hz
    apply hp
    rw [← hpfn, hz]
    simp
  have h : 0 < momentPairing μ (ofFn n (toFn n p)) (ofFn n (toFn n p)) := by
    rw [momentPairing_ofFn_ofFn]
    simpa only [Pi.star_apply, star_trivial] using hpos.dotProduct_mulVec_pos hv
  simpa only [hpfn] using h

/-- Orthogonality of the moment construction transfers to its actual nodal polynomial. -/
theorem momentFunctional_nodal_mul_eq_zero (μ : ℕ → ℝ) {n : ℕ}
    (hdet : IsUnit (momentHankelMatrix μ n).det) (x : Fin n → ℝ)
    (hx : Function.Injective x) (hroots : ∀ i, (monicMomentPolynomial μ n).IsRoot (x i))
    {g : ℝ[X]} (hg : g.degree < n) :
    momentFunctional μ (Lagrange.nodal univ x * g) = 0 := by
  rw [← (isMonicOfDegree_monicMomentPolynomial μ n).eq_nodal hx hroots]
  change momentPairing μ (monicMomentPolynomial μ n) g = 0
  rw [momentPairing_comm]
  exact momentPairing_monicMomentPolynomial μ n hdet hg

end Polynomial

namespace Lagrange

/-- Roots of the monic moment polynomial yield Gaussian exactness below
degree `2 * n`, without assuming a Gaussian rule in advance. -/
theorem quadrature_exact_monicMomentPolynomial (μ : ℕ → ℝ) {n : ℕ}
    (hdet : IsUnit (momentHankelMatrix μ n).det) (x : Fin n → ℝ)
    (hx : Function.Injective x) (hroots : ∀ i, (monicMomentPolynomial μ n).IsRoot (x i))
    {p : ℝ[X]} (hp : p.degree < (2 * n : ℕ)) :
    momentFunctional μ p =
      ∑ i : Fin n, quadratureWeight (momentFunctionalLinearMap μ) x i * p.eval (x i) := by
  exact quadrature_exact_of_orthogonal_nodal (momentFunctionalLinearMap μ) x hx
    (fun g hg ↦ momentFunctional_nodal_mul_eq_zero μ hdet x hx hroots hg) hp

/-- A positive definite finite moment system gives positive Gaussian weights
at the distinct roots of its monic orthogonal polynomial. -/
theorem quadratureWeight_pos_monicMomentPolynomial (μ : ℕ → ℝ) {n : ℕ}
    (hpos : (momentHankelMatrix μ n).PosDef) (x : Fin n → ℝ)
    (hx : Function.Injective x) (hroots : ∀ i, (monicMomentPolynomial μ n).IsRoot (x i))
    (i : Fin n) : 0 < quadratureWeight (momentFunctionalLinearMap μ) x i := by
  have hdet : IsUnit (momentHankelMatrix μ n).det := isUnit_iff_ne_zero.mpr hpos.det_pos.ne'
  exact quadratureWeight_pos_of_orthogonal_nodal (momentFunctionalLinearMap μ) x hx
    (fun g hg ↦ momentFunctional_nodal_mul_eq_zero μ hdet x hx hroots hg)
    (fun p hp hdeg ↦ momentPairing_self_pos_of_hankel_posDef μ hpos hp hdeg) i

end Lagrange
