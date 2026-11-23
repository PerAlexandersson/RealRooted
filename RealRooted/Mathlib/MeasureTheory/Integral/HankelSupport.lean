/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Moment
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.MeasureTheory.Integral.PolynomialMoment

/-!
# Strict Hankel positivity without a finite carrying set

A measure on the nonnegative half-line that is not carried by any finite
set makes every nonzero polynomial square, weighted by any natural power,
have strictly positive integral. This includes continuous and singular
measures, without requiring any atoms.
-/

public section

open Polynomial

namespace MeasureTheory

/-- A nonnegative measure not carried by a finite set gives a positive integral
to each nonzero polynomial square weighted by a natural power. -/
theorem integral_weighted_eval_sq_pos_of_no_finite_carrier
    {mu : Measure ℝ} (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu)
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    (hfinite : ∀ S : Set ℝ, S.Finite → mu Sᶜ ≠ 0)
    {p : ℝ[X]} (hp : p ≠ 0) (r : ℕ) :
    0 < ∫ x : ℝ, x ^ r * p.eval x ^ 2 ∂mu := by
  have hint : Integrable (fun x : ℝ => x ^ r * p.eval x ^ 2) mu := by
    apply (integrable_pow_mul_polynomial_eval hmom r (p ^ 2)).congr
    filter_upwards [] with x
    simp only [Polynomial.eval_pow]
  have hnonneg : ∀ᵐ x ∂mu, 0 ≤ x ^ r * p.eval x ^ 2 :=
    hpos.mono fun x hx => mul_nonneg (pow_nonneg hx r) (sq_nonneg _)
  apply lt_of_le_of_ne (integral_nonneg_of_ae hnonneg)
  intro hz
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hz.symm
  let S : Set ℝ := {0} ∪ {x | p.IsRoot x}
  have hS : S.Finite := (Set.finite_singleton 0).union (finite_setOfPred_isRoot hp)
  apply hfinite S hS
  apply ae_iff.mp
  filter_upwards [hzero] with x hx
  rcases mul_eq_zero.mp hx with hx | hx
  · exact Or.inl (by simpa only [Set.mem_singleton_iff] using eq_zero_of_pow_eq_zero hx)
  · exact Or.inr (eq_zero_of_pow_eq_zero hx)

/-- A nonnegative all-moments measure without a finite carrying set gives
positive definite Hankel matrices at every size and natural shift. -/
theorem posDef_integral_pow_hankel_of_no_finite_carrier
    {mu : Measure ℝ} (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu)
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    (hfinite : ∀ S : Set ℝ, S.Finite → mu Sᶜ ≠ 0) (n r : ℕ) :
    (momentHankelMatrix (fun k => ∫ x : ℝ, x ^ (k + r) ∂mu) n).PosDef := by
  apply momentHankelMatrix_posDef_of_pos
  intro p hp _
  rw [momentPairing, momentFunctional_integral_pow_add hmom]
  simpa only [Polynomial.eval_mul, pow_two] using
    integral_weighted_eval_sq_pos_of_no_finite_carrier hmom hpos hfinite hp r

end MeasureTheory
