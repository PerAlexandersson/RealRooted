/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

import RealRooted.Jacobi.MomentPolynomial

public import RealRooted.SimpleRoots

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowWeightedOrthogonal

public import RealRooted.Jacobi.Orthogonality.Integral

import RealRooted.RiemannHypothesis.PrimeWindowJacobiPolynomial
import RealRooted.Jacobi.MomentStability
import Mathlib.Tactic.Linarith
import RealRooted.RiemannHypothesis.PrimeWindowJacobi

/-!
# Strict interlacing between independent prime windows under RH

RH supplies convergence of the weighted prime moments to one fixed Jacobi
moment sequence. Unconditional stability then gives strict root separation
between independently moving prime windows and between a prime window and the
fixed reference polynomial. Every nontrivial real pencil is simple and split.

The two window centers need only tend to infinity: no relative order or
disjointness is assumed. Degrees are fixed, and degree zero is included. These
are asymptotic cross-family conclusions; ordinary orthogonal-polynomial
real-rootedness for one positive measure is an unconditional fact.
All root comparisons use the common normalized window coordinate `(p - X) / H`.
-/

public section

open Filter Topology Polynomial

namespace RiemannHypothesis

/-- Under RH, independent prime-window centers tending to infinity give
genuine adjacent-degree interlacing for the same fixed Jacobi reference weight.
The explicit no-common-root conclusion strengthens the repository's weak root
comparisons in `Interlaces`. -/
theorem eventually_interlaces_primeWindowWeightedPolynomial
    (hRH : RiemannHypothesis) {ι : Type*} {l : Filter ι} {A B : ι → ℝ}
    (hA : Tendsto A l atTop) (hB : Tendsto B l atTop)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    ∀ᶠ t in l,
      RealRooted.Interlaces
        (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
          (A t) (Real.sqrt (A t) * Real.log (A t) ^ 3) n)
        (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
          (B t) (Real.sqrt (B t) * Real.log (B t) ^ 3) (n + 1)) ∧
      ∀ x,
        (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
          (A t) (Real.sqrt (A t) * Real.log (A t) ^ 3) n).IsRoot x →
        ¬ (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
          (B t) (Real.sqrt (B t) * Real.log (B t) ^ 3) (n + 1)).IsRoot x := by
  exact RealRooted.eventually_interlaces_jacobi_moment_polynomials
    (α := α) (β := β) (n := n) (by linarith) (by linarith)
    (fun k _ ↦ (hRH.tendsto_primeWindowWeightedMoment_jacobi hα hβ k).comp hA)
    (fun k _ ↦ (hRH.tendsto_primeWindowWeightedMoment_jacobi hα hβ k).comp hB)

/-- One eventual threshold works for every nontrivial real pencil parameter
pair, even when the lower and higher polynomials come from independent windows. -/
theorem eventually_isSimpleRealRooted_primeWindow_pencil
    (hRH : RiemannHypothesis) {ι : Type*} {l : Filter ι} {A B : ι → ℝ}
    (hA : Tendsto A l atTop) (hB : Tendsto B l atTop)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    ∀ᶠ t in l, ∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 →
      RealRooted.IsSimpleRealRooted
        (C a * Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
            (A t) (Real.sqrt (A t) * Real.log (A t) ^ 3) n +
          C b * Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
            (B t) (Real.sqrt (B t) * Real.log (B t) ^ 3) (n + 1)) := by
  exact RealRooted.eventually_isSimpleRealRooted_jacobi_moment_pencil
    (α := α) (β := β) (n := n) (by linarith) (by linarith)
    (fun k _ ↦ (hRH.tendsto_primeWindowWeightedMoment_jacobi hα hβ k).comp hA)
    (fun k _ ↦ (hRH.tendsto_primeWindowWeightedMoment_jacobi hα hβ k).comp hB)

/-- The degree-`n` prime polynomial eventually lies strictly between the roots
of the fixed degree-`n+1` monic Jacobi reference, under RH. -/
theorem eventually_interlaces_primeWindow_jacobi
    (hRH : RiemannHypothesis) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      RealRooted.Interlaces
        (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3) n)
        (shiftedJacobiMonic (n + 1) α β) ∧
      ∀ x,
        (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3) n).IsRoot x →
        ¬ (shiftedJacobiMonic (n + 1) α β).IsRoot x := by
  have h := RealRooted.eventually_interlaces_jacobi_moment_polynomials
    (μ := fun X : ℝ ↦ Chebyshev.primeWindowWeightedMoment
      (RealRooted.shiftedJacobiWeight α β) X (Real.sqrt X * Real.log X ^ 3))
    (ν := fun _ : ℝ ↦ RealRooted.shiftedJacobiMoment α β)
    (α := α) (β := β) (n := n) (by linarith) (by linarith)
    (fun k _ ↦ hRH.tendsto_primeWindowWeightedMoment_jacobi hα hβ k)
    (fun _ _ ↦ tendsto_const_nhds)
  simpa only [Chebyshev.primeWindowWeightedPolynomial,
    ← RealRooted.shiftedJacobiMonic_eq_monicMomentPolynomial (n + 1)
      (by linarith : -1 < α) (by linarith : -1 < β)] using h

/-- The fixed degree-`n` Jacobi reference eventually lies strictly between
the roots of the degree-`n+1` weighted prime polynomial, under RH. -/
theorem eventually_interlaces_jacobi_primeWindow
    (hRH : RiemannHypothesis) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      RealRooted.Interlaces (shiftedJacobiMonic n α β)
        (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3) (n + 1)) ∧
      ∀ x, (shiftedJacobiMonic n α β).IsRoot x →
        ¬ (Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
          X (Real.sqrt X * Real.log X ^ 3) (n + 1)).IsRoot x := by
  have h := RealRooted.eventually_interlaces_jacobi_moment_polynomials
    (μ := fun _ : ℝ ↦ RealRooted.shiftedJacobiMoment α β)
    (ν := fun X : ℝ ↦ Chebyshev.primeWindowWeightedMoment
      (RealRooted.shiftedJacobiWeight α β) X (Real.sqrt X * Real.log X ^ 3))
    (α := α) (β := β) (n := n) (by linarith) (by linarith)
    (fun _ _ ↦ tendsto_const_nhds)
    (fun k _ ↦ hRH.tendsto_primeWindowWeightedMoment_jacobi hα hβ k)
  simpa only [Chebyshev.primeWindowWeightedPolynomial,
    ← RealRooted.shiftedJacobiMonic_eq_monicMomentPolynomial n
      (by linarith : -1 < α) (by linarith : -1 < β)] using h

/-- RH yields simple real-rooted pencils between a weighted prime polynomial
and the fixed next-degree Jacobi reference, uniformly in all real coefficients. -/
theorem eventually_isSimpleRealRooted_primeWindow_jacobi_pencil
    (hRH : RiemannHypothesis) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 →
      RealRooted.IsSimpleRealRooted
        (C a * Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
            X (Real.sqrt X * Real.log X ^ 3) n +
          C b * shiftedJacobiMonic (n + 1) α β) := by
  have h := RealRooted.eventually_isSimpleRealRooted_jacobi_moment_pencil
    (μ := fun X : ℝ ↦ Chebyshev.primeWindowWeightedMoment
      (RealRooted.shiftedJacobiWeight α β) X (Real.sqrt X * Real.log X ^ 3))
    (ν := fun _ : ℝ ↦ RealRooted.shiftedJacobiMoment α β)
    (α := α) (β := β) (n := n) (by linarith) (by linarith)
    (fun k _ ↦ hRH.tendsto_primeWindowWeightedMoment_jacobi hα hβ k)
    (fun _ _ ↦ tendsto_const_nhds)
  simpa only [Chebyshev.primeWindowWeightedPolynomial,
    ← RealRooted.shiftedJacobiMonic_eq_monicMomentPolynomial (n + 1)
      (by linarith : -1 < α) (by linarith : -1 < β)] using h

/-- RH also yields simple real-rooted pencils with the fixed Jacobi reference
in the lower degree and the prime-window polynomial in the higher degree. -/
theorem eventually_isSimpleRealRooted_jacobi_primeWindow_pencil
    (hRH : RiemannHypothesis) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 →
      RealRooted.IsSimpleRealRooted
        (C a * shiftedJacobiMonic n α β +
          C b * Chebyshev.primeWindowWeightedPolynomial (RealRooted.shiftedJacobiWeight α β)
            X (Real.sqrt X * Real.log X ^ 3) (n + 1)) := by
  have h := RealRooted.eventually_isSimpleRealRooted_jacobi_moment_pencil
    (μ := fun _ : ℝ ↦ RealRooted.shiftedJacobiMoment α β)
    (ν := fun X : ℝ ↦ Chebyshev.primeWindowWeightedMoment
      (RealRooted.shiftedJacobiWeight α β) X (Real.sqrt X * Real.log X ^ 3))
    (α := α) (β := β) (n := n) (by linarith) (by linarith)
    (fun _ _ ↦ tendsto_const_nhds)
    (fun k _ ↦ hRH.tendsto_primeWindowWeightedMoment_jacobi hα hβ k)
  simpa only [Chebyshev.primeWindowWeightedPolynomial,
    ← RealRooted.shiftedJacobiMonic_eq_monicMomentPolynomial n
      (by linarith : -1 < α) (by linarith : -1 < β)] using h

/-- The independent-window conclusion specializes to the original unweighted
reference family, whose limiting polynomials are monic shifted Legendre polynomials. -/
theorem eventually_interlaces_primeWindowPolynomial
    (hRH : RiemannHypothesis) {ι : Type*} {l : Filter ι} {A B : ι → ℝ}
    (hA : Tendsto A l atTop) (hB : Tendsto B l atTop) (n : ℕ) :
    ∀ᶠ t in l,
      RealRooted.Interlaces
        (Chebyshev.primeWindowPolynomial (A t) (Real.sqrt (A t) * Real.log (A t) ^ 3) n)
        (Chebyshev.primeWindowPolynomial (B t) (Real.sqrt (B t) * Real.log (B t) ^ 3)
          (n + 1)) ∧
      ∀ x,
        (Chebyshev.primeWindowPolynomial
          (A t) (Real.sqrt (A t) * Real.log (A t) ^ 3) n).IsRoot x →
        ¬ (Chebyshev.primeWindowPolynomial (B t) (Real.sqrt (B t) * Real.log (B t) ^ 3)
          (n + 1)).IsRoot x := by
  simpa only [RealRooted.shiftedJacobiWeight_zero_zero,
    Chebyshev.primeWindowWeightedPolynomial_one] using
    hRH.eventually_interlaces_primeWindowWeightedPolynomial hA hB
      (α := 0) (β := 0) le_rfl le_rfl n

/-- All nontrivial real combinations of consecutive degrees from two independent
unweighted prime windows eventually have simple real roots under RH. -/
theorem eventually_isSimpleRealRooted_primeWindowPolynomial_pencil
    (hRH : RiemannHypothesis) {ι : Type*} {l : Filter ι} {A B : ι → ℝ}
    (hA : Tendsto A l atTop) (hB : Tendsto B l atTop) (n : ℕ) :
    ∀ᶠ t in l, ∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 →
      RealRooted.IsSimpleRealRooted
        (C a * Chebyshev.primeWindowPolynomial
            (A t) (Real.sqrt (A t) * Real.log (A t) ^ 3) n +
          C b * Chebyshev.primeWindowPolynomial
            (B t) (Real.sqrt (B t) * Real.log (B t) ^ 3) (n + 1)) := by
  simpa only [RealRooted.shiftedJacobiWeight_zero_zero,
    Chebyshev.primeWindowWeightedPolynomial_one] using
    hRH.eventually_isSimpleRealRooted_primeWindow_pencil hA hB
      (α := 0) (β := 0) le_rfl le_rfl n

end RiemannHypothesis
