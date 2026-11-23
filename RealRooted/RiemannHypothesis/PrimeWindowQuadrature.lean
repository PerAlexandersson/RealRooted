/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.LinearAlgebra.Lagrange.Quadrature

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowOrthogonal

public import RealRooted.Jacobi.Orthogonality

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import RealRooted.Jacobi.Orthogonality.Integral
import RealRooted.RiemannHypothesis.PrimeWindowJacobiQuadrature

/-!
# Prime-window Gaussian quadrature approaching Gauss-Legendre quadrature

Under Mathlib's RH, every fixed-degree prime-window rule is eventually a positive
Gaussian rule for the original finite weighted prime sum. Its nodes and weights
converge to the Gauss-Legendre rule on `[0, 1]`; nodes and weights have error
`O(1 / log X)`. Exactness is proved for every polynomial of degree below `2 * n`.
The empty rule and the one-node rule are included without extra degree restrictions.
-/

public section

open Filter Topology Polynomial

namespace RiemannHypothesis

/-- RH gives actual positive Gaussian rules for prime windows, converging to
the actual Gauss-Legendre rule. The rules are exact below degree `2 * n`, and
their nodes and weights have a fixed-degree `O(1 / log X)` error. No quadrature, positivity,
or reference exactness premise is supplied by the caller. -/
theorem exists_primeWindow_gaussian_quadrature (hRH : RiemannHypothesis) (n : ℕ) :
    let H : ℝ → ℝ := fun X ↦ Real.sqrt X * Real.log X ^ 3
    let L : ℝ → ℝ[X] →ₗ[ℝ] ℝ :=
      fun X ↦ momentFunctionalLinearMap (Chebyshev.primeWindowMoment X (H X))
    let L₀ : ℝ[X] →ₗ[ℝ] ℝ :=
      momentFunctionalLinearMap (RealRooted.shiftedJacobiMoment 0 0)
    ∃ (r : Fin n → ℝ) (s : ℝ → Fin n → ℝ) (C : ℝ), 0 < C ∧ StrictMono r ∧
      (∀ i, (shiftedJacobiMonic n 0 0).IsRoot (r i)) ∧
      (∀ i, 0 < Lagrange.quadratureWeight L₀ r i) ∧
      (∀ p : ℝ[X], p.degree < (2 * n : ℕ) →
        (∫ t : ℝ in 0..1, p.eval t) =
          ∑ i : Fin n, Lagrange.quadratureWeight L₀ r i * p.eval (r i)) ∧
      (∀ᶠ X : ℝ in atTop, StrictMono (s X) ∧
        (∀ i, (Chebyshev.primeWindowPolynomial X (H X) n).IsRoot (s X i)) ∧
        (∀ i, 0 < Lagrange.quadratureWeight (L X) (s X) i) ∧
        (∀ p : ℝ[X], p.degree < (2 * n : ℕ) →
          (∑ a ∈ Chebyshev.primeWindow X (H X),
            (Real.log a / H X) * p.eval (((a : ℝ) - X) / H X)) =
            ∑ i : Fin n, Lagrange.quadratureWeight (L X) (s X) i * p.eval (s X i)) ∧
        (∀ i, |s X i - r i| ≤ C / Real.log X) ∧
        ∀ i, |Lagrange.quadratureWeight (L X) (s X) i -
          Lagrange.quadratureWeight L₀ r i| ≤ C / Real.log X) ∧
      ∀ i, Tendsto (fun X : ℝ ↦ s X i) atTop (𝓝 (r i)) ∧
        Tendsto (fun X : ℝ ↦ Lagrange.quadratureWeight (L X) (s X) i) atTop
          (𝓝 (Lagrange.quadratureWeight L₀ r i)) := by
  simpa only [RealRooted.shiftedJacobiWeight_zero_zero,
    Chebyshev.primeWindowWeightedMoment_one, Chebyshev.primeWindowWeightedPolynomial_one,
    mul_one] using hRH.exists_primeWindow_jacobi_gaussian_quadrature
      (α := 0) (β := 0) (by norm_num) (by norm_num) n

end RiemannHypothesis
