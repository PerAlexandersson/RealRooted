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
import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowQuadrature
import RealRooted.Jacobi.Orthogonality.Integral
import RealRooted.RiemannHypothesis.PrimeWindowRoots
import RealRooted.RiemannHypothesis.PrimeWindowPolynomial
import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowMoments
import RealRooted.Mathlib.LinearAlgebra.Lagrange.QuadraturePerturbation
import RealRooted.Jacobi.GaussianQuadrature
import RealRooted.Jacobi.MomentPolynomial

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

private theorem eventually_primeWindow_weight_sub_le
    (hRH : RiemannHypothesis) {n : ℕ} {r : Fin n → ℝ} {s : ℝ → Fin n → ℝ}
    (hr : Function.Injective r)
    (hs : ∀ i, Tendsto (fun X : ℝ ↦ s X i) atTop (𝓝 (r i)))
    {A : ℝ} (hA : 0 < A)
    (hnode : ∀ᶠ X : ℝ in atTop, ∀ i, |s X i - r i| ≤ A / Real.log X) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ i,
      |Lagrange.quadratureWeight
          (momentFunctionalLinearMap
            (Chebyshev.primeWindowMoment X (Real.sqrt X * Real.log X ^ 3))) (s X) i -
        Lagrange.quadratureWeight
          (momentFunctionalLinearMap (RealRooted.shiftedJacobiMoment 0 0)) r i| ≤
        C / Real.log X := by
  obtain ⟨M, hM, hweights⟩ := Lagrange.eventually_abs_quadratureWeight_sub_le
    (momentFunctionalLinearMap (RealRooted.shiftedJacobiMoment 0 0)) hr hs
  obtain ⟨B, hB, hmom⟩ := hRH.eventually_primeWindowMoment_sub_le
  refine ⟨M * (A + B), mul_pos hM (add_pos hA hB), ?_⟩
  filter_upwards [hweights, hnode, hmom, eventually_gt_atTop (1 : ℝ)]
    with X hweight hn hm hX i
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hδ : 0 ≤ (A + B) / Real.log X := (div_pos (add_pos hA hB) hlog).le
  have hn' : ∀ j, |s X j - r j| ≤ (A + B) / Real.log X := by
    intro j
    exact (hn j).trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right hB.le) hlog.le)
  have hm' : ∀ j : Fin n,
      |momentFunctionalLinearMap
          (Chebyshev.primeWindowMoment X (Real.sqrt X * Real.log X ^ 3)) (Polynomial.X ^ j.val) -
        momentFunctionalLinearMap (RealRooted.shiftedJacobiMoment 0 0)
          (Polynomial.X ^ j.val)| ≤ (A + B) / Real.log X := by
    intro j
    simp only [momentFunctionalLinearMap_apply, momentFunctional_X_pow,
      RealRooted.shiftedJacobiMoment_zero_zero]
    exact (hm j.val).trans
      (div_le_div_of_nonneg_right (le_add_of_nonneg_left hA.le) hlog.le)
  have h := hweight.2
    (momentFunctionalLinearMap
      (Chebyshev.primeWindowMoment X (Real.sqrt X * Real.log X ^ 3)))
    ((A + B) / Real.log X) hδ hn' hm' i
  simpa only [mul_div_assoc] using h

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
  dsimp only
  let H : ℝ → ℝ := fun X ↦ Real.sqrt X * Real.log X ^ 3
  let L : ℝ → ℝ[X] →ₗ[ℝ] ℝ :=
    fun X ↦ momentFunctionalLinearMap (Chebyshev.primeWindowMoment X (H X))
  let L₀ : ℝ[X] →ₗ[ℝ] ℝ :=
    momentFunctionalLinearMap (RealRooted.shiftedJacobiMoment 0 0)
  obtain ⟨r, s, A, hA, hr, href, hroots, hslim⟩ :=
    hRH.exists_primeWindowPolynomial_roots_tendsto n
  have hnode : ∀ᶠ X : ℝ in atTop, ∀ i, |s X i - r i| ≤ A / Real.log X :=
    hroots.mono fun _ h ↦ h.2.2.2.2
  obtain ⟨C, hC, hweightbound⟩ :=
    eventually_primeWindow_weight_sub_le hRH hr.injective hslim hA hnode
  have hLm : ∀ i : Fin n, Tendsto (fun X : ℝ ↦ L X (Polynomial.X ^ i.val)) atTop
      (𝓝 (L₀ (Polynomial.X ^ i.val))) := by
    intro i
    simpa only [L, L₀, H, momentFunctionalLinearMap_apply, momentFunctional_X_pow,
      RealRooted.shiftedJacobiMoment_zero_zero] using hRH.tendsto_primeWindowMoment i.val
  have hwlim : Tendsto (fun X : ℝ ↦ Lagrange.quadratureWeight (L X) (s X)) atTop
      (𝓝 (Lagrange.quadratureWeight L₀ r)) :=
    Lagrange.tendsto_quadratureWeight hr.injective hslim hLm
  refine ⟨r, s, A + C, add_pos hA hC, hr, href, ?_, ?_, ?_, ?_⟩
  · intro i
    exact RealRooted.shiftedJacobiMonic_quadratureWeight_pos
      (by norm_num) (by norm_num) r hr.injective href i
  · intro p hp
    have h := RealRooted.shiftedJacobiMonic_quadrature_integral
      (by norm_num : (-1 : ℝ) < 0) (by norm_num : (-1 : ℝ) < 0) r hr.injective href hp
    simpa only [RealRooted.shiftedJacobiIntegrand, RealRooted.shiftedJacobiWeight,
      Real.rpow_zero, one_mul, mul_one] using h
  · filter_upwards [hroots, hRH.eventually_primeWindowMoment_hankel_posDef n, hweightbound,
      eventually_gt_atTop (1 : ℝ)] with X hroot hpos hweight hX
    have hsmono := hroot.2.2.1
    have hsroot := hroot.2.2.2.1
    have hlog : 0 ≤ Real.log X := (Real.log_pos hX).le
    refine ⟨hsmono, hsroot, ?_, ?_, ?_, ?_⟩
    · intro i
      exact Chebyshev.primeWindow_quadratureWeight_pos
        X (H X) hpos (s X) hsmono.injective hsroot i
    · intro p hp
      exact Chebyshev.primeWindow_quadrature_exact X (H X)
        (isUnit_iff_ne_zero.mpr hpos.det_pos.ne') (s X) hsmono.injective hsroot hp
    · intro i
      exact (hroot.2.2.2.2 i).trans
        (div_le_div_of_nonneg_right (le_add_of_nonneg_right hC.le) hlog)
    · intro i
      exact (hweight i).trans
        (div_le_div_of_nonneg_right (le_add_of_nonneg_left hA.le) hlog)
  · intro i
    exact ⟨hslim i, tendsto_pi_nhds.mp hwlim i⟩

end RiemannHypothesis
