/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowOrthogonal
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi
import Mathlib.Topology.Instances.Real.Lemmas
import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowMoments
import RealRooted.Mathlib.Analysis.Asymptotics.IncrementBounds
import RealRooted.Jacobi.MomentPolynomial
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Perturbation
import Mathlib.Algebra.Order.Star.Real
import RealRooted.RiemannHypothesis.PrimeWindowJacobiPolynomialBounds

/-!
# Prime-window orthogonal polynomials approaching shifted Legendre polynomials

Under Mathlib's RH, the finite logarithmically weighted prime windows of length
`sqrt X * log X ^ 3` have eventually positive definite moment matrices in every
fixed degree. Their monic orthogonal polynomials converge coefficientwise to
the monic shifted Legendre polynomial, with error `O(1 / log X)`.
-/

public section

open Filter Topology Polynomial

namespace RiemannHypothesis

private theorem tendsto_primeWindowMoment_uniform (hRH : RiemannHypothesis) (k : ℕ) :
    Tendsto (fun X : ℝ ↦
      Chebyshev.primeWindowMoment X (Real.sqrt X * Real.log X ^ 3) k)
      atTop (𝓝 (RealRooted.shiftedJacobiMoment 0 0 k)) := by
  simpa only [RealRooted.shiftedJacobiMoment_zero_zero] using hRH.tendsto_primeWindowMoment k

private theorem uniform_hankel_isUnit (n : ℕ) :
    IsUnit (momentHankelMatrix (RealRooted.shiftedJacobiMoment 0 0) n).det :=
  isUnit_iff_ne_zero.mpr
    (RealRooted.shiftedJacobiMoment_hankel_posDef n (by norm_num) (by norm_num)).det_pos.ne'

/-- RH gives eventual nonsingularity of every fixed finite prime-window
moment matrix. The assertion does not apply to arbitrary small or empty windows. -/
theorem eventually_primeWindowMoment_hankel_isUnit (hRH : RiemannHypothesis) (n : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      IsUnit (momentHankelMatrix
        (Chebyshev.primeWindowMoment X (Real.sqrt X * Real.log X ^ 3)) n).det := by
  obtain ⟨_, _, hbound⟩ := eventually_isUnit_momentHankelMatrix_det_and_inv_bound
    (n := n) (fun k _ ↦ tendsto_primeWindowMoment_uniform hRH k) (uniform_hankel_isUnit n)
  exact hbound.mono fun _ h ↦ h.1

/-- Actual nonnegative prime weights and eventual nonsingularity give positive
definite prime-window Hankel matrices in every fixed degree under RH. -/
theorem eventually_primeWindowMoment_hankel_posDef (hRH : RiemannHypothesis) (n : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      (momentHankelMatrix
        (Chebyshev.primeWindowMoment X (Real.sqrt X * Real.log X ^ 3)) n).PosDef := by
  filter_upwards [hRH.eventually_primeWindowMoment_hankel_isUnit n,
    Real.eventually_sqrt_mul_log_cube_pos_le] with X hdet hH
  exact (Chebyshev.primeWindowMoment_hankel_posSemidef hH.1 n).posDef_iff_det_ne_zero.mpr
    (isUnit_iff_ne_zero.mp hdet)

/-- Under RH, the constructed prime-window polynomial is eventually
orthogonal in the original finite weighted prime sum to every lower-degree polynomial. -/
theorem eventually_primeWindowPolynomial_orthogonal (hRH : RiemannHypothesis) (n : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ p : ℝ[X], p.degree < n →
      (∑ a ∈ Chebyshev.primeWindow X (Real.sqrt X * Real.log X ^ 3),
        (Real.log a / (Real.sqrt X * Real.log X ^ 3)) *
          p.eval (((a : ℝ) - X) / (Real.sqrt X * Real.log X ^ 3)) *
          (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).eval
            (((a : ℝ) - X) / (Real.sqrt X * Real.log X ^ 3))) = 0 := by
  filter_upwards [hRH.eventually_primeWindowMoment_hankel_isUnit n] with X hdet p hp
  exact Chebyshev.sum_primeWindowPolynomial_mul_eval_eq_zero _ _ n hdet hp

/-- Every coefficient of the fixed-degree prime-window polynomial tends to
the corresponding monic shifted Legendre coefficient under RH. -/
theorem tendsto_coeff_primeWindowPolynomial (hRH : RiemannHypothesis) (n k : ℕ) :
    Tendsto (fun X : ℝ ↦
      (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).coeff k)
      atTop (𝓝 ((shiftedJacobiMonic n 0 0).coeff k)) := by
  exact RealRooted.tendsto_coeff_monicMomentPolynomial_shiftedJacobi
    (by norm_num) (by norm_num) (fun j _ ↦ tendsto_primeWindowMoment_uniform hRH j) k

/-- RH gives a common `O(1 / log X)` error bound for all coefficients of each
fixed-degree prime-window polynomial relative to the monic shifted Legendre polynomial. -/
theorem eventually_coeff_primeWindowPolynomial_sub_le
    (hRH : RiemannHypothesis) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop, ∀ k : ℕ,
      |(Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).coeff k -
          (shiftedJacobiMonic n 0 0).coeff k| ≤ C / Real.log X := by
  simpa only [RealRooted.shiftedJacobiWeight_zero_zero,
    Chebyshev.primeWindowWeightedPolynomial_one] using
      hRH.eventually_coeff_primeWindowWeightedPolynomial_sub_le
        (α := 0) (β := 0) (by norm_num) (by norm_num) n

end RiemannHypothesis
