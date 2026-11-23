/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.MomentAlgebra
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Formal series of normalized orthogonal moments
-/

public section

open scoped PowerSeries

namespace Polynomial

/-- The normalized moment-pairing series starting at the degree of the monic
orthogonal polynomial. Under positive Hankel forms its constant term is one. -/
@[expose] noncomputable def momentOrthogonalSeries (μ : ℕ → ℝ) (n : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.mk fun k =>
    momentPairing μ (X ^ (n + k)) (monicMomentPolynomial μ n) / momentNormSq μ n

/-- The coefficients of the normalized orthogonal-moment series. -/
@[simp] theorem coeff_momentOrthogonalSeries (μ : ℕ → ℝ) (n k : ℕ) :
    PowerSeries.coeff k (momentOrthogonalSeries μ n) =
      momentPairing μ (X ^ (n + k)) (monicMomentPolynomial μ n) / momentNormSq μ n := by
  simp only [momentOrthogonalSeries, PowerSeries.coeff_mk]

/-- Positive Hankel forms normalize each orthogonal-moment series to constant one. -/
theorem coeff_zero_momentOrthogonalSeries (μ : ℕ → ℝ)
    (hpos : ∀ n, (momentHankelMatrix μ n).PosDef) (n : ℕ) :
    PowerSeries.coeff 0 (momentOrthogonalSeries μ n) = 1 := by
  rw [coeff_momentOrthogonalSeries, Nat.add_zero,
    momentPairing_X_pow_monicMomentPolynomial_eq_norm μ n
      (isUnit_iff_ne_zero.mpr (hpos n).det_pos.ne'),
    div_self (momentNormSq_pos μ n (hpos (n + 1))).ne']

/-- The degree-zero member is the original moment series divided by its mass. -/
theorem coeff_momentOrthogonalSeries_zero (μ : ℕ → ℝ) (k : ℕ) :
    PowerSeries.coeff k (momentOrthogonalSeries μ 0) = μ k / μ 0 := by
  simp only [coeff_momentOrthogonalSeries, Nat.zero_add, monicMomentPolynomial_zero,
    momentNormSq_zero, momentPairing, mul_one, momentFunctional_X_pow]

end Polynomial
