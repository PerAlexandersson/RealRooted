import RealRooted.Basic
import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform

/-!
# Coefficientwise positivity for polynomial basis transforms

This module connects the coefficient-generic basis-transform API to the
real-polynomial coefficient-positivity predicate used by the real-rootedness
library.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A basis transform preserves coefficientwise nonnegativity when every
basis element has nonnegative coefficients. -/
theorem HasNonnegCoeffs.basisTransform {B : ℕ → ℝ[X]} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hB : ∀ k, HasNonnegCoeffs (B k)) :
    HasNonnegCoeffs (Polynomial.basisTransform B p) := by
  intro j
  rw [Polynomial.coeff_basisTransform]
  simpa only [Polynomial.sum] using
    Finset.sum_nonneg fun k _ => mul_nonneg (hp k) (hB k j)

end RealRooted
