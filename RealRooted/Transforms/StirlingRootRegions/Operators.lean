module

public import RealRooted.NarayanaTransformation.Basis
public import RealRooted.BorceaBranden.Applications.UnivariatePoissonStar
import RealRooted.Transforms.StirlingRootRegions
import Mathlib.Algebra.Polynomial.Module.AEval
import RealRooted.BorceaBranden.Applications.PoissonStarGeneral

/-!
# Polynomial functional calculus for the Touchard raising operator

For `N = X (1 + D)` we prove `g(N) p = (S g) ⋆ p`, so preservation of the PF cone
is equivalent to `S g` being PF. The sharp grouped-cubic region therefore also
classifies the corresponding cubic differential operators. Parameters can vary
at every step of a recurrence with any PF seed.

Source: the unpublished manuscript *Long OEIS proofs and grouped factors under
the Stirling transform* (2026), differential-operator section, issue #2134.
-/

public section

open Polynomial

namespace RealRooted

noncomputable section

/-- Polynomial functional calculus of `N = X (1 + D)` is Poisson multiplication
by the Touchard transform of the source polynomial. -/
theorem aeval_raising_eq_starC (g p : ℝ[X]) :
    aeval (Poisson.starCLinearMap 1 X) g p =
      Poisson.starC 1 (basisTransform touchard g) p := by
  have hX : basisTransform touchard X = X := by
    simpa only [pow_one, touchard_one] using basisTransform_X_pow touchard 1
  induction g using Polynomial.induction_on generalizing p with
  | C a =>
      simp only [aeval_C, Module.algebraMap_end_apply, smul_eq_C_mul,
        basisTransform_C, touchard_zero, mul_one]
      symm
      simpa only [mul_one, Poisson.starC_one_left] using
        Poisson.starC_C_mul_left 1 a 1 p
  | add g h hg hh =>
      simp only [map_add, LinearMap.add_apply, basisTransform_add,
        Poisson.starC_add_left, hg, hh]
  | monomial n a ih =>
      rw [show C a * X ^ (n + 1) = X * (C a * X ^ n) by ring,
        map_mul, aeval_X, mul_apply_eq_comp, ih,
        Poisson.starCLinearMap_apply, ← Poisson.starC_assoc]
      have hmul := basisTransform_touchard_mul X (C a * X ^ n)
      rw [hX] at hmul
      rw [← hmul]

/-- A polynomial in `N = X (1 + D)` preserves PF exactly when its Touchard image is PF. -/
theorem preservesPF_aeval_raising_iff (g : ℝ[X]) :
    (∀ p, IsPFPolynomial p →
      IsPFPolynomial (aeval (Poisson.starCLinearMap 1 X) g p)) ↔
        IsPFPolynomial (basisTransform touchard g) := by
  simp_rw [aeval_raising_eq_starC]
  exact Poisson.preservesPF_iff_of_nonneg zero_le_one _

/-- The sharp grouped-cubic region also exactly classifies the differential operator
`(N + b + 1/2) ((N + b)^2 + w)`, including the repeated-root boundaries. -/
theorem preservesPF_aeval_raising_half_shifted_cubic_iff {b w : ℝ} (hw : 0 ≤ w) :
    (∀ p, IsPFPolynomial p → IsPFPolynomial
      (aeval (Poisson.starCLinearMap 1 X)
        ((X + C (b + 1 / 2)) * ((X + C b) ^ 2 + C w)) p)) ↔
      -(1 / 2) ≤ b ∧ w ≤ 3 * b + 9 / 4 := by
  rw [preservesPF_aeval_raising_iff, isPFPolynomial_touchard_half_shifted_cubic_iff hw]

/-- Polynomials in the raising operator with PF Touchard images preserve PF in every
row of a recurrence. The source polynomial may vary with the row, and the seed is arbitrary. -/
theorem isPFPolynomial_aeval_raising_recurrence
    {g P : ℕ → ℝ[X]} (hseed : IsPFPolynomial (P 0))
    (hg : ∀ n, IsPFPolynomial (basisTransform touchard (g n)))
    (hrec : ∀ n, P (n + 1) = aeval (Poisson.starCLinearMap 1 X) (g n) (P n))
    (n : ℕ) : IsPFPolynomial (P n) := by
  induction n with
  | zero => exact hseed
  | succ n ih =>
      rw [hrec]
      exact (preservesPF_aeval_raising_iff (g n)).mpr (hg n) (P n) ih

end

end RealRooted
