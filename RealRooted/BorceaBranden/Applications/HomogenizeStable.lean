import RealRooted.Mathlib.Algebra.Polynomial.Homogenize
import RealRooted.Tactic.FiniteSymbolPF

/-!
# Stable homogenization of real-rooted polynomials

This module proves the nonzero form of the homogenization step used in finite-symbol arguments.
The zero polynomial must be excluded because strict upper-half-plane stability requires every
evaluation in the region to be nonzero.
-/

open Polynomial

namespace RealRooted.BorceaBranden

open Tactic.FiniteSymbolPF

/-- A nonzero split polynomial with nonpositive roots has stable bivariate homogenization. -/
theorem homogenizeBivariate_stable_of_splits_nonpos {p : Polynomial ℝ}
    (hp0 : p ≠ 0) (hpSplits : p.Splits) (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    IsBivariateUpperStable (complexifyMv (homogenizeBivariate p.natDegree p)) := by
  have hbridge :
      homogenizeBivariate p.natDegree p = p.homogenize p.natDegree := by
    unfold homogenizeBivariate Polynomial.homogenize
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro k hk
    simp [MvPolynomial.monomial_eq, mul_assoc]
  have hhomogenized := congrArg
    (fun q : Polynomial ℝ => q.homogenize p.natDegree)
    hpSplits.eq_prod_roots
  have hhom :
      complexifyMv (homogenizeBivariate p.natDegree p) =
        MvPolynomial.C (p.leadingCoeff : ℂ) *
          (p.roots.map (fun r : ℝ =>
            MvPolynomial.X 0 - MvPolynomial.C (r : ℂ) * MvPolynomial.X 1)).prod := by
    rw [hbridge, hhomogenized, Polynomial.homogenize_C_mul,
      hpSplits.natDegree_eq_card_roots, Polynomial.homogenize_rootFactorProduct]
    unfold complexifyMv
    rw [map_mul, map_multiset_prod]
    simp [Multiset.map_map]
  rw [hhom]
  apply (MvUpperHalfPlaneStable.nonposRootFactorProduct 0 1 p.roots hroots).C_mul
  exact_mod_cast Polynomial.leadingCoeff_ne_zero.mpr hp0

/-- A split polynomial with nonpositive roots has stable-or-zero bivariate homogenization. -/
theorem homogenizeBivariate_stableOrZero_of_splits_nonpos {p : Polynomial ℝ}
    (hpSplits : p.Splits) (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    MvUpperHalfPlaneStableOrZero
      (complexifyMv (homogenizeBivariate p.natDegree p)) := by
  by_cases hp0 : p = 0
  · subst p
    simpa [homogenizeBivariate, complexifyMv] using
      (MvUpperHalfPlaneStableOrZero.zero (sigma := Fin 2))
  · exact (homogenizeBivariate_stable_of_splits_nonpos hp0 hpSplits hroots).orZero

end RealRooted.BorceaBranden
