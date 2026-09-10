import RealRooted.Mathlib.Algebra.Polynomial.Homogenize
import RealRooted.MultivariateStability

/-!
# Stable homogenization of real-rooted polynomials

This module proves the nonzero form of the homogenization step used in finite-symbol arguments.
The zero polynomial must be excluded because strict upper-half-plane stability requires every
evaluation in the region to be nonzero.
-/

open Polynomial

namespace RealRooted.BorceaBranden

/-- The project's explicit bivariate homogenization agrees with Mathlib's
polynomial homogenization. -/
theorem homogenizeBivariate_eq_homogenize (d : ℕ) (p : Polynomial ℝ) :
    homogenizeBivariate d p = p.homogenize d := by
  unfold homogenizeBivariate Polynomial.homogenize
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  simp [MvPolynomial.monomial_eq, mul_assoc]

/-- A nonzero split polynomial with nonpositive roots has stable bivariate homogenization. -/
theorem homogenizeBivariate_stable_of_splits_nonpos {p : Polynomial ℝ}
    (hp0 : p ≠ 0) (hpSplits : p.Splits) (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    IsBivariateUpperStable (complexifyMv (homogenizeBivariate p.natDegree p)) := by
  have hhomogenized := congrArg
    (fun q : Polynomial ℝ => q.homogenize p.natDegree)
    hpSplits.eq_prod_roots
  have hhom :
      complexifyMv (homogenizeBivariate p.natDegree p) =
        MvPolynomial.C (p.leadingCoeff : ℂ) *
          (p.roots.map (fun r : ℝ =>
            MvPolynomial.X 0 - MvPolynomial.C (r : ℂ) * MvPolynomial.X 1)).prod := by
    rw [homogenizeBivariate_eq_homogenize, hhomogenized,
      Polynomial.homogenize_C_mul,
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

/-- Padding a nonzero split polynomial with nonpositive roots to any larger
homogeneous degree preserves strict bivariate stability. -/
theorem homogenize_stable_of_splits_nonpos_of_natDegree_le
    {p : Polynomial ℝ} {d : ℕ} (hdegree : p.natDegree ≤ d)
    (hp0 : p ≠ 0) (hpSplits : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    MvUpperHalfPlaneStable (complexifyMv (p.homogenize d)) := by
  rw [Polynomial.homogenize_eq_homogenize_natDegree_mul_X_one_pow hdegree]
  change MvUpperHalfPlaneStable
    (MvPolynomial.map Complex.ofRealHom
      (p.homogenize p.natDegree * MvPolynomial.X 1 ^ (d - p.natDegree)))
  rw [map_mul, map_pow, MvPolynomial.map_X]
  apply MvUpperHalfPlaneStable.mul
  · rw [← homogenizeBivariate_eq_homogenize]
    exact homogenizeBivariate_stable_of_splits_nonpos hp0 hpSplits hroots
  · intro z hz
    rw [MvPolynomial.eval_pow, MvPolynomial.eval_X]
    apply pow_ne_zero
    intro hz0
    have hz1 := hz 1
    simp [hz0] at hz1

/-- Padding a split polynomial with nonpositive roots to any larger homogeneous
degree preserves weak bivariate stability, including the zero polynomial. -/
theorem homogenize_stableOrZero_of_splits_nonpos_of_natDegree_le
    {p : Polynomial ℝ} {d : ℕ} (hdegree : p.natDegree ≤ d)
    (hpSplits : p.Splits) (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    MvUpperHalfPlaneStableOrZero (complexifyMv (p.homogenize d)) := by
  by_cases hp0 : p = 0
  · subst p
    simpa [complexifyMv] using
      (MvUpperHalfPlaneStableOrZero.zero (sigma := Fin 2))
  · exact (homogenize_stable_of_splits_nonpos_of_natDegree_le
      hdegree hp0 hpSplits hroots).orZero

end RealRooted.BorceaBranden
