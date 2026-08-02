import RealRooted.Tactic.HomogenizeStable

open Polynomial

namespace RealRooted
namespace Tactic

example {p : ℝ[X]}
    (hp0 : p ≠ 0)
    (hsplits : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    IsBivariateUpperStable
      (complexifyMv (homogenizeBivariate p.natDegree p)) := by
  rr_homogenize_bivariate_stable using
    nonzero := hp0,
    splits := hsplits,
    roots_nonpos := hroots

example {p : ℝ[X]}
    (hsplits : p.Splits)
    (hroots : ∀ r ∈ p.roots, r ≤ 0) :
    MvUpperHalfPlaneStableOrZero
      (complexifyMv (homogenizeBivariate p.natDegree p)) := by
  rr_homogenize_bivariate_stable_or_zero using
    splits := hsplits,
    roots_nonpos := hroots

end Tactic
end RealRooted
