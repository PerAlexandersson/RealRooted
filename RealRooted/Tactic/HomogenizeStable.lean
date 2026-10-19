import RealRooted.BorceaBranden.Applications.HomogenizeStable

/-!
# Stable homogenization tactic frontends

Thin certificate-driven wrappers around the proved stable homogenization
theorems.
-/

namespace RealRooted
namespace Tactic

/-- Closes `IsBivariateUpperStable (complexifyMv (homogenizeBivariate p.natDegree p))` from
`nonzero : p ≠ 0`, `splits : p.Splits` and `roots_nonpos : ∀ r ∈ p.roots, r ≤ 0`. -/
syntax (name := rr_homogenize_bivariate_stable_named)
  "rr_homogenize_bivariate_stable" " using "
    "nonzero" ":=" term ","
    "splits" ":=" term ","
    "roots_nonpos" ":=" term :
  tactic

/-- Closes `MvUpperHalfPlaneStableOrZero (complexifyMv (homogenizeBivariate p.natDegree p))`
from `splits : p.Splits` and `roots_nonpos : ∀ r ∈ p.roots, r ≤ 0`. -/
syntax (name := rr_homogenize_bivariate_stable_or_zero_named)
  "rr_homogenize_bivariate_stable_or_zero" " using "
    "splits" ":=" term ","
    "roots_nonpos" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_homogenize_bivariate_stable using
        nonzero := $hp0:term,
        splits := $hsplits:term,
        roots_nonpos := $hroots:term) =>
      `(tactic|
        exact
          RealRooted.BorceaBranden.homogenizeBivariate_stable_of_splits_nonpos
            $hp0 $hsplits $hroots)
  | `(tactic|
      rr_homogenize_bivariate_stable_or_zero using
        splits := $hsplits:term,
        roots_nonpos := $hroots:term) =>
      `(tactic|
        exact
          RealRooted.BorceaBranden.homogenizeBivariate_stableOrZero_of_splits_nonpos
            $hsplits $hroots)

end Tactic
end RealRooted
