import RealRooted.CubicDiscriminant
import RealRooted.Tactic.Finish

/-!
# Cubic-discriminant tactic frontends

Thin wrappers for the checked quadratic and cubic discriminant split criteria.
-/

open Lean.Elab.Tactic

namespace RealRooted
namespace Tactic

syntax (name := rr_quadratic_splits_discriminant_named)
  "rr_quadratic_splits_discriminant" " using "
    "degree" ":=" term ","
    "discriminant" ":=" term :
  tactic

syntax (name := rr_cubic_splits_discriminant_named)
  "rr_cubic_splits_discriminant" " using "
    "degree" ":=" term ","
    "discriminant" ":=" term :
  tactic

syntax (name := rr_natDegree_le_three_splits_discriminant_named)
  "rr_natDegree_le_three_splits_discriminant" " using "
    "degree" ":=" term ","
    "discriminant" ":=" term :
  tactic

syntax (name := rr_cubic_discriminant_iff_splits_named)
  "rr_cubic_discriminant_iff_splits" " using "
    "degree" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_quadratic_splits_discriminant using
        degree := $hdeg:term,
        discriminant := $hdisc:term) =>
      `(tactic| exact RealRooted.quadratic_splits_of_discrim_nonneg $hdeg $hdisc)
  | `(tactic|
      rr_cubic_splits_discriminant using
        degree := $hdeg:term,
        discriminant := $hdisc:term) =>
      `(tactic| exact RealRooted.splits_of_cubicDiscr_nonneg $hdeg $hdisc)
  | `(tactic|
      rr_natDegree_le_three_splits_discriminant using
        degree := $hdeg:term,
        discriminant := $hdisc:term) =>
      `(tactic|
        exact RealRooted.splits_of_natDegree_le_three_cubicDiscr_nonneg
          $hdeg $hdisc)
  | `(tactic|
      rr_cubic_discriminant_iff_splits using
        degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.cubicDiscr_nonneg_iff_splits_of_natDegree_le_three
          $hdeg)

end Tactic
end RealRooted
