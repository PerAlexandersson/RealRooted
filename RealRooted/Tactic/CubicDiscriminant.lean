module

public import RealRooted.CubicDiscriminant
public import RealRooted.Tactic.Finish

/-!
# Cubic-discriminant tactic frontends

Thin wrappers for the checked quadratic and cubic discriminant split criteria.
-/

@[expose] public section

open Lean.Elab.Tactic

namespace RealRooted
namespace Tactic

/-- Closes `p.Splits` from `degree : p.natDegree = 2` and `discriminant : 0 ≤ discrim (p.coeff
2) (p.coeff 1) (p.coeff 0)`. -/
syntax (name := rr_quadratic_splits_discriminant_named)
  "rr_quadratic_splits_discriminant" " using "
    "degree" ":=" term ","
    "discriminant" ":=" term :
  tactic

/-- Closes `p.Splits` from `degree : p.natDegree = 3` and `discriminant : 0 ≤ cubicDiscr p`. -/
syntax (name := rr_cubic_splits_discriminant_named)
  "rr_cubic_splits_discriminant" " using "
    "degree" ":=" term ","
    "discriminant" ":=" term :
  tactic

/-- Closes `p.Splits` from `degree : p.natDegree ≤ 3` and `discriminant : 0 ≤ cubicDiscr p`. -/
syntax (name := rr_natDegree_le_three_splits_discriminant_named)
  "rr_natDegree_le_three_splits_discriminant" " using "
    "degree" ":=" term ","
    "discriminant" ":=" term :
  tactic

/-- Closes `0 ≤ cubicDiscr p ↔ p.Splits` from `degree : p.natDegree ≤ 3`. -/
syntax (name := rr_cubic_discriminant_iff_splits_named)
  "rr_cubic_discriminant_iff_splits" " using "
    "degree" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_quadratic_splits_discriminant using
        degree := $hdeg:term,
        discriminant := $hdisc:term) =>
      `(tactic| exact RealRooted.splits_of_natDegree_eq_two_of_discrim_nonneg $hdeg $hdisc)
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
