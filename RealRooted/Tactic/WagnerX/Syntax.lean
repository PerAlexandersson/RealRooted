module

public import RealRooted.Tactic.WagnerX.TranslatedLag

/-!
# Wagner `X`-shift tactic syntax
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- Closes `StrictInterl g (X * f)` from `proper : StrictInterl f g`;
`left_nonneg : HasNonnegCoeffs f`; and `right_nonneg : HasNonnegCoeffs g`. -/
syntax (name := rr_strict_interl_mul_X)
  "rr_strict_interl_mul_X" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term :
  tactic

/-- Bare form of `rr_strict_interl_mul_X`: finds the three certificates in the local context by
`rr_lookup`, using `rr_base_strict_interl` and `rr_nonneg`. -/
syntax (name := rr_strict_interl_mul_X_inferred)
  "rr_strict_interl_mul_X" : tactic

/-- Closes `StrictInterl (X * f) (X * g)` from `proper : StrictInterl f g`.
The former `left_nonneg` and `right_nonneg` fields remain accepted for compatibility. -/
syntax (name := rr_strict_interl_mul_X_both)
  "rr_strict_interl_mul_X_both" " using " "proper" ":=" term :
  tactic

@[tactic_alt rr_strict_interl_mul_X_both]
syntax (name := rrStrictInterlMulXBothCompat)
  "rr_strict_interl_mul_X_both" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term :
  tactic

/-- Bare form of `rr_strict_interl_mul_X_both`: finds the strict-interlacing
certificate in the local context using `rr_base_strict_interl`. -/
syntax (name := rr_strict_interl_mul_X_both_inferred)
  "rr_strict_interl_mul_X_both" : tactic
end Tactic
end RealRooted

