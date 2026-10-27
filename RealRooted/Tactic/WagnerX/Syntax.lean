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

/-- Closes `StrictInterl g ((C c * X) * f)` from `proper : StrictInterl f g`;
`left_nonneg : HasNonnegCoeffs f`; `right_nonneg : HasNonnegCoeffs g`; and `coeff_ne : c ≠ 0`. -/
syntax (name := rr_strict_interl_C_mul_X)
  "rr_strict_interl_C_mul_X" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "coeff_ne" ":=" term :
  tactic

/-- Variant of `rr_strict_interl_C_mul_X` with `coeff_pos : 0 < c` in place of
`coeff_ne : c ≠ 0`. -/
syntax (name := rr_strict_interl_C_mul_X_pos)
  "rr_strict_interl_C_mul_X" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "coeff_pos" ":=" term :
  tactic

/-- Bare form of `rr_strict_interl_C_mul_X`: takes `coeff_ne : c ≠ 0` from the `using` clause and
finds the other certificates in the local context by `rr_lookup`. -/
syntax (name := rr_strict_interl_C_mul_X_inferred)
  "rr_strict_interl_C_mul_X" " using "
    "coeff_ne" ":=" term :
  tactic

/-- Bare form of `rr_strict_interl_C_mul_X_pos`: takes `coeff_pos : 0 < c` from the `using` clause
and finds the other certificates in the local context by `rr_lookup`. -/
syntax (name := rr_strict_interl_C_mul_X_pos_inferred)
  "rr_strict_interl_C_mul_X" " using "
    "coeff_pos" ":=" term :
  tactic

/-- Closes `StrictInterl (X * f.derivative) (X * f)` from `splits : f.Splits`
and `degree_two : 2 ≤ f.natDegree`. The former `nonneg_coeffs` field remains
accepted for compatibility. -/
syntax (name := rr_strict_interl_X_derivative_X_self)
  "rr_strict_interl_X_derivative_X_self" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term :
  tactic

@[tactic_alt rr_strict_interl_X_derivative_X_self]
syntax (name := rrStrictInterlXDerivativeXSelfCompat)
  "rr_strict_interl_X_derivative_X_self" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "nonneg_coeffs" ":=" term :
  tactic

/-- Bare form of `rr_strict_interl_X_derivative_X_self`: finds the splitting
and degree certificates in the local context, using `rr_degree` for the latter. -/
syntax (name := rr_strict_interl_X_derivative_X_self_inferred)
  "rr_strict_interl_X_derivative_X_self" : tactic

/-- Closes `StrictInterl g (X * (C c * g.derivative + C a * f))` from `proper : StrictInterl f g`;
`left_nonneg : HasNonnegCoeffs f`; `right_nonneg : HasNonnegCoeffs g`;
`degree_two : 2 ≤ g.natDegree`; `lag_coeff_pos : 0 < a`; and `derivative_coeff_pos : 0 < c`. -/
syntax (name := rr_strict_interl_wagner_derivative_gap_lag)
  "rr_strict_interl_wagner_derivative_gap_lag" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term :
  tactic

/-- Bare form of `rr_strict_interl_wagner_derivative_gap_lag`: finds all certificates in the local
context by `rr_lookup`, using `rr_base_strict_interl`, `rr_nonneg` and `rr_degree`, and proves the
coefficient positivity by `rr_wagner_pos` if needed. -/
syntax (name := rr_strict_interl_wagner_derivative_gap_lag_inferred)
  "rr_strict_interl_wagner_derivative_gap_lag" : tactic

/-- Closes a positivity side goal for a coefficient by `rr_side_pos`. -/
syntax (name := rr_wagner_pos) "rr_wagner_pos" : tactic

/-- Term form of `rr_wagner_pos`: elaborates to `by rr_wagner_pos`. -/
syntax (name := rr_wagner_pos_term) "rr_wagner_pos_term" : term

/-- Term `fun n => by rr_wagner_pos`: positivity of a coefficient at every row. -/
syntax (name := rr_wagner_pos_seq) "rr_wagner_pos_seq" : term

macro_rules
  | `(tactic| rr_wagner_pos) =>
      `(tactic| rr_side_pos)
  | `(rr_wagner_pos_term) =>
      `(by rr_wagner_pos)
  | `(rr_wagner_pos_seq) =>
      `(fun n => by rr_wagner_pos)
end Tactic
end RealRooted
