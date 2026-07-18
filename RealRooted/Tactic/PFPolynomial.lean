import RealRooted.PFPolynomial

/-!
# PF-polynomial tactic frontends

Thin wrappers for standard closure operations on `IsPFPolynomial`.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_pf_zero_named) "rr_pf_zero" : tactic
syntax (name := rr_pf_one_named) "rr_pf_one" : tactic
syntax (name := rr_pf_X_named) "rr_pf_X" : tactic
syntax (name := rr_pf_X_add_one_named) "rr_pf_X_add_one" : tactic

syntax (name := rr_pf_has_nonneg_named)
  "rr_pf_has_nonneg" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_zero_or_splits_named)
  "rr_pf_zero_or_splits" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_of_nonneg_splits_named)
  "rr_pf_of_nonneg_splits" " using "
    "nonneg" ":=" term ","
    "splits" ":=" term :
  tactic

syntax (name := rr_pf_of_nonneg_zero_or_splits_named)
  "rr_pf_of_nonneg_zero_or_splits" " using "
    "nonneg" ":=" term ","
    "zero_or_splits" ":=" term :
  tactic

syntax (name := rr_pf_C_nonneg_named)
  "rr_pf_C_nonneg" " using " "scalar_nonneg" ":=" term :
  tactic

syntax (name := rr_pf_const_mul_named)
  "rr_pf_const_mul" " using "
    "scalar_pos" ":=" term ","
    "pf" ":=" term :
  tactic

syntax (name := rr_pf_X_add_C_named)
  "rr_pf_X_add_C" " using " "scalar_nonneg" ":=" term :
  tactic

syntax (name := rr_pf_X_pow_named)
  "rr_pf_X_pow" " using " "exponent" ":=" term :
  tactic

syntax (name := rr_pf_X_mul_named)
  "rr_pf_X_mul" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_mul_named)
  "rr_pf_mul" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term :
  tactic

syntax (name := rr_pf_pow_named)
  "rr_pf_pow" " using "
    "pf" ":=" term ","
    "exponent" ":=" term :
  tactic

syntax (name := rr_pf_derivative_named)
  "rr_pf_derivative" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_reverse_named)
  "rr_pf_reverse" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_reciprocal_shift_named)
  "rr_pf_reciprocal_shift" " using "
    "pf" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_pf_mul_X_add_one_named)
  "rr_pf_mul_X_add_one" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_prec0_self_named)
  "rr_pf_prec0_self" " using " "pf" ":=" term :
  tactic

syntax (name := rr_pf_prec0_X_mul_both_named)
  "rr_pf_prec0_X_mul_both" " using "
    "left_pf" ":=" term ","
    "right_pf" ":=" term ","
    "prec0" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_pf_zero) =>
      `(tactic| exact RealRooted.IsPFPolynomial.zero)
  | `(tactic| rr_pf_one) =>
      `(tactic| exact RealRooted.IsPFPolynomial.one)
  | `(tactic| rr_pf_X) =>
      `(tactic| exact RealRooted.isPFPolynomial_X)
  | `(tactic| rr_pf_X_add_one) =>
      `(tactic| exact RealRooted.isPFPolynomial_X_add_one)
  | `(tactic| rr_pf_has_nonneg using pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.hasNonnegCoeffs $hp)
  | `(tactic| rr_pf_zero_or_splits using pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.eq_zero_or_splits $hp)
  | `(tactic|
      rr_pf_of_nonneg_splits using
        nonneg := $hnn:term,
        splits := $hsplits:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.of_realRooted_nonneg $hnn $hsplits)
  | `(tactic|
      rr_pf_of_nonneg_zero_or_splits using
        nonneg := $hnn:term,
        zero_or_splits := $hrr:term) =>
      `(tactic|
        exact RealRooted.IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
          $hnn $hrr)
  | `(tactic| rr_pf_C_nonneg using scalar_nonneg := $ha:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.of_C_nonneg $ha)
  | `(tactic|
      rr_pf_const_mul using
        scalar_pos := $ha:term,
        pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.const_mul $ha $hp)
  | `(tactic| rr_pf_X_add_C using scalar_nonneg := $ha:term) =>
      `(tactic| exact RealRooted.isPFPolynomial_X_add_C $ha)
  | `(tactic| rr_pf_X_pow using exponent := $n:term) =>
      `(tactic| exact RealRooted.isPFPolynomial_X_pow $n)
  | `(tactic| rr_pf_X_mul using pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.X_mul $hp)
  | `(tactic|
      rr_pf_mul using
        left_pf := $hp:term,
        right_pf := $hq:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.mul $hp $hq)
  | `(tactic|
      rr_pf_pow using
        pf := $hp:term,
        exponent := $n:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.pow $hp $n)
  | `(tactic| rr_pf_derivative using pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.derivative $hp)
  | `(tactic| rr_pf_reverse using pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.reverse $hp)
  | `(tactic|
      rr_pf_reciprocal_shift using
        pf := $hp:term,
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.reciprocalShift_preserves_pf $hp $hdeg)
  | `(tactic| rr_pf_mul_X_add_one using pf := $hp:term) =>
      `(tactic| exact RealRooted.isPFPolynomial_mul_X_add_one $hp)
  | `(tactic| rr_pf_prec0_self using pf := $hp:term) =>
      `(tactic| exact RealRooted.IsPFPolynomial.prec0_self $hp)
  | `(tactic|
      rr_pf_prec0_X_mul_both using
        left_pf := $hp:term,
        right_pf := $hq:term,
        prec0 := $hpq:term) =>
      `(tactic| exact RealRooted.prec0_X_mul_both_of_pf $hp $hq $hpq)

end Tactic
end RealRooted
