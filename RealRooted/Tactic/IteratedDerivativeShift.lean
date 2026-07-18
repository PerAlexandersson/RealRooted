import RealRooted.IteratedDerivativeShift

/-!
# Iterated derivative-shift tactic frontends

Thin wrappers for `TDeriv` and `iterateTDeriv` preservation facts.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_TDeriv_pos_lc_named)
  "rr_TDeriv_pos_lc" " using " "pos_lc" ":=" term :
  tactic

syntax (name := rr_TDeriv_ne_zero_named)
  "rr_TDeriv_ne_zero" " using " "nonzero" ":=" term :
  tactic

syntax (name := rr_TDeriv_splits_named)
  "rr_TDeriv_splits" " using "
    "eps_pos" ":=" term ","
    "splits" ":=" term :
  tactic

syntax (name := rr_TDeriv_prec_named)
  "rr_TDeriv_prec" " using "
    "eps_pos" ":=" term ","
    "nonzero" ":=" term ","
    "splits" ":=" term :
  tactic

syntax (name := rr_iterateTDeriv_ne_zero_named)
  "rr_iterateTDeriv_ne_zero" " using " "nonzero" ":=" term :
  tactic

syntax (name := rr_iterateTDeriv_splits_named)
  "rr_iterateTDeriv_splits" " using "
    "eps_pos" ":=" term ","
    "splits" ":=" term :
  tactic

syntax (name := rr_iterateTDeriv_prec_succ_named)
  "rr_iterateTDeriv_prec_succ" " using "
    "eps_pos" ":=" term ","
    "nonzero" ":=" term ","
    "splits" ":=" term :
  tactic

syntax (name := rr_iterateTDeriv_natDegree_named)
  "rr_iterateTDeriv_natDegree" :
  tactic

syntax (name := rr_iterateTDeriv_leadingCoeff_named)
  "rr_iterateTDeriv_leadingCoeff" :
  tactic

syntax (name := rr_iterateTDeriv_monic_named)
  "rr_iterateTDeriv_monic" " using " "monic" ":=" term :
  tactic

syntax (name := rr_TDeriv_add_named)
  "rr_TDeriv_add" :
  tactic

syntax (name := rr_TDeriv_C_mul_named)
  "rr_TDeriv_C_mul" :
  tactic

syntax (name := rr_iterateTDeriv_add_named)
  "rr_iterateTDeriv_add" :
  tactic

syntax (name := rr_iterateTDeriv_C_mul_named)
  "rr_iterateTDeriv_C_mul" :
  tactic

syntax (name := rr_derivative_TDeriv_named)
  "rr_derivative_TDeriv" :
  tactic

syntax (name := rr_iterate_derivative_TDeriv_named)
  "rr_iterate_derivative_TDeriv" :
  tactic

syntax (name := rr_iterate_derivative_iterateTDeriv_named)
  "rr_iterate_derivative_iterateTDeriv" :
  tactic

macro_rules
  | `(tactic| rr_TDeriv_pos_lc using pos_lc := $hp:term) =>
      `(tactic| exact RealRooted.HasPosLeadingCoeff.TDeriv $hp)
  | `(tactic| rr_TDeriv_ne_zero using nonzero := $hp:term) =>
      `(tactic| exact RealRooted.TDeriv_ne_zero $hp)
  | `(tactic|
      rr_TDeriv_splits using
        eps_pos := $heps:term,
        splits := $hp:term) =>
      `(tactic| exact RealRooted.splits_tderiv $heps $hp)
  | `(tactic|
      rr_TDeriv_prec using
        eps_pos := $heps:term,
        nonzero := $hp0:term,
        splits := $hp:term) =>
      `(tactic| exact RealRooted.prec_TDeriv $heps $hp0 $hp)
  | `(tactic| rr_iterateTDeriv_ne_zero using nonzero := $hp:term) =>
      `(tactic| exact RealRooted.iterateTDeriv_ne_zero $hp)
  | `(tactic|
      rr_iterateTDeriv_splits using
        eps_pos := $heps:term,
        splits := $hp:term) =>
      `(tactic| exact RealRooted.splits_iterateTDeriv $heps $hp)
  | `(tactic|
      rr_iterateTDeriv_prec_succ using
        eps_pos := $heps:term,
        nonzero := $hp0:term,
        splits := $hp:term) =>
      `(tactic| exact RealRooted.prec_iterateTDeriv_succ $heps $hp0 $hp)
  | `(tactic| rr_iterateTDeriv_natDegree) =>
      `(tactic| exact RealRooted.natDegree_iterateTDeriv _ _ _)
  | `(tactic| rr_iterateTDeriv_leadingCoeff) =>
      `(tactic| exact RealRooted.leadingCoeff_iterateTDeriv _ _ _)
  | `(tactic| rr_iterateTDeriv_monic using monic := $hp:term) =>
      `(tactic| exact RealRooted.monic_iterateTDeriv $hp)
  | `(tactic| rr_TDeriv_add) =>
      `(tactic| exact RealRooted.TDeriv_add _ _ _)
  | `(tactic| rr_TDeriv_C_mul) =>
      `(tactic| exact RealRooted.TDeriv_C_mul _ _ _)
  | `(tactic| rr_iterateTDeriv_add) =>
      `(tactic| exact RealRooted.iterateTDeriv_add _ _ _ _)
  | `(tactic| rr_iterateTDeriv_C_mul) =>
      `(tactic| exact RealRooted.iterateTDeriv_C_mul _ _ _ _)
  | `(tactic| rr_derivative_TDeriv) =>
      `(tactic| exact RealRooted.derivative_TDeriv _ _)
  | `(tactic| rr_iterate_derivative_TDeriv) =>
      `(tactic| exact RealRooted.iterate_derivative_TDeriv _ _ _)
  | `(tactic| rr_iterate_derivative_iterateTDeriv) =>
      `(tactic| exact RealRooted.iterate_derivative_iterateTDeriv _ _ _ _)

end Tactic
end RealRooted
