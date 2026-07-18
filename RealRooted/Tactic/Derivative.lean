import RealRooted.Derivative
import RealRooted.Tactic.Finish

/-!
# Derivative tactic frontends

Thin wrappers for derivative interlacing and routine derivative side goals.
-/

open Lean.Elab.Tactic

namespace RealRooted
namespace Tactic

syntax (name := rr_derivative_interlaces_named)
  "rr_derivative_interlaces" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term :
  tactic

syntax (name := rr_derivative_interlaces_auto)
  "rr_derivative_interlaces" " using "
    "splits" ":=" term :
  tactic

syntax (name := rr_derivative_prec_named)
  "rr_derivative_prec" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term :
  tactic

syntax (name := rr_derivative_prec_auto)
  "rr_derivative_prec" " using "
    "splits" ":=" term :
  tactic

syntax (name := rr_nonneg_coeffs_derivative_named)
  "rr_nonneg_coeffs_derivative" " using "
    "nonneg_coeffs" ":=" term :
  tactic

syntax (name := rr_pos_lc_derivative_named)
  "rr_pos_lc_derivative" " using "
    "pos_lc" ":=" term ","
    "degree_ne_zero" ":=" term :
  tactic

syntax (name := rr_pos_lc_derivative_auto)
  "rr_pos_lc_derivative" " using "
    "pos_lc" ":=" term :
  tactic

syntax (name := rr_derivative_ne_zero_named)
  "rr_derivative_ne_zero" " using "
    "degree_ne_zero" ":=" term :
  tactic

syntax (name := rr_derivative_ne_zero_auto)
  "rr_derivative_ne_zero" :
  tactic

macro_rules
  | `(tactic|
      rr_derivative_interlaces using
        splits := $hsplits:term,
        degree_two := $hdeg:term) =>
      `(tactic| exact RealRooted.derivative_interlaces $hsplits $hdeg)
  | `(tactic|
      rr_derivative_interlaces using
        splits := $hsplits:term) =>
      `(tactic| exact RealRooted.derivative_interlaces $hsplits (by rr_close_side))
  | `(tactic|
      rr_derivative_prec using
        splits := $hsplits:term,
        degree_two := $hdeg:term) =>
      `(tactic| exact (RealRooted.derivative_interlaces $hsplits $hdeg).toPrec)
  | `(tactic|
      rr_derivative_prec using
        splits := $hsplits:term) =>
      `(tactic|
        exact (RealRooted.derivative_interlaces $hsplits (by rr_close_side)).toPrec)
  | `(tactic|
      rr_nonneg_coeffs_derivative using
        nonneg_coeffs := $hnn:term) =>
      `(tactic| exact RealRooted.HasNonnegCoeffs.derivative $hnn)
  | `(tactic|
      rr_pos_lc_derivative using
        pos_lc := $hpos:term,
        degree_ne_zero := $hdeg:term) =>
      `(tactic| exact RealRooted.HasPosLeadingCoeff.derivative $hpos $hdeg)
  | `(tactic|
      rr_pos_lc_derivative using
        pos_lc := $hpos:term) =>
      `(tactic|
        exact RealRooted.HasPosLeadingCoeff.derivative $hpos (by rr_close_side))
  | `(tactic|
      rr_derivative_ne_zero using
        degree_ne_zero := $hdeg:term) =>
      `(tactic| exact RealRooted.derivative_ne_zero_of_natDegree_ne_zero $hdeg)
  | `(tactic| rr_derivative_ne_zero) =>
      `(tactic|
        exact RealRooted.derivative_ne_zero_of_natDegree_ne_zero (by rr_close_side))

end Tactic
end RealRooted
