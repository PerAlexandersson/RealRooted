import RealRooted.MagnitudeDominated

/-!
# Magnitude-dominated lag tactic frontends

Thin wrappers for magnitude-dominated Ma-Wang / generalized Liu-Wang
interlacing certificates.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_magnitude_dominated_succ_named)
  "rr_magnitude_dominated_succ" " using "
    "interlaces" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "certificate" ":=" term :
  tactic

syntax (name := rr_magnitude_dominated_same_named)
  "rr_magnitude_dominated_same" " using "
    "interlaces" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "certificate" ":=" term :
  tactic

syntax (name := rr_magnitude_dominated_named)
  "rr_magnitude_dominated" " using "
    "interlaces" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "certificate" ":=" term :
  tactic

syntax (name := rr_magnitude_cert_abs_dominated_named)
  "rr_magnitude_cert_abs_dominated" " using "
    "head_negative" ":=" term ","
    "domination" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_magnitude_dominated_succ using
        interlaces := $hinter:term,
        interlacer_pos_lc := $hinterpos:term,
        target_pos_lc := $htargetpos:term,
        degree := $hdeg:term,
        certificate := $hcert:term) =>
      `(tactic|
        exact RealRooted.prec_of_magnitude_dominated_succ
          $hinter $hinterpos $htargetpos $hdeg $hcert)
  | `(tactic|
      rr_magnitude_dominated_same using
        interlaces := $hinter:term,
        interlacer_pos_lc := $hinterpos:term,
        target_pos_lc := $htargetpos:term,
        degree := $hdeg:term,
        certificate := $hcert:term) =>
      `(tactic|
        exact RealRooted.prec_of_magnitude_dominated_same
          $hinter $hinterpos $htargetpos $hdeg $hcert)
  | `(tactic|
      rr_magnitude_dominated using
        interlaces := $hinter:term,
        interlacer_pos_lc := $hinterpos:term,
        target_pos_lc := $htargetpos:term,
        degree_lower := $hlo:term,
        degree_upper := $hhi:term,
        certificate := $hcert:term) =>
      `(tactic|
        exact RealRooted.prec_of_magnitude_dominated
          $hinter $hinterpos $htargetpos $hlo $hhi $hcert)
  | `(tactic|
      rr_magnitude_cert_abs_dominated using
        head_negative := $hhead:term,
        domination := $hdom:term) =>
      `(tactic| exact RealRooted.magnitude_cert_of_abs_dominated $hhead $hdom)

end Tactic
end RealRooted
