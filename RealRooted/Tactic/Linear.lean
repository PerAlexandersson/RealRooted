import RealRooted.Linear
import RealRooted.Tactic.Finish

/-!
# Linear-polynomial tactic frontends

Thin wrappers for the degree-one real-rootedness and interlacing endpoints.
-/

open Lean.Elab.Tactic

namespace RealRooted
namespace Tactic

syntax (name := rr_X_sub_C_realrooted_named)
  "rr_X_sub_C_realrooted" " using "
    "root" ":=" term :
  tactic

syntax (name := rr_degree_one_realrooted_named)
  "rr_degree_one_realrooted" " using "
    "degree" ":=" term :
  tactic

syntax (name := rr_degree_one_realrooted_auto)
  "rr_degree_one_realrooted" : tactic

syntax (name := rr_natDegree_le_one_realrooted_named)
  "rr_natDegree_le_one_realrooted" " using "
    "nonzero" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_interlaces_one_linear_named)
  "rr_interlaces_one_linear" " using "
    "degree" ":=" term :
  tactic

syntax (name := rr_interlaces_one_linear_auto)
  "rr_interlaces_one_linear" : tactic

syntax (name := rr_interlaces_C_linear_named)
  "rr_interlaces_C_linear" " using "
    "scalar_ne" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_interlaces_C_linear_auto)
  "rr_interlaces_C_linear" " using "
    "scalar_ne" ":=" term :
  tactic

syntax (name := rr_prec_C_mul_left_named)
  "rr_prec_C_mul_left" " using "
    "prec" ":=" term ","
    "scalar_ne" ":=" term :
  tactic

syntax (name := rr_prec_C_mul_left_auto)
  "rr_prec_C_mul_left" " using "
    "prec" ":=" term :
  tactic

syntax (name := rr_prec_C_mul_right_named)
  "rr_prec_C_mul_right" " using "
    "prec" ":=" term ","
    "scalar_ne" ":=" term :
  tactic

syntax (name := rr_prec_C_mul_right_auto)
  "rr_prec_C_mul_right" " using "
    "prec" ":=" term :
  tactic

syntax (name := rr_prec_C_mul_both_named)
  "rr_prec_C_mul_both" " using "
    "prec" ":=" term ","
    "left_ne" ":=" term ","
    "right_ne" ":=" term :
  tactic

syntax (name := rr_prec_C_mul_both_auto)
  "rr_prec_C_mul_both" " using "
    "prec" ":=" term :
  tactic

syntax (name := rr_C_mul_realrooted_named)
  "rr_C_mul_realrooted" " using "
    "realrooted" ":=" term ","
    "scalar_ne" ":=" term :
  tactic

syntax (name := rr_X_mul_realrooted_named)
  "rr_X_mul_realrooted" " using "
    "realrooted" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_X_sub_C_realrooted using
        root := $r:term) =>
      `(tactic| exact RealRooted.isRealRooted_X_sub_C $r)
  | `(tactic|
      rr_degree_one_realrooted using
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.isRealRooted_of_degree_one $hdeg)
  | `(tactic| rr_degree_one_realrooted) =>
      `(tactic|
        exact RealRooted.isRealRooted_of_degree_one (by
          first
            | rr_lookup [rr_degree]
            | compute_degree!))
  | `(tactic|
      rr_natDegree_le_one_realrooted using
        nonzero := $hne:term,
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.isRealRooted_of_natDegree_le_one $hne $hdeg)
  | `(tactic|
      rr_interlaces_one_linear using
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.interlaces_one_linear $hdeg)
  | `(tactic| rr_interlaces_one_linear) =>
      `(tactic|
        exact RealRooted.interlaces_one_linear (by
          first
            | rr_lookup [rr_degree]
            | compute_degree!))
  | `(tactic|
      rr_interlaces_C_linear using
        scalar_ne := $hc:term,
        degree := $hdeg:term) =>
      `(tactic| exact RealRooted.interlaces_C_linear $hc $hdeg)
  | `(tactic|
      rr_interlaces_C_linear using
        scalar_ne := $hc:term) =>
      `(tactic|
        exact RealRooted.interlaces_C_linear $hc (by
          first
            | rr_lookup [rr_degree]
            | compute_degree!))
  | `(tactic|
      rr_prec_C_mul_left using
        prec := $hprec:term,
        scalar_ne := $ha:term) =>
      `(tactic| exact RealRooted.prec_C_mul_left $hprec $ha)
  | `(tactic|
      rr_prec_C_mul_left using
        prec := $hprec:term) =>
      `(tactic| exact RealRooted.prec_C_mul_left $hprec (by rr_side_ne))
  | `(tactic|
      rr_prec_C_mul_right using
        prec := $hprec:term,
        scalar_ne := $ha:term) =>
      `(tactic| exact RealRooted.prec_C_mul_right $hprec $ha)
  | `(tactic|
      rr_prec_C_mul_right using
        prec := $hprec:term) =>
      `(tactic| exact RealRooted.prec_C_mul_right $hprec (by rr_side_ne))
  | `(tactic|
      rr_prec_C_mul_both using
        prec := $hprec:term,
        left_ne := $hleft:term,
        right_ne := $hright:term) =>
      `(tactic|
        exact RealRooted.prec_C_mul_right
          (RealRooted.prec_C_mul_left $hprec $hleft) $hright)
  | `(tactic|
      rr_prec_C_mul_both using
        prec := $hprec:term) =>
      `(tactic|
        exact RealRooted.prec_C_mul_right
          (RealRooted.prec_C_mul_left $hprec (by rr_side_ne)) (by rr_side_ne))
  | `(tactic|
      rr_C_mul_realrooted using
        realrooted := $hp:term,
        scalar_ne := $ha:term) =>
      `(tactic| exact RealRooted.isRealRooted_C_mul $hp.1 $hp.2 $ha)
  | `(tactic|
      rr_X_mul_realrooted using
        realrooted := $hp:term) =>
      `(tactic| exact RealRooted.isRealRooted_X_mul $hp.1 $hp.2)

end Tactic
end RealRooted
