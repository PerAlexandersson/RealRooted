import RealRooted.Tactic.ReciprocalShift

/-!
# J1 gap-3 reciprocal frontend

Compatibility tactic syntax for the original J1-specific reciprocal-shift route;
the underlying theorems are `isRealRooted_of_reciprocalShift_sequence` and
`isRealRooted_of_reciprocalShift_pf_sequence`.
-/

open Polynomial

namespace RealRooted

namespace Tactic

syntax (name := rr_j1_gap3_reciprocal_sequence_realrooted)
  "rr_j1_gap3_reciprocal_sequence_realrooted" " using "
    "model_realrooted" ":=" term ","
    "degree" ":=" term ","
    "reciprocal" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_j1_gap3_reciprocal_sequence_realrooted using
        model_realrooted := $hmodel:term,
        degree := $hdegree:term,
        reciprocal := $hreciprocal:term) =>
      `(tactic|
        rr_reciprocal_shift_sequence using
          model_realrooted := $hmodel,
          degree := $hdegree,
          reciprocal := $hreciprocal)

syntax (name := rr_j1_gap3_reciprocal_pf_sequence_realrooted)
  "rr_j1_gap3_reciprocal_pf_sequence_realrooted" " using "
    "model_pf" ":=" term ","
    "model_ne" ":=" term ","
    "degree" ":=" term ","
    "reciprocal" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_j1_gap3_reciprocal_pf_sequence_realrooted using
        model_pf := $hmodel:term,
        model_ne := $hmodel_ne:term,
        degree := $hdegree:term,
        reciprocal := $hreciprocal:term) =>
      `(tactic|
        rr_reciprocal_shift_pf_sequence using
          model_pf := $hmodel,
          model_ne := $hmodel_ne,
          degree := $hdegree,
          reciprocal := $hreciprocal)

end Tactic
end RealRooted
