import RealRooted.StaircaseSum

/-!
# Staircase-sum tactic frontends

Thin wrappers for staircase-weighted sums of interlacing nonnegative
sequences.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_staircaseSum_zero_named)
  "rr_staircaseSum_zero" :
  tactic

syntax (name := rr_staircaseSum_length_named)
  "rr_staircaseSum_length" :
  tactic

syntax (name := rr_staircaseSum_prec_named)
  "rr_staircaseSum_prec" " using "
    "interlacing_nonneg" ":=" term ","
    "index_lt" ":=" term :
  tactic

syntax (name := rr_staircaseSum_realrooted_named)
  "rr_staircaseSum_realrooted" " using "
    "interlacing_nonneg" ":=" term ","
    "index_lt" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_staircaseSum_zero) =>
      `(tactic| exact RealRooted.staircaseSum_zero _)
  | `(tactic| rr_staircaseSum_length) =>
      `(tactic| exact RealRooted.staircaseSum_length _)
  | `(tactic|
      rr_staircaseSum_prec using
        interlacing_nonneg := $hfs:term,
        index_lt := $hm:term) =>
      `(tactic|
        exact RealRooted.prec_get_staircaseSum_of_isInterlacingSeqNonneg
          $hfs $hm)
  | `(tactic|
      rr_staircaseSum_realrooted using
        interlacing_nonneg := $hfs:term,
        index_lt := $hm:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_staircaseSum_of_isInterlacingSeqNonneg
          $hfs $hm)

end Tactic
end RealRooted
