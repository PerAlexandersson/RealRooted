import RealRooted.Challenges.Wagner

/-!
# Wagner challenge tactic frontends

Thin wrappers around the challenge-facing Wagner lemma forms.
-/

open Polynomial

namespace RealRooted
namespace Tactic

syntax (name := rr_wagner_common_right_add_named)
  "rr_wagner_common_right_add" " using "
    "left" ":=" term ","
    "right" ":=" term ","
    "common" ":=" term ","
    "left_interlaces_common" ":=" term ","
    "right_interlaces_common" ":=" term :
  tactic

syntax (name := rr_wagner_common_left_add_named)
  "rr_wagner_common_left_add" " using "
    "left" ":=" term ","
    "right" ":=" term ","
    "common" ":=" term ","
    "common_interlaces_left" ":=" term ","
    "common_interlaces_right" ":=" term :
  tactic

syntax (name := rr_wagner_mulX_iff_named)
  "rr_wagner_mulX_iff" " using "
    "shorter" ":=" term ","
    "longer" ":=" term ","
    "degree" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_wagner_common_right_add using
        left := $hf:term,
        right := $hg:term,
        common := $hh:term,
        left_interlaces_common := $hfh:term,
        right_interlaces_common := $hgh:term) =>
      `(tactic|
        exact RealRooted.Challenges.Wagner.commonRight_add
          $hf $hg $hh $hfh $hgh)
  | `(tactic|
      rr_wagner_common_left_add using
        left := $hf:term,
        right := $hg:term,
        common := $hh:term,
        common_interlaces_left := $hhf:term,
        common_interlaces_right := $hhg:term) =>
      `(tactic|
        exact RealRooted.Challenges.Wagner.commonLeft_add
          $hf $hg $hh $hhf $hhg)
  | `(tactic|
      rr_wagner_mulX_iff using
        shorter := $hf:term,
        longer := $hg:term,
        degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.Challenges.Wagner.mulX_iff $hf $hg $hdeg)

end Tactic
end RealRooted
