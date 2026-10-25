module

public import RealRooted.Tactic.CommonInterleaver.BasicSyntax

/-!
# Analytic common-interleaver tactic syntax

Parser declarations for root-count certificates and two-polynomial
common-interleaver endpoints.
-/

@[expose] public section

namespace RealRooted
namespace Tactic

/-- Closes `∃ k, StrictInterl f k ∧ StrictInterl g k` for a compatible pair `f`, `g`;
`left_pos_lc` and `right_pos_lc` give positive leading coefficients and
`compatible : Compatible f g`. -/
syntax (name := rr_chudnovskySeymour_compatible_pair_common_interleaver_named)
  "rr_chudnovskySeymour_compatible_pair_common_interleaver" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "compatible" ":=" term :
  tactic

/-- Closes `∃ k, StrictInterl k f ∧ StrictInterl k g` for a compatible pair `f`, `g`; the
arguments are as in `rr_chudnovskySeymour_compatible_pair_common_interleaver`. -/
syntax (name := rr_chudnovskySeymour_compatible_pair_common_left_interleaver_named)
  "rr_chudnovskySeymour_compatible_pair_common_left_interleaver" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "compatible" ":=" term :
  tactic

end Tactic
end RealRooted
