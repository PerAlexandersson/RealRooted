import RealRooted.Tactic.CommonInterleaver.BasicSyntax

/-!
# Analytic common-interleaver tactic syntax

Parser declarations for root-count certificates and two-polynomial
common-interleaver endpoints.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_chudnovskySeymour_compatible_pair_common_interleaver_named)
  "rr_chudnovskySeymour_compatible_pair_common_interleaver" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "compatible" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_compatible_pair_common_left_interleaver_named)
  "rr_chudnovskySeymour_compatible_pair_common_left_interleaver" " using "
    "left_pos_lc" ":=" term ","
    "right_pos_lc" ":=" term ","
    "compatible" ":=" term :
  tactic

end Tactic
end RealRooted
