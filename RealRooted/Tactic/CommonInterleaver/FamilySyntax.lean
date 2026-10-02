import RealRooted.Tactic.CommonInterleaver.AnalyticSyntax

/-!
# Family common-interleaver tactic syntax

Parser declarations for Chudnovsky--Seymour four-way certificates and
pairwise-to-family compatibility upgrades.
-/

namespace RealRooted
namespace Tactic

syntax (name := rr_chudnovskySeymour_fourWay_degree_le_one_named)
  "rr_chudnovskySeymour_fourWay_degree_le_one" " using "
    "member_pos_lc" ":=" term ","
    "member_degree_le_one" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_fourWay_degree_le_two_named)
  "rr_chudnovskySeymour_fourWay_degree_le_two" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term ","
    "member_degree_le_two" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver_named)
  "rr_chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver_named)
  "rr_chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

syntax (name := rr_chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_named)
  "rr_chudnovskySeymour_pairwiseCompatible_iff_familyCompatible" " using "
    "member_realrooted" ":=" term ","
    "member_pos_lc" ":=" term :
  tactic

end Tactic
end RealRooted
