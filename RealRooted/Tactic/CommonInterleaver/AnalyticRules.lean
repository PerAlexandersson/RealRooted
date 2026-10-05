import RealRooted.Tactic.CommonInterleaver.AnalyticSyntax
import RealRooted.Tactic.CommonInterleaver.BasicRules

/-!
# Analytic common-interleaver tactic rules

Macro expansions for root-count certificates and two-polynomial
common-interleaver endpoints.
-/

open Polynomial

namespace RealRooted
namespace Tactic

macro_rules
  | `(tactic|
      rr_chudnovskySeymour_compatible_pair_common_interleaver using
        left_pos_lc := $hf:term,
        right_pos_lc := $hg:term,
        compatible := $hcomp:term) =>
      `(tactic|
        exact RealRooted.chudnovskySeymour_compatiblePairHasCommonInterleaver
          $hf $hg $hcomp)
  | `(tactic|
      rr_chudnovskySeymour_compatible_pair_common_left_interleaver using
        left_pos_lc := $hf:term,
        right_pos_lc := $hg:term,
        compatible := $hcomp:term) =>
      `(tactic|
        exact RealRooted.chudnovskySeymour_compatiblePairHasCommonLeftInterleaver
          $hf $hg $hcomp)

end Tactic
end RealRooted
