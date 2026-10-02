import RealRooted.Tactic.CommonInterleaver.AnalyticRules
import RealRooted.Tactic.CommonInterleaver.FamilySyntax

/-!
# Family common-interleaver tactic rules

Routing helpers and macro expansions for Chudnovsky--Seymour four-way
certificates and pairwise-to-family compatibility upgrades.
-/

open Polynomial

namespace RealRooted
namespace Tactic

macro_rules
  | `(tactic|
      rr_chudnovskySeymour_fourWay_pairDegreeSplit_nonnegCoeffs using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_nonneg_coeffs := $hnn:term,
        same_degree := $hsame:term,
        succ_degree := $hsucc:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_pairDegreeSplit_and_nonnegCoeffs
          $hrr $hpos $hnn $hsame $hsucc)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_degree_le_one using
        member_pos_lc := $hpos:term,
        member_degree_le_one := $hdeg:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_natDegree_le_one
          $hpos $hdeg)
  | `(tactic|
      rr_chudnovskySeymour_fourWay_degree_le_two using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term,
        member_degree_le_two := $hdeg:term) =>
      `(tactic|
        exact chudnovskySeymour_fourWay_of_natDegree_le_two
          $hrr $hpos $hdeg)
  | `(tactic|
      rr_chudnovskySeymour_pairwiseCompatible_iff_familyCompatible using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term) =>
      `(tactic|
        exact RealRooted.chudnovskySeymour_pairwiseCompatible_iff_familyCompatible
          $hrr $hpos)
  | `(tactic|
      rr_chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term) =>
      `(tactic|
        exact
          RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonLeftInterleaver
            $hrr $hpos)
  | `(tactic|
      rr_chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver using
        member_realrooted := $hrr:term,
        member_pos_lc := $hpos:term) =>
      `(tactic|
        exact
          RealRooted.chudnovskySeymour_pairwiseCompatible_iff_commonInterleaver
            $hrr $hpos)

end Tactic
end RealRooted
