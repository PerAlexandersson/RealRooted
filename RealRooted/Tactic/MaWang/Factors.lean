module

public import RealRooted.Tactic.MaWang.Denominator

/-!
# Ma--Wang tactic factor rules

Elaboration rules for specialized derivative-factor sequence certificates.
-/

@[expose] public section

namespace RealRooted
namespace Tactic

macro_rules
  | `(tactic|
      rr_mw_derivative_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact RealRooted.MaWang.strictInterl_derivative_X_sequence_of_nonneg_coeffs
          $hbase $hpos $hnonneg $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_X_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_X_sequence_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          recurrence := $hrec,
          degree_lower := rr_mw_tail_degree_seq $hdeg,
          degree_upper := rr_mw_tail_degree_seq $hdeg)
  | `(tactic|
      rr_mw_derivative_X_one_add_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.MaWang.strictInterl_derivative_X_mul_one_add_X_sequence_of_nonneg_coeffs
            $hbase $hpos $hnonneg $hroot_lower $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_X_one_add_sequence_nonneg using
        base := $hbase:term,
        pos_lc := $hpos:term,
        nonneg_coeffs := $hnonneg:term,
        root_lower := $hroot_lower:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_X_one_add_sequence_nonneg using
          base := $hbase,
          pos_lc := $hpos,
          nonneg_coeffs := $hnonneg,
          root_lower := $hroot_lower,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)

end Tactic
end RealRooted
