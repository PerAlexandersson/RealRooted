module

public import RealRooted.Tactic.MaWang.FactorSyntax

/-!
# Ma--Wang tactic step rules

Elaboration rules for the one-step and short-window certificates.
-/

public section

namespace RealRooted
namespace Tactic

macro_rules
  | `(tactic| rr_mw_root_window_linear_facts) =>
      `(tactic|
        all_goals
          try
            have hroot_window_one_add_mul_nonneg : 0 ≤ 1 + r := by
              linarith only [hroot_window_lower]
          try
            have hroot_window_one_add_two_mul_nonneg : 0 ≤ 1 + 2 * r := by
              linarith only [hroot_window_lower]
          try
            have hroot_window_one_add_three_mul_nonneg : 0 ≤ 1 + 3 * r := by
              linarith only [hroot_window_lower]
          try
            have hroot_window_one_add_four_mul_nonneg : 0 ≤ 1 + 4 * r := by
              linarith only [hroot_window_lower]
          try
            have hroot_window_two_add_three_mul_nonneg : 0 ≤ 2 + 3 * r := by
              linarith only [hroot_window_lower])
  | `(tactic| rr_ma_wang) =>
      `(tactic|
        rr_ma_wang using
          splits := (by rr_lookup),
          degree_lower := (by rr_lookup [rr_degree]),
          degree_upper := (by rr_lookup [rr_degree]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          root_sign := (by rr_lookup))
  | `(tactic| rr_ma_wang_same) =>
      `(tactic|
        rr_ma_wang_same using
          splits := (by rr_lookup),
          degree := (by rr_lookup [rr_degree]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          root_sign := (by rr_lookup))
  | `(tactic| rr_ma_wang_succ) =>
      `(tactic|
        rr_ma_wang_succ using
          splits := (by rr_lookup),
          degree := (by rr_lookup [rr_degree]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          root_sign := (by rr_lookup))
  | `(tactic|
      rr_ma_wang using
        $hf:term, $hdeg_lo:term, $hdeg_hi:term, $hF_pos:term,
        $hf_pos:term, $hroot_sign:term) =>
      `(tactic|
        exact RealRooted.MaWang.strictInterl_derivative_of_mul_sq_neg_of_splits
          $hf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hroot_sign)
  | `(tactic|
      rr_ma_wang using
        splits := $hf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_sign := $hroot_sign:term) =>
      `(tactic|
        rr_ma_wang using
          $hf, $hdeg_lo, $hdeg_hi, $hF_pos, $hf_pos, $hroot_sign)
  | `(tactic|
      rr_ma_wang_same using
        $hf:term, $hdeg:term, $hF_pos:term, $hf_pos:term, $hroot_sign:term) =>
      `(tactic|
        exact RealRooted.MaWang.strictInterl_derivative_of_mul_sq_neg_of_splits
          $hf (Eq.ge $hdeg) (Nat.le_succ_of_le (Eq.le $hdeg))
          $hF_pos $hf_pos $hroot_sign)
  | `(tactic|
      rr_ma_wang_same using
        splits := $hf:term,
        degree := $hdeg:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_sign := $hroot_sign:term) =>
      `(tactic|
        rr_ma_wang_same using $hf, $hdeg, $hF_pos, $hf_pos, $hroot_sign)
  | `(tactic|
      rr_ma_wang_succ using
        $hf:term, $hdeg:term, $hF_pos:term, $hf_pos:term, $hroot_sign:term) =>
      `(tactic|
        exact RealRooted.MaWang.strictInterl_derivative_of_mul_sq_neg_of_splits
          $hf (Nat.le_of_succ_le (Eq.ge $hdeg)) (Eq.le $hdeg)
          $hF_pos $hf_pos $hroot_sign)
  | `(tactic|
      rr_ma_wang_succ using
        splits := $hf:term,
        degree := $hdeg:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_sign := $hroot_sign:term) =>
      `(tactic|
        rr_ma_wang_succ using $hf, $hdeg, $hF_pos, $hf_pos, $hroot_sign)
  | `(tactic|
      rr_strict_interl_evalCoeff_nonpos using
        interlaces := $hgf:term,
        source_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        coeff_nonpos := $hb_nonpos:term) =>
      `(tactic|
        exact RealRooted.strictInterl_of_interlaces_evalCoeff_nonpos
          $hgf $hg_pos $hF_pos $hdeg_lo $hdeg_hi $hb_nonpos)
  | `(tactic|
      rr_strict_interl_evalCoeff_nonpos using
        interlaces := $hgf:term,
        source_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree := $hdeg:term,
        coeff_nonpos := $hb_nonpos:term) =>
      `(tactic|
        rr_strict_interl_evalCoeff_nonpos using
          interlaces := $hgf,
          source_pos_lc := $hg_pos,
          target_pos_lc := $hF_pos,
          degree_lower := (by rr_mw_degree_from $hdeg),
          degree_upper := (by rr_mw_degree_from $hdeg),
          coeff_nonpos := $hb_nonpos)
  | `(tactic| rr_strict_interl_evalCoeff_nonpos) =>
      `(tactic|
        rr_strict_interl_evalCoeff_nonpos using
          interlaces := (by rr_lookup),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          degree_lower := (by rr_lookup [rr_degree]),
          degree_upper := (by rr_lookup [rr_degree]),
          coeff_nonpos := (by rr_lookup))
  | `(tactic| rr_strict_interl_evalCoeff_nonpos using degree := $hdeg:term) =>
      `(tactic|
        rr_strict_interl_evalCoeff_nonpos using
          interlaces := (by rr_lookup),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          degree := $hdeg,
          coeff_nonpos := (by rr_lookup))
  | `(tactic|
      rr_mw_derivative_nonpos using
        $hf:term, $hdeg_lo:term, $hdeg_hi:term, $hF_pos:term,
        $hf_pos:term, $hv_nonpos:term) =>
      `(tactic|
        exact RealRooted.MaWang.strictInterl_derivative_of_nonpos_of_splits
          $hf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hv_nonpos)
  | `(tactic|
      rr_mw_derivative_nonpos using
        splits := $hf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonpos := $hv_nonpos:term) =>
      `(tactic|
        rr_mw_derivative_nonpos using
          $hf, $hdeg_lo, $hdeg_hi, $hF_pos, $hf_pos, $hv_nonpos)
  | `(tactic|
      rr_mw_derivative_nonpos using
        splits := $hf:term,
        degree := $hdeg:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonpos := $hv_nonpos:term) =>
      `(tactic|
        rr_mw_derivative_nonpos using
          splits := $hf,
          degree_lower := (by rr_mw_degree_from $hdeg),
          degree_upper := (by rr_mw_degree_from $hdeg),
          target_pos_lc := $hF_pos,
          source_pos_lc := $hf_pos,
          coeff_nonpos := $hv_nonpos)
  | `(tactic| rr_mw_derivative_nonpos) =>
      `(tactic|
        rr_mw_derivative_nonpos using
          splits := (by rr_lookup),
          degree_lower := (by rr_lookup [rr_degree]),
          degree_upper := (by rr_lookup [rr_degree]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          coeff_nonpos := (by rr_lookup))
  | `(tactic| rr_mw_derivative_nonpos using degree := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos using
          splits := (by rr_lookup),
          degree := $hdeg,
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          coeff_nonpos := (by rr_lookup))
  | `(tactic|
      rr_mw_derivative_sign_roots_nonpos using
        splits := $hf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        roots_nonpos := $hroot_nonpos:term) =>
      `(tactic|
        exact
          RealRooted.MaWang.strictInterl_derivative_of_nonpos_of_splits
            $hf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (by
              intro r hroot
              have hroot_nonpos : r ≤ 0 := $hroot_nonpos r hroot
              rr_sign))
  | `(tactic|
      rr_mw_derivative_sign_root_upper using
        splits := $hf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_upper := $hroot_upper:term) =>
      `(tactic|
        exact
          RealRooted.MaWang.strictInterl_derivative_of_nonpos_of_splits
            $hf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (by
              intro r hroot
              have hroot_upper := $hroot_upper r hroot
              rr_sign))
  | `(tactic|
      rr_mw_derivative_sign_window using
        splits := $hf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term) =>
      `(tactic|
        exact
          RealRooted.MaWang.strictInterl_derivative_of_nonpos_of_splits
            $hf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (by
              intro r hroot
              have hroot_lower := $hroot_lower r hroot
              have hroot_upper := $hroot_upper r hroot
              rr_sign))
  | `(tactic|
      rr_mw_derivative_one_add_two_window_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.MaWang.strictInterl_derivative_one_add_X_mul_one_add_two_mul_X_sequence
            $hbase $hpos $hroot_lo $hroot_hi $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_one_add_two_window_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_one_add_two_window_sequence using
          base := $hbase,
          pos_lc := $hpos,
          root_lower := $hroot_lo,
          root_upper := $hroot_hi,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)


end Tactic
end RealRooted
