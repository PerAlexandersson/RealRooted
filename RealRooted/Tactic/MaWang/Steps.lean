import RealRooted.Tactic.MaWang.FactorSyntax

/-!
# Ma--Wang tactic step rules

Elaboration rules for the one-step and short-window certificates.
-/

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
  | `(tactic| rr_mw_two_variants $hleft:term, $hright:term) =>
      `(tactic|
        rr_first_exact_then_realrooted_sequence_or_projection $hleft, $hright)
  | `(tactic|
      rr_mw_three_variants $hleft:term, $hmiddle:term, $hright:term) =>
      `(tactic|
        rr_first_exact_then_realrooted_sequence_or_projection $hleft, $hmiddle, $hright)
  | `(tactic| rr_ma_wang) =>
      `(tactic|
        rr_ma_wang using
          splits := (by rr_lookup),
          degree_two := (by rr_lookup [rr_degree]),
          degree_lower := (by rr_lookup [rr_degree]),
          degree_upper := (by rr_lookup [rr_degree]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          root_sign := (by rr_lookup))
  | `(tactic| rr_ma_wang_same) =>
      `(tactic|
        rr_ma_wang_same using
          splits := (by rr_lookup),
          degree_two := (by rr_lookup [rr_degree]),
          degree := (by rr_lookup [rr_degree]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          root_sign := (by rr_lookup))
  | `(tactic| rr_ma_wang_succ) =>
      `(tactic|
        rr_ma_wang_succ using
          splits := (by rr_lookup),
          degree_two := (by rr_lookup [rr_degree]),
          degree := (by rr_lookup [rr_degree]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          root_sign := (by rr_lookup))
  | `(tactic|
      rr_ma_wang using
        $hf:term, $hdegf:term, $hdeg_lo:term, $hdeg_hi:term, $hF_pos:term,
        $hf_pos:term, $hroot_sign:term) =>
      `(tactic|
        exact RealRooted.prec_ma_wang
          $hf (le_trans (by norm_num : (1 : ℕ) ≤ 2) $hdegf)
          $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hroot_sign)
  | `(tactic|
      rr_ma_wang using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_sign := $hroot_sign:term) =>
      `(tactic|
        rr_ma_wang using
          $hf, $hdegf, $hdeg_lo, $hdeg_hi, $hF_pos, $hf_pos, $hroot_sign)
  | `(tactic|
      rr_ma_wang_same using
        $hf:term, $hdegf:term, $hdeg:term, $hF_pos:term, $hf_pos:term,
        $hroot_sign:term) =>
      `(tactic|
        exact RealRooted.prec_ma_wang_same
          $hf (le_trans (by norm_num : (1 : ℕ) ≤ 2) $hdegf)
          $hdeg $hF_pos $hf_pos $hroot_sign)
  | `(tactic|
      rr_ma_wang_same using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree := $hdeg:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_sign := $hroot_sign:term) =>
      `(tactic|
        rr_ma_wang_same using $hf, $hdegf, $hdeg, $hF_pos, $hf_pos, $hroot_sign)
  | `(tactic|
      rr_ma_wang_succ using
        $hf:term, $hdegf:term, $hdeg:term, $hF_pos:term, $hf_pos:term,
        $hroot_sign:term) =>
      `(tactic|
        exact RealRooted.prec_ma_wang_succ
          $hf (le_trans (by norm_num : (1 : ℕ) ≤ 2) $hdegf)
          $hdeg $hF_pos $hf_pos $hroot_sign)
  | `(tactic|
      rr_ma_wang_succ using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree := $hdeg:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_sign := $hroot_sign:term) =>
      `(tactic|
        rr_ma_wang_succ using $hf, $hdegf, $hdeg, $hF_pos, $hf_pos, $hroot_sign)
  | `(tactic|
      rr_prec_evalCoeff_nonpos using
        interlaces := $hgf:term,
        source_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        coeff_nonpos := $hb_nonpos:term) =>
      `(tactic|
        exact RealRooted.prec_of_interlaces_evalCoeff_nonpos
          $hgf $hg_pos $hF_pos $hdeg_lo $hdeg_hi $hb_nonpos)
  | `(tactic|
      rr_prec_evalCoeff_nonpos using
        interlaces := $hgf:term,
        source_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree := $hdeg:term,
        coeff_nonpos := $hb_nonpos:term) =>
      `(tactic|
        rr_prec_evalCoeff_nonpos using
          interlaces := $hgf,
          source_pos_lc := $hg_pos,
          target_pos_lc := $hF_pos,
          degree_lower := (by rr_mw_degree_from $hdeg),
          degree_upper := (by rr_mw_degree_from $hdeg),
          coeff_nonpos := $hb_nonpos)
  | `(tactic| rr_prec_evalCoeff_nonpos) =>
      `(tactic|
        rr_prec_evalCoeff_nonpos using
          interlaces := (by rr_lookup),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          degree_lower := (by rr_lookup [rr_degree]),
          degree_upper := (by rr_lookup [rr_degree]),
          coeff_nonpos := (by rr_lookup))
  | `(tactic| rr_prec_evalCoeff_nonpos using degree := $hdeg:term) =>
      `(tactic|
        rr_prec_evalCoeff_nonpos using
          interlaces := (by rr_lookup),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          degree := $hdeg,
          coeff_nonpos := (by rr_lookup))
  | `(tactic|
      rr_mw_derivative_nonpos_step using
        splits := $hf:term,
        degree_two := $hdegf:term,
        target_pos_lc := $hF_pos:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonpos := $hv_nonpos:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_of_nonpos_of_recurrence
          $hf $hdegf $hrec $hF_pos $hdeg_lo $hdeg_hi $hf_pos $hv_nonpos)
  | `(tactic| rr_mw_derivative_nonpos_step using recurrence := $hrec:term) =>
      `(tactic|
        rr_refine_then
          (RealRooted.prec_mw_derivative_of_nonpos_of_recurrence
            ?_ ?_ $hrec ?_ ?_ ?_ ?_ ?_)
          with rr_lookup)
  | `(tactic|
      rr_mw_derivative_nonpos using
        $hf:term, $hdegf:term, $hdeg_lo:term, $hdeg_hi:term, $hF_pos:term,
        $hf_pos:term, $hv_nonpos:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_of_nonpos
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hv_nonpos)
  | `(tactic|
      rr_mw_derivative_nonpos using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonpos := $hv_nonpos:term) =>
      `(tactic|
        rr_mw_derivative_nonpos using
          $hf, $hdegf, $hdeg_lo, $hdeg_hi, $hF_pos, $hf_pos, $hv_nonpos)
  | `(tactic|
      rr_mw_derivative_nonpos using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree := $hdeg:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonpos := $hv_nonpos:term) =>
      `(tactic|
        rr_mw_derivative_nonpos using
          splits := $hf,
          degree_two := $hdegf,
          degree_lower := (by rr_mw_degree_from $hdeg),
          degree_upper := (by rr_mw_degree_from $hdeg),
          target_pos_lc := $hF_pos,
          source_pos_lc := $hf_pos,
          coeff_nonpos := $hv_nonpos)
  | `(tactic| rr_mw_derivative_nonpos) =>
      `(tactic|
        rr_mw_derivative_nonpos using
          splits := (by rr_lookup),
          degree_two := (by rr_lookup [rr_degree]),
          degree_lower := (by rr_lookup [rr_degree]),
          degree_upper := (by rr_lookup [rr_degree]),
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          coeff_nonpos := (by rr_lookup))
  | `(tactic| rr_mw_derivative_nonpos using degree := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_nonpos using
          splits := (by rr_lookup),
          degree_two := (by rr_lookup [rr_degree]),
          degree := $hdeg,
          target_pos_lc := (by rr_lookup [rr_pos_lc]),
          source_pos_lc := (by rr_lookup [rr_pos_lc]),
          coeff_nonpos := (by rr_lookup))
  | `(tactic|
      rr_mw_derivative_sign_roots_nonpos using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        roots_nonpos := $hroot_nonpos:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_of_nonpos
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (by
              intro r hroot
              have hroot_nonpos : r ≤ 0 := $hroot_nonpos r hroot
              rr_sign))
  | `(tactic|
      rr_mw_derivative_sign_nonneg_coeffs using
        realrooted := $hrr:term,
        nonneg := $hnn:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_of_nonpos
            ($hrr).2 $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (rr_sign_at_roots_term $hrr, $hnn))
  | `(tactic|
      rr_mw_derivative_sign_nonneg_factor using
        realrooted := $hrr:term,
        nonneg := $hnn:term,
        factor_nonneg := $hfactor:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_of_nonpos
            ($hrr).2 $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (rr_sign_at_roots_factor_term $hrr, $hnn, $hfactor))
  | `(tactic|
      rr_mw_derivative_sign_root_upper using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_upper := $hroot_upper:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_of_nonpos
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (by
              intro r hroot
              have hroot_upper := $hroot_upper r hroot
              rr_sign))
  | `(tactic|
      rr_mw_derivative_sign_window using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_lower := $hroot_lower:term,
        root_upper := $hroot_upper:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_of_nonpos
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos
            (by
              intro r hroot
              have hroot_lower := $hroot_lower r hroot
              have hroot_upper := $hroot_upper r hroot
              rr_sign))
  | `(tactic|
      rr_mw_derivative_X_mul using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        roots_nonpos := $hf_roots:term,
        factor_nonneg := $hq_nonneg:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_X_mul_of_nonneg_on_roots
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hf_roots $hq_nonneg)
  | `(tactic|
      rr_mw_derivative_C_mul_X_mul using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonneg := $hc:term,
        roots_nonpos := $hf_roots:term,
        factor_nonneg := $hq_nonneg:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_C_mul_X_mul_of_nonneg_on_roots
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hc $hf_roots $hq_nonneg)
  | `(tactic|
      rr_mw_derivative_X_one_add_window using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term) =>
      `(tactic|
        exact RealRooted.prec_mw_derivative_X_mul_one_add_X_of_roots_in_Icc
          $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hroot_lo $hroot_hi)
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        coeff_nonneg := $hc:term,
        root_upper := $hroot_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_neg_C_mul_X_mul_one_add_X_of_roots_le_neg_one
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hc $hroot_hi)
  | `(tactic|
      rr_mw_derivative_neg_X_one_add_outer_auto using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_upper := $hroot_hi:term) =>
      `(tactic|
        rr_refine_then
          (RealRooted.prec_mw_derivative_neg_C_mul_X_mul_one_add_X_of_roots_le_neg_one
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos ?_ $hroot_hi)
          with rr_mw_active_nonneg_at 0)
  | `(tactic|
      rr_mw_derivative_one_add_two_window using
        splits := $hf:term,
        degree_two := $hdegf:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        target_pos_lc := $hF_pos:term,
        source_pos_lc := $hf_pos:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_one_add_X_mul_one_add_two_mul_X_of_roots_in_interval
            $hf $hdegf $hdeg_lo $hdeg_hi $hF_pos $hf_pos $hroot_lo $hroot_hi)
  | `(tactic|
      rr_mw_derivative_one_add_two_window_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        exact
          RealRooted.prec_mw_derivative_one_add_X_mul_one_add_two_mul_X_sequence
            $hbase $hpos $hdeg_two $hroot_lo $hroot_hi $hrec $hdeg_lo $hdeg_hi)
  | `(tactic|
      rr_mw_derivative_one_add_two_window_sequence using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_one_add_two_window_sequence using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          root_lower := $hroot_lo,
          root_upper := $hroot_hi,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)

  | `(tactic|
      rr_mw_derivative_one_add_two_window_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term,
        recurrence := $hrec:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_mw_derivative_one_add_X_mul_one_add_two_mul_X_sequence
            $hbase $hpos $hdeg_two $hroot_lo $hroot_hi $hrec $hdeg_lo $hdeg_hi))
  | `(tactic|
      rr_mw_derivative_one_add_two_window_sequence_realrooted using
        base := $hbase:term,
        pos_lc := $hpos:term,
        degree_two := $hdeg_two:term,
        root_lower := $hroot_lo:term,
        root_upper := $hroot_hi:term,
        recurrence := $hrec:term,
        degree_succ := $hdeg:term) =>
      `(tactic|
        rr_mw_derivative_one_add_two_window_sequence_realrooted using
          base := $hbase,
          pos_lc := $hpos,
          degree_two := $hdeg_two,
          root_lower := $hroot_lo,
          root_upper := $hroot_hi,
          recurrence := $hrec,
          degree_lower := rr_mw_degree_seq $hdeg,
          degree_upper := rr_mw_degree_seq $hdeg)

end Tactic
end RealRooted
