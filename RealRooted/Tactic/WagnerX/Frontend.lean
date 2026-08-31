import RealRooted.Tactic.WagnerX.Syntax

/-!
# Wagner `X`-shift tactic frontend
-/

open Polynomial

namespace RealRooted
namespace Tactic

macro_rules
  -- Each conclusion fixes its hidden polynomial and scalar parameters first.
  | `(tactic|
      rr_prec_mul_X using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term) =>
      `(tactic|
        exact RealRooted.prec_mul_X_of_prec_of_nonneg $hprec $hfnn $hgnn)
  | `(tactic| rr_prec_mul_X) =>
      `(tactic|
        exact (by
          apply RealRooted.prec_mul_X_of_prec_of_nonneg
          case h => rr_lookup [rr_base_prec]
          case hfnn => rr_lookup [rr_nonneg]
          case hgnn => rr_lookup [rr_nonneg]))
  | `(tactic|
      rr_prec_mul_X_both using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term) =>
      `(tactic|
        exact RealRooted.prec_mul_X_both_of_prec_of_nonneg $hprec $hfnn $hgnn)
  | `(tactic| rr_prec_mul_X_both) =>
      `(tactic|
        exact (by
          apply RealRooted.prec_mul_X_both_of_prec_of_nonneg
          case h => rr_lookup [rr_base_prec]
          case hfnn => rr_lookup [rr_nonneg]
          case hgnn => rr_lookup [rr_nonneg]))
  | `(tactic|
      rr_prec_C_mul_X using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term,
        coeff_ne := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_C_mul_X_of_prec_of_nonneg $hprec $hfnn $hgnn $hc)
  | `(tactic|
      rr_prec_C_mul_X using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term,
        coeff_pos := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_C_mul_X_of_prec_of_nonneg
          $hprec $hfnn $hgnn ($hc).ne')
  | `(tactic|
      rr_prec_C_mul_X using
        coeff_ne := $hc:term) =>
      `(tactic|
        exact (by
          apply RealRooted.prec_C_mul_X_of_prec_of_nonneg
          case h => rr_lookup [rr_base_prec]
          case hfnn => rr_lookup [rr_nonneg]
          case hgnn => rr_lookup [rr_nonneg]
          case hc => exact $hc))
  | `(tactic|
      rr_prec_C_mul_X using
        coeff_pos := $hc:term) =>
      `(tactic|
        exact (by
          apply RealRooted.prec_C_mul_X_of_prec_of_nonneg
          case h => rr_lookup [rr_base_prec]
          case hfnn => rr_lookup [rr_nonneg]
          case hgnn => rr_lookup [rr_nonneg]
          case hc => exact ($hc).ne'))
  | `(tactic|
      rr_prec_X_derivative_X_self using
        splits := $hf:term,
        degree_two := $hdeg:term,
        nonneg_coeffs := $hfnn:term) =>
      `(tactic|
        exact RealRooted.prec_X_mul_derivative_X_mul_self_of_splits_nonneg
          $hf $hdeg $hfnn)
  | `(tactic| rr_prec_X_derivative_X_self) =>
      `(tactic|
        exact (by
          apply RealRooted.prec_X_mul_derivative_X_mul_self_of_splits_nonneg
          case hf => rr_lookup
          case hdeg => rr_lookup [rr_degree]
          case hfnn => rr_lookup [rr_nonneg]))
  | `(tactic|
      rr_prec_wagner_derivative_gap_lag using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_wagner_derivative_gap_lag_step
          $hprec $hfnn $hgnn $hdeg $ha $hc)
  | `(tactic| rr_prec_wagner_derivative_gap_lag) =>
      `(tactic|
        exact (by
          apply RealRooted.prec_wagner_derivative_gap_lag_step
          case h => rr_lookup [rr_base_prec]
          case hfnn => rr_lookup [rr_nonneg]
          case hgnn => rr_lookup [rr_nonneg]
          case hdeg => rr_lookup [rr_degree]
          case ha => first | rr_lookup | rr_wagner_pos
          case hc => first | rr_lookup | rr_wagner_pos))
  | `(tactic|
      rr_prec_wagner_derivative_gap_lag_den using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term,
        denom_pos := $hd:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.prec_wagner_derivative_gap_lag_step_den
          $hprec $hfnn $hgnn $hdeg $ha $hc $hd $hrec)
  | `(tactic|
      rr_prec_wagner_derivative_gap_lag_sequence using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.prec_wagner_derivative_gap_lag_sequence
          $hbase $hnonneg $hdeg $ha $hc $hrec)
  | `(tactic|
      rr_prec_wagner_derivative_gap_lag_sequence_realrooted using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_wagner_derivative_gap_lag_sequence
            $hbase $hnonneg $hdeg $ha $hc $hrec))
  | `(tactic|
      rr_prec_wagner_derivative_gap_lag_sequence_den using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term,
        denom_pos := $hd:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.prec_wagner_derivative_gap_lag_sequence_den
          $hbase $hnonneg $hdeg $ha $hc $hd $hrec)
  | `(tactic|
      rr_prec_wagner_derivative_gap_lag_sequence_den_realrooted using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term,
        denom_pos := $hd:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_wagner_derivative_gap_lag_sequence_den
            $hbase $hnonneg $hdeg $ha $hc $hd $hrec))
  | `(tactic|
      rr_natDegree_pos_X_lag_sequence using
        base_zero := $hzero:term,
        base_one := $hone:term,
        current_coeff_pos := $ha:term,
        lag_coeff_pos := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        simpa using
          (RealRooted.natDegree_pos_X_lag_combo_sequence
            $hzero $hone $ha $hc $hrec))
  | `(tactic|
      rr_natDegree_pos_X_lag_sequence_shifted using
        base_zero := $hzero:term,
        base_one := $hone:term,
        current_coeff_pos := $ha:term,
        lag_coeff_pos := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        simpa using
          (RealRooted.natDegree_pos_X_lag_combo_sequence_shifted
            $hzero $hone $ha $hc $hrec))
  | `(tactic|
      rr_prec_pos_X_lag_combo using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term,
        current_coeff_pos := $ha:term,
        lag_coeff_nonneg := $hc:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_add_assoc
          (RealRooted.prec_pos_X_lag_combo_of_prec_nonneg
            $hprec $hfnn $hgnn $ha $hc),
          (RealRooted.prec_pos_X_lag_combo_of_prec_nonneg
            $hprec $hfnn $hgnn $ha $hc))
  | `(tactic|
      rr_prec_pos_X_lag_combo using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term,
        current_coeff_pos := $ha:term,
        lag_coeff_pos := $hc:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_add_assoc
          (RealRooted.prec_pos_X_lag_combo_of_prec_nonneg
            $hprec $hfnn $hgnn $ha ($hc).le),
          (RealRooted.prec_pos_X_lag_combo_of_prec_nonneg
            $hprec $hfnn $hgnn $ha ($hc).le))
  | `(tactic|
      rr_prec_pos_X_lag_sequence using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        current_coeff_pos := $ha:term,
        lag_coeff_nonneg := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.prec_pos_X_lag_combo_sequence
          $hbase $hnonneg $ha $hc $hrec)
  | `(tactic|
      rr_prec_pos_X_lag_sequence_auto using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_first_exact
          (RealRooted.prec_pos_X_lag_combo_sequence
            $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq $hrec),
          (RealRooted.prec_pos_X_lag_combo_sequence
              (a := fun _ => (1 : ℝ)) (c := fun _ => (1 : ℝ))
              $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq
              (rr_wagner_recurrence_seq $hrec)))
  | `(tactic|
      rr_prec_pos_X_lag_coeff_sequence_auto using
        current_coeff := $a:term,
        lag_coeff := $c:term,
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.prec_pos_X_lag_combo_sequence
          (a := $a) (c := $c)
          $hbase $hnonneg rr_side_pos_seq_term rr_side_nonneg_seq_term
          (rr_wagner_recurrence_seq $hrec))
  | `(tactic|
      rr_prec_pos_X_lag_sequence_realrooted using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        current_coeff_pos := $ha:term,
        lag_coeff_nonneg := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_pos_X_lag_combo_sequence
            $hbase $hnonneg $ha $hc $hrec))
  | `(tactic|
      rr_prec_pos_X_lag_sequence_realrooted_auto using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_pos_X_lag_combo_sequence
            $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq $hrec),
          (RealRooted.isRealRooted_of_prec_pos_X_lag_combo_sequence
            (a := fun _ => (1 : ℝ)) (c := fun _ => (1 : ℝ))
            $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq
            (rr_wagner_recurrence_seq $hrec)))
  | `(tactic|
      rr_prec_pos_X_lag_coeff_sequence_realrooted_auto using
        current_coeff := $a:term,
        lag_coeff := $c:term,
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_pos_X_lag_combo_sequence
            (a := $a) (c := $c)
            $hbase $hnonneg rr_side_pos_seq_term rr_side_nonneg_seq_term
            (rr_wagner_recurrence_seq $hrec)))
  | `(tactic|
      rr_natDegree_pos_X_sub_C_lag_sequence using
        shift := $r:term,
        base_zero := $hzero:term,
        base_one := $hone:term,
        current_coeff_pos := $ha:term,
        lag_coeff_pos := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        simpa using
          (RealRooted.natDegree_pos_X_sub_C_lag_combo_sequence
            (r := $r) $hzero $hone $ha $hc $hrec))
  | `(tactic|
      rr_natDegree_pos_X_sub_C_lag_sequence_shifted using
        shift := $r:term,
        base_zero := $hzero:term,
        base_one := $hone:term,
        current_coeff_pos := $ha:term,
        lag_coeff_pos := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        simpa using
          (RealRooted.natDegree_pos_X_sub_C_lag_combo_sequence_shifted
            (r := $r) $hzero $hone $ha $hc $hrec))
  | `(tactic|
      rr_prec_pos_X_sub_C_lag_sequence using
        shift := $r:term,
        base := $hbase:term,
        shift_nonneg_coeffs := $hnonneg:term,
        current_coeff_pos := $ha:term,
        lag_coeff_nonneg := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.prec_pos_X_sub_C_lag_combo_sequence
          (r := $r) $hbase $hnonneg $ha $hc $hrec)
  | `(tactic|
      rr_prec_pos_X_sub_C_lag_sequence_realrooted using
        shift := $r:term,
        base := $hbase:term,
        shift_nonneg_coeffs := $hnonneg:term,
        current_coeff_pos := $ha:term,
        lag_coeff_nonneg := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_pos_X_sub_C_lag_combo_sequence
            (r := $r) $hbase $hnonneg $ha $hc $hrec))
  | `(tactic|
      rr_prec_pos_X_sub_C_lag_sequence_realrooted_auto using
        shift := $r:term,
        base := $hbase:term,
        shift_nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_pos_X_sub_C_lag_combo_sequence
            (r := $r) $hbase $hnonneg
            rr_wagner_pos_seq rr_wagner_pos_seq $hrec))
  | `(tactic|
      rr_prec_pos_X_unit_lag_sequence_auto using
        current_coeff := $a:term,
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.prec_pos_X_lag_combo_sequence
          (a := $a) (c := fun _ => (1 : ℝ))
          $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq
          (rr_wagner_recurrence_seq $hrec))
  | `(tactic|
      rr_prec_pos_X_unit_lag_sequence_realrooted_auto using
        current_coeff := $a:term,
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_pos_X_lag_combo_sequence
            (a := $a) (c := fun _ => (1 : ℝ))
            $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq
            (rr_wagner_recurrence_seq $hrec)))
  | `(tactic|
      rr_prec_pos_X_same_coeff_sequence_auto using
        shared_coeff := $c:term,
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.prec_pos_X_lag_combo_sequence
          (a := $c) (c := $c)
          $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq
          (rr_wagner_recurrence_seq $hrec))
  | `(tactic|
      rr_prec_pos_X_same_coeff_sequence_realrooted_auto using
        shared_coeff := $c:term,
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_pos_X_lag_combo_sequence
            (a := $c) (c := $c)
            $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq
            (rr_wagner_recurrence_seq $hrec)))



end Tactic
end RealRooted
