import RealRooted.Tactic.Favard.RowSignSyntax
import RealRooted.Tactic.Favard.Denominator

/-!
# Favard tactic row-sign rules

Macro rules for row-sign-normalized affine Favard certificates.
-/

namespace RealRooted
namespace Tactic

macro_rules
  | `(tactic|
      rr_favard_affine_param_row_sign using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep))
  | `(tactic|
      rr_favard_affine_param_row_sign_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
  | `(tactic|
      rr_favard_affine_param_row_sign_den using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_goal_variant_alternatives3
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign_den
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw));
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_split
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_split
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_split
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw));
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_split_rev
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_split_rev
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_split_rev
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)))
  | `(tactic|
      rr_favard_affine_param_row_sign_den_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := $hs,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw))
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_auto using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_prod using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_prod using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope_left := $aleft,
          raw_slope_right := $aright,
          raw_const := $braw,
          raw_lag_left := $cleft,
          raw_lag_right := $cright,
          slope_pos := $hs,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_prod using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_raw_prod
            (s := $s) (α := $α) (β := $β) (d := $d)
            (aleft := $aleft) (aright := $aright) (braw := $braw)
            (cleft := $cleft) (cright := $cright)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw_prod
            (s := $s) (α := $α) (β := $β) (d := $d)
            (aleft := $aleft) (aright := $aright) (braw := $braw)
            (cleft := $cleft) (cright := $cright)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_raw_prod
            (s := $s) (α := $α) (β := $β) (d := $d)
            (aleft := $aleft) (aright := $aright) (braw := $braw)
            (cleft := $cleft) (cright := $cright)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw))
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_prod_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_prod_auto using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope_left := $aleft,
          raw_slope_right := $aright,
          raw_const := $braw,
          raw_lag_left := $cleft,
          raw_lag_right := $cright,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_prod_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_prod using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope_left := $aleft,
          raw_slope_right := $aright,
          raw_const := $braw,
          raw_lag_left := $cleft,
          raw_lag_right := $cright,
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_unit using
        slope := $s:term,
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        slope_pos := $hs:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := $hs,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_unit using
        slope := $s:term,
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_unit using
          slope := $s,
          alpha := $α,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_unit using
        slope := $s:term,
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_auto using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_raw using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_row_sign_den_raw using
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_raw using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := rr_positivity_seq_term,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_raw_auto using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_row_sign_den_raw_auto using
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_raw_auto using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_row_sign_den_raw using
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_raw_unit using
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_row_sign_den_raw_unit using
          alpha := $α,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_raw_unit using
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_unit using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_unit using
        slope := $s:term,
        alpha := $α:term,
        slope_pos := $hs:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          slope_pos := $hs,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_unit using
        slope := $s:term,
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_auto using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den using
        alpha := $α:term,
        beta := $β:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_seq_term,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_auto using
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_row_sign_den using
          alpha := $α,
          beta := $β,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_unit using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_unit using
        slope := $s:term,
        alpha := $α:term,
        slope_pos := $hs:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          slope_pos := $hs,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
  | `(tactic|
      rr_favard_affine_param_row_sign_unit using
        slope := $s:term,
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_auto using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_param_row_sign_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_unit using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_param_row_sign using
        alpha := $α:term,
        beta := $β:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_seq_term,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
  | `(tactic|
      rr_favard_param_row_sign_auto using
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_param_row_sign using
          alpha := $α,
          beta := $β,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)

end Tactic
end RealRooted
