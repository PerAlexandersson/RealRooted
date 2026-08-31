import RealRooted.Tactic.Favard.RowSignSyntax

/-!
# Favard tactic direct rules

Macro rules for direct monic and positive-slope affine Favard certificates.
-/

namespace RealRooted
namespace Tactic

macro_rules
  | `(tactic| rr_favard) =>
      `(tactic|
        rr_favard using
          recurrence := (by assumption),
          beta_pos := (by assumption))
  | `(tactic| rr_favard_auto) =>
      `(tactic|
        rr_favard_auto using
          recurrence := (by assumption))
  | `(tactic| rr_favard using $hrec:term, $hbeta:term) =>
      `(tactic|
        first
          | exact RealRooted.favardInterlacing $hrec $hbeta
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard $hrec $hbeta)
          | exact RealRooted.nonzero_of_favard $hrec $hbeta
          | exact RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
              $hrec $hbeta
          | exact RealRooted.favardInterlacing $hrec $hbeta _
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard $hrec $hbeta _)
          | exact RealRooted.nonzero_of_favard $hrec $hbeta _
          | exact RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
              $hrec $hbeta _)
  | `(tactic|
      rr_favard using
        recurrence := $hrec:term,
        beta_pos := $hbeta:term) =>
      `(tactic|
        rr_favard using $hrec, $hbeta)
  | `(tactic|
      rr_favard_auto using
        recurrence := $hrec:term) =>
      `(tactic|
        first
          | rr_favard_refine_positivity_seq
              (RealRooted.favardInterlacing $hrec ?_)
          | rr_favard_exact_realrooted_positivity_seq
              (RealRooted.isRealRooted_of_favard $hrec ?_)
          | rr_favard_refine_positivity_seq
              (RealRooted.nonzero_of_favard $hrec ?_)
          | rr_favard_refine_positivity_seq
              (RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
                $hrec ?_)
          | rr_favard_refine_positivity_seq
              (RealRooted.favardInterlacing $hrec ?_ _)
          | rr_favard_exact_realrooted_positivity_seq
              (RealRooted.isRealRooted_of_favard $hrec ?_ _)
          | rr_favard_refine_positivity_seq
              (RealRooted.nonzero_of_favard $hrec ?_ _)
          | rr_favard_refine_positivity_seq
              (RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
                $hrec ?_ _))
  | `(tactic|
      rr_favard_const using
        $α:term, $β:term, $hβ:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_const_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_const_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_const_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep))
  | `(tactic|
      rr_favard_const using
        alpha := $α:term,
        beta := $β:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_const using $α, $β, $hβ, $hP0, $hP1, $hstep)
  | `(tactic|
      rr_favard_const_auto using
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_const using
          alpha := $α,
          beta := $β,
          beta_pos := rr_positivity_term,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_const_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_const_auto using
          alpha := $α,
          beta := 1,
          base_zero := $hP0,
          base_one := rr_favard_base_one $hP1,
          step := rr_favard_step_seq $hstep)
  | `(tactic|
      rr_favard_const_unit using
        $α:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_const_unit using
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_param using
        $α:term, $β:term, $hβ:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_param_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_param_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_param_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep))
  | `(tactic|
      rr_favard_param using
        alpha := $α:term,
        beta := $β:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_param using $α, $β, $hβ, $hP0, $hP1, $hstep)
  | `(tactic|
      rr_favard_param_auto using
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_param using
          alpha := $α,
          beta := $β,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
  | `(tactic|
      rr_favard_param_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_param_auto using
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_param_unit using
        $α:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_param_unit using
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_affine_const using
        $s:term, $α:term, $β:term, $hs:term, $hβ:term, $hP0:term, $hP1:term,
        $hstep:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_const_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_affine_const_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_affine_const_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep))
  | `(tactic|
      rr_favard_affine_const using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_const using
          $s, $α, $β, $hs, $hβ, $hP0, $hP1, $hstep)
  | `(tactic|
      rr_favard_affine_const_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_const using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_term,
          beta_pos := rr_positivity_term,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_affine_const_unit using
        slope := $s:term,
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_const_auto using
          slope := $s,
          alpha := $α,
          beta := 1,
          base_zero := $hP0,
          base_one := rr_favard_base_one $hP1,
          step := rr_favard_step_seq $hstep)
  | `(tactic|
      rr_favard_affine_const_unit using
        $s:term, $α:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_affine_const_unit using
          slope := $s,
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_affine_const_row_sign using
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
          (RealRooted.favardInterlacing_affine_const_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_affine_const_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_affine_const_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep))
  | `(tactic|
      rr_favard_affine_const_row_sign_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_const_row_sign using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_term,
          beta_pos := rr_positivity_term,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_const_row_sign_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_const_row_sign_auto using
          slope := 1,
          alpha := $α,
          beta := 1,
          base_zero := $hP0,
          base_one := rr_favard_base_one $hP1,
          step := rr_favard_step_seq $hstep)
  | `(tactic|
      rr_favard_const_row_sign_unit using
        $α:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_const_row_sign_unit using
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_affine_param_infer using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        step := $hstep:term) =>
      `(tactic|
        first
          | rr_favard_affine_param using
              slope := $s,
              alpha := $α,
              beta := $β,
              slope_pos := rr_favard_positive_lookup_term,
              beta_pos := rr_favard_positive_lookup_term,
              base_zero := rr_favard_base_lookup_term,
              base_one := rr_favard_base_lookup_term,
              step := rr_favard_step_dsimp_seq $hstep
          | rr_favard_affine_param_row_sign using
              slope := $s,
              alpha := $α,
              beta := $β,
              slope_pos := rr_favard_positive_lookup_term,
              beta_pos := rr_favard_positive_lookup_term,
              base_zero := rr_favard_base_lookup_term,
              base_one := rr_favard_base_lookup_term,
              step := rr_favard_step_dsimp_seq $hstep)
  | `(tactic|
      rr_favard_affine_param using
        $s:term, $α:term, $β:term, $hs:term, $hβ:term, $hP0:term, $hP1:term,
        $hstep:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.interlaces_of_favard_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.favardInterlacing_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.interlaces_of_favard_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _),
          (RealRooted.favardInterlacing_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _),
          (RealRooted.nonzero_of_favard_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _))
  | `(tactic|
      rr_favard_affine_param using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param using $s, $α, $β, $hs, $hβ, $hP0, $hP1, $hstep)
  | `(tactic|
      rr_favard_affine_param_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)

end Tactic
end RealRooted
