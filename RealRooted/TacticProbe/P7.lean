module

import RealRooted.Applications.BinderVecchi.UniformMatroid
import RealRooted.Applications.OEIS.ClosedFormRows
import RealRooted.Applications.OEIS.CubicParentRows
import RealRooted.Applications.PeakPolynomials.HitPolynomials
import RealRooted.Applications.PeakPolynomials.PeakInduction
import RealRooted.Tactic.RowInterlacing
import RealRooted.Tactic.Recurrence

/-! Scratch tactic probe (issue #2042); not part of the library. -/

open Polynomial

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.longLine false
-- the heartbeat budget is per example; failed alternatives inside  consume it
set_option maxHeartbeats 800000

namespace RealRooted.TacticProbe

set_option rr.row.explain true

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_nextBoundary_A_last_W_last := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_nextBoundary_D_last_D_castSucc := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_nextBoundary_D_last_U_castSucc := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_next_A_A_of_lt := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_next_A_W := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_next_D_D_of_lt := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_next_D_U := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_next_U_U_of_le := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_next_W_W_of_le := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_sum_D_P := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.isRealRooted_P := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.splits_P := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.splits_S := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.splits_T := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.splits_next_A := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.splits_next_W := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.IsReachable.isRealRooted_P := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.exists_next_W_sub_next_A_eq_mul := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.hasNonnegCoeffs_A := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.hasNonnegCoeffs_P := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.hasNonnegCoeffs_S := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.hasNonnegCoeffs_T := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.hasNonnegCoeffs_W := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.PeakPolynomials.interl_add_X_sub_C_one_mul := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.interl_hit_update_succ := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.splits_hit_of_cover_of_du := by
  intros
  rr_row_splits

example : type_of% @RealRooted.BinderVecchi.isRealRooted_modifiedAugmentedHodgePoincare := by
  intros
  rr_row_splits

example : type_of% @RealRooted.BinderVecchi.isRealRooted_refinedHodgePoincare := by
  intros
  rr_row_splits

example : type_of% @RealRooted.BinderVecchi.modifiedAugmentedHodgePoincare_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.BinderVecchi.natDegree_eulerian_le := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.BinderVecchi.refinedHodgePoincare_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.ClosedFormRows.A100898_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.ClosedFormRows.A110200_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.ClosedFormRows.A124376_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.ClosedFormRows.A157169_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.ClosedFormRows.A157171_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.ClosedFormRows.A286100_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.CubicParentRows.a114123_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.CubicParentRows.a184883_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.CubicParentRows.a216182_splits := by
  intros
  rr_row_splits

end RealRooted.TacticProbe
