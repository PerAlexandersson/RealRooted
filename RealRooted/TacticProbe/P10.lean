module

import RealRooted.Applications.OEIS.A144696.Basic
import RealRooted.Applications.OEIS.A144696.StrictInterlacing
import RealRooted.Applications.OEIS.HarmonicDerivativeRows
import RealRooted.Applications.OEIS.TouchardImages
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

example : type_of% @RealRooted.harmonicFactorProduct_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.harmonicFactorProduct_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.harmonicFactorProduct_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.harmonicFactorProduct_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.harmonicFactorProduct_strictInterl_harmonicDerivativeRow := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.harmonicFactorProduct_strictInterl_harmonicDerivativeRow := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.hasNonnegCoeffs_a144696BernsteinImage := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.hasNonnegCoeffs_a144696Polynomial := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.hasPosLeadingCoeff_a144696BernsteinImage := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.interlaces_of_touchardDerivativeRow_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.interlaces_of_touchardEulerQuotientRow_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.leadingCoeff_a144696BernsteinImage := by
  intros
  rr_row_leadingCoeff_pos

example : type_of% @RealRooted.leadingCoeff_a144696Polynomial := by
  intros
  rr_row_leadingCoeff_pos

example : type_of% @RealRooted.natDegree_a144696BernsteinImage := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.natDegree_a144696Polynomial := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.touchardDerivativeRow_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.touchardDerivativeRow_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.touchardDerivativeRow_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.touchardDerivativeRow_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.touchardEulerQuotientRow_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.touchardEulerQuotientRow_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.touchardEulerQuotientRow_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.touchardEulerQuotientRow_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

end RealRooted.TacticProbe
