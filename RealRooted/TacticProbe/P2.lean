module

import RealRooted.Applications.OEIS.A151775
import RealRooted.Applications.OEIS.A155112
import RealRooted.Applications.OEIS.A155495
import RealRooted.Applications.OEIS.A181543
import RealRooted.Applications.OEIS.A219836
import RealRooted.Applications.OEIS.A271697
import RealRooted.Applications.OEIS.A275442
import RealRooted.Applications.OEIS.A297191
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

example : type_of% @RealRooted.Applications.OEIS.A151775.splits_polynomial := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A151775.strictInterl_polynomial_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A151775.strictInterl_polynomial_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A155112.splits_polynomial := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A155495.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A155495.polynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A155495.polynomial_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A155495.polynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A155495.polynomial_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A155495.polynomial_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A155495.splits_of_recurrence := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A181543.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A181543.polynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A181543.polynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A181543.splits_of_recurrence := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A219836.Model.natDegree_of_recurrence := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A219836.row_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A271697_interlaces_add_two := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A271697_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A271697_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A271697_strictInterl_add_two := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A271697_strictInterl_add_two := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A275442.natDegree_row := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A275442.natDegree_shiftedBridge := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A275442.natDegree_shiftedRow := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A275442.row_hasPosLeadingCoeff := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.A275442.row_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.A275442.row_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A275442.shiftedBridge_hasPosLeadingCoeff := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.A275442.shiftedRow_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.A275442.shiftedRow_hasPosLeadingCoeff := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.A275442.shiftedRow_six_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A275442.shiftedRow_six_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A275442.shiftedRow_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A275442.strictInterl_shiftedBridge_all := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A275442.strictInterl_shiftedBridge_all := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A275442.strictInterl_shiftedBridge_of_prev := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A275442.strictInterl_shiftedBridge_of_prev := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A275442.strictInterl_shiftedBridge_small := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A275442.strictInterl_shiftedBridge_small := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A275442.strictInterl_shiftedRow_last_new_of_bridge := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A275442.strictInterl_shiftedRow_last_new_of_bridge := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A275442.strictInterl_shiftedRow_partial_step := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A275442.strictInterl_shiftedRow_partial_step := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A275442.strictInterl_shiftedRow_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A275442.strictInterl_shiftedRow_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A297191.hasNonnegCoeffs_gammaPolynomial := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.A297191.hasNonnegCoeffs_polynomial := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.A297191.natDegree_gammaPolynomial := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A297191.natDegree_polynomial := by
  intros
  rr_row_natDegree

end RealRooted.TacticProbe
