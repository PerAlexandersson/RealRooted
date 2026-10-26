module

import RealRooted.Applications.OEIS.A297191
import RealRooted.Applications.OEIS.A304330
import RealRooted.Applications.OEIS.A304334
import RealRooted.Applications.OEIS.A318107
import RealRooted.Applications.OEIS.A318397
import RealRooted.Applications.OEIS.A359363
import RealRooted.Applications.OEIS.A367177
import RealRooted.Applications.OEIS.A394446
import RealRooted.Applications.OEIS.A394813
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

example : type_of% @RealRooted.Applications.OEIS.A297191.splits_polynomial := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A297191.strictInterl_gammaPolynomial_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A297191.strictInterl_gammaPolynomial_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A297191.strictInterl_halfStep_polynomial_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A297191.strictInterl_halfStep_polynomial_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A297191.strictInterl_polynomial_halfStep := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A297191.strictInterl_polynomial_halfStep := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A297191.strictInterl_polynomial_two_step := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A297191.strictInterl_polynomial_two_step := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A304330.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A304330.polynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A304330.polynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A304330.qPolynomial_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A304330.qPolynomial_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A304330.splits_of_recurrence := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A304334.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A318107.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A318107.natDegree_of_recurrence := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A318107.polynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A318107.polynomial_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A318107.polynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A318107.polynomial_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A318107.polynomial_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A318107.primitivePolynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A318107.splits_of_recurrence := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A318397.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A318397.polynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A318397.polynomial_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A318397.polynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A318397.polynomial_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A318397.polynomial_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A318397.splits_of_recurrence := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A359363.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A359363.polynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A359363.polynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A359363.polynomial_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A359363.polynomial_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A359363.splits_of_recurrence := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A367177.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A367177.polynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A367177.polynomial_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A367177.polynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A367177.polynomial_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A367177.polynomial_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A367177.splits_of_recurrence := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A394446.splits_polynomial := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A394813.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A394813.polynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A394813.polynomial_natDegree := by
  intros
  rr_row_natDegree

end RealRooted.TacticProbe
