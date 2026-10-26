module

import RealRooted.Applications.OEIS.A080721
import RealRooted.Applications.OEIS.A110608
import RealRooted.Applications.OEIS.A111910
import RealRooted.Applications.OEIS.A119308
import RealRooted.Applications.OEIS.A124848
import RealRooted.Applications.OEIS.A132166
import RealRooted.Applications.OEIS.A132885
import RealRooted.Applications.OEIS.A144438
import RealRooted.Applications.OEIS.A151775
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

example : type_of% @RealRooted.Applications.OEIS.A080721.splits_of_recurrence := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A110608.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A110608.polynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A110608.polynomial_leadingCoeff_pos := by
  intros
  rr_row_leadingCoeff_pos

example : type_of% @RealRooted.Applications.OEIS.A110608.polynomial_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A110608.polynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A110608.polynomial_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A110608.polynomial_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A110608.polynomial_strictInterl_succ_of_splits := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A110608.polynomial_strictInterl_succ_of_splits := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A110608.splits_of_recurrence := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A111910.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A111910.polynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A111910.polynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A111910.polynomial_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A111910.polynomial_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A111910.splits_of_recurrence := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A119308.A119308_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A119308.A119308_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.A119308.A119308_prec := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A119308.A119308_prec := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A119308.A119308_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A119308.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A119308.polynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A119308.polynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A119308.polynomial_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A119308.polynomial_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A119308.splits_of_recurrence := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A124848.splits_polynomial := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A132166.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A132166.polynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A132166.polynomial_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A132166.polynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A132166.polynomial_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A132166.polynomial_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A132885.hasNonnegCoeffs_polynomial := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.A132885.natDegree_polynomial := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A144438_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.A144438_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A144438_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A144438_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.A144438_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A144438_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A144438_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A151775.hasNonnegCoeffs_polynomial := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.A151775.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A151775.natDegree_polynomial := by
  intros
  rr_row_natDegree

end RealRooted.TacticProbe
