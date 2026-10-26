module

import RealRooted.Applications.OEIS.A144438
import RealRooted.Applications.OEIS.A144438.BottomTotal
import RealRooted.Applications.OEIS.A144438.CodeExtension
import RealRooted.Applications.OEIS.A144438.DecorationOrbit
import RealRooted.Applications.OEIS.A144438.EligibleSupport
import RealRooted.Applications.OEIS.A144438.ExactLayer
import RealRooted.Applications.OEIS.A144438.ExceptionalHistory
import RealRooted.Applications.OEIS.A144438.FiberStability
import RealRooted.Applications.OEIS.A144438.Gamma
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.Endpoints
import RealRooted.Applications.OEIS.A144438.LayerTotalStructure
import RealRooted.Applications.OEIS.A144438.NormalizedCode
import RealRooted.Applications.OEIS.A262226
import RealRooted.Applications.OEIS.A395326
import RealRooted.Applications.OEIS.HigherOrderDegreeModels
import RealRooted.Applications.OEIS.IndispensableDigits
import RealRooted.Applications.OEIS.QuarticGamma
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

example : type_of% @RealRooted.Applications.OEIS.A395326.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A395326.polynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A395326.polynomial_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.DecoCode.last_ne_one_of_isAdmissible := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.DecoExceptionalHistory.normal_ne_exceptional := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.DecoNormalizedCode.Decoration.nonoverlap := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.DecoNormalizedCode.Eligible.leftLabel_ne_rightLabel := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.DecoNormalizedCode.eligible_ne_succ := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.DecoNormalizedCode.eligible_succ_ne := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.DecoNormalizedCode.fiberPolynomial_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.DecoNormalizedCode.finalSwap_support_disjoint := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.DecoNormalizedCode.weightedFiberNormalForm_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.HasNonnegCoeffs.weightedDecoLagTransform := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.HasNonnegCoeffs.weightedDecoTransform := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.HigherOrderDegreeModels.A110205.natDegree_of_recurrence := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.HigherOrderDegreeModels.A110205.polynomial_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.HigherOrderDegreeModels.A262226.natDegree_of_recurrence := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.HigherOrderDegreeModels.A262226.polynomial_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.HigherOrderDegreeModels.A262226.polynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.HigherOrderDegreeModels.A262226.splits_of_recurrence := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.HigherOrderDegreeModels.A367873.natDegree_of_recurrence := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.HigherOrderDegreeModels.A367873.polynomial_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.IndispensableDigits.interlaces_of_last_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.IndispensableDigits.interlaces_of_total_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.IndispensableDigits.strictInterl_last_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.IndispensableDigits.strictInterl_last_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.IndispensableDigits.strictInterl_total_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.IndispensableDigits.strictInterl_total_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.QuarticGamma.hasNonnegCoeffs_polynomial := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.QuarticGamma.natDegree_polynomial := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.QuarticGamma.splits_polynomial := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.decoBottomTotal_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.decoBottomTotal_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.decoEulerianGamma_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.decoEulerian_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.decoEulerian_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.decoEulerian_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.decoEulerian_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.decoEulerian_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.decoEulerian_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.decoEulerian_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.decoExactLayerDehomogenized_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.decoExactLayerFromStarts_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

end RealRooted.TacticProbe
