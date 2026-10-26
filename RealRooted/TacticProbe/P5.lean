module

import RealRooted.Applications.OEIS.A144438.DecoratedCycle
import RealRooted.Applications.OEIS.A144438.DiagonalBridge
import RealRooted.Applications.OEIS.A144438.ExactLayer
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.Degree
import RealRooted.Applications.OEIS.A144438.LayerTotal
import RealRooted.Applications.OEIS.InversePeaks
import RealRooted.Applications.OEIS.InversePeaksTypeB
import RealRooted.Applications.OEIS.LowerReentrantCorner
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

example : type_of% @RealRooted.Applications.OEIS.decoExactLayer_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.decoExceptionalLayerStep_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.decoLayerTotal_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.decoNormalLayerStep_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.decoratedCycleEulerian_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.decoratedCycleEulerian_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.decoratedCycleEulerian_leadingCoeff := by
  intros
  rr_row_leadingCoeff_pos

example : type_of% @RealRooted.Applications.OEIS.decoratedCycleEulerian_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.decoratedCycleEulerian_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.decoratedCycleEulerian_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.decoratedCycleEulerian_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.diagonal_admissibleCodePolynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.diagonal_admissibleCodePolynomial_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.diagonal_admissibleCodePolynomial_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.diagonal_decoExactLayerDehomogenized_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.diagonal_normalizedFiberPolynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.diagonal_normalizedFiberPolynomial_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.diagonal_normalizedFiberPolynomial_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.inversePeakEulerian_even_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.inversePeakEulerian_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.inversePeakEulerian_hasPosLeadingCoeff := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.inversePeakEulerian_interlaces_of_degree_succ := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.inversePeakEulerian_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.inversePeakEulerian_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.inversePeakEulerian_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.inversePeakEulerian_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.inversePeakTypeB_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.inversePeakTypeB_hasPosLeadingCoeff := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.inversePeakTypeB_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.inversePeakTypeB_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.inversePeakTypeB_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.inversePeakTypeB_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.inversePeakTypeB_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.lowerReentrantCorner_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.lowerReentrantCorner_hasPosLeadingCoeff := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.lowerReentrantCorner_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.lowerReentrantCorner_odd_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.lowerReentrantCorner_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.lowerReentrantCorner_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.lowerReentrantCorner_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.normalizedDecoratedCycleEulerian_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.normalizedDecoratedCycleEulerian_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.scaledInversePeakGamma_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.scaledInversePeakGamma_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.weightedDecoCompanionBasis_degree_lt := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.weightedDecoCompanionBasis_natDegree_le := by
  intros
  rr_row_natDegree

end RealRooted.TacticProbe
