module

import RealRooted.Applications.OEIS.A144438.Gamma
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.Degree
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.DiagonalInduction
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.Endpoints
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.EulerianCone
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.MagicConeEndpoint
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.ParameterContinuity
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.ParameterFamily
import RealRooted.Applications.OEIS.A144438.Weighted
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

example : type_of% @RealRooted.Applications.OEIS.weightedDecoDiagonalCompanion_degree_lt := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.weightedDecoDiagonalCompanion_natDegree_lt := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.weightedDecoDiagonalLag_degree_lt := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.weightedDecoDiagonalLag_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.weightedDecoDiagonalLag_natDegree_lt := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.weightedDecoDiagonal_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.weightedDecoDiagonal_hasPosLeadingCoeff := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.weightedDecoDiagonal_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.weightedDecoDiagonal_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.weightedDecoDiagonal_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.weightedDecoDiagonal_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.weightedDecoEulerian_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.weightedDecoEulerian_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.weightedDecoEulerian_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.weightedDecoEulerian_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.weightedDecoEulerian_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.weightedDecoEulerian_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.weightedDecoEulerian_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.weightedDecoGammaNat_natDegree_le := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.weightedDecoGamma_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.weightedDecoGamma_natDegree_le := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.weightedDecoLagBasis_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.weightedDecoMagicBasisImage_endpoint_and_resultant_ne_zero_of_sign := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.weightedDecoMagicBasisImage_endpoint_of_sign := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.weightedDecoMagicBasisImage_endpoint_of_sign := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.weightedDecoMagicBasisImage_self_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.weightedDecoMagicBasisImage_self_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.weightedDecoParameterCompanion_natDegree_le := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.weightedDecoParameterImage_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.weightedDecoParameterInput_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.weightedDecoTransform_natDegree_of_monic := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.weightedDecoTransform_zero_eq_zero_or_splits_of_roots_mem_Icc := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.weightedDeco_endpoint_resultant_ne_zero_of_sign := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_A_U_of_lt := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_A_X_mul_D_of_lt := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_D_W_of_lt := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_P_S := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_P_T := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_P_W := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_R_P := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_U_W_of_lt := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_U_X_mul_D := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_nextBoundary_A_last_A_castSucc := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.interl_nextBoundary_A_last_W_castSucc := by
  intros
  rr_row_interlaces

end RealRooted.TacticProbe
