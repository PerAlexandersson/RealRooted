module

import RealRooted.Applications.BinderVecchi.UniformChow
import RealRooted.Applications.OEIS.A144696.Endpoints
import RealRooted.Applications.OEIS.A144696.StrictInterlacing
import RealRooted.Applications.OEIS.A330798
import RealRooted.Applications.OEIS.HarmonicDerivativeRows
import RealRooted.Applications.OEIS.PathPowerRows
import RealRooted.Applications.OEIS.PeriodicTopRows
import RealRooted.Applications.OEIS.ReflectedEulerRows
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

example : type_of% @RealRooted.PathPowerRows.splits_a116089 := by
  intros
  rr_row_splits

example : type_of% @RealRooted.PathPowerRows.splits_a127893 := by
  intros
  rr_row_splits

example : type_of% @RealRooted.PathPowerRows.splits_a206294 := by
  intros
  rr_row_splits

example : type_of% @RealRooted.PathPowerRows.splits_a277627 := by
  intros
  rr_row_splits

example : type_of% @RealRooted.PathPowerRows.strictInterl_a109955 := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.PathPowerRows.strictInterl_a109955 := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.PathPowerRows.strictInterl_a109960 := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.PathPowerRows.strictInterl_a109960 := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.PathPowerRows.strictInterl_a116088 := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.PathPowerRows.strictInterl_a116088 := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.PathPowerRows.strictInterl_a116089 := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.PathPowerRows.strictInterl_a116089 := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.PathPowerRows.strictInterl_a127893 := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.PathPowerRows.strictInterl_a127893 := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.PathPowerRows.strictInterl_a206294 := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.PathPowerRows.strictInterl_a206294 := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.PathPowerRows.strictInterl_a277627 := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.PathPowerRows.strictInterl_a277627 := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.ReflectedEulerRows.interlaces_of_centralFactorial_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.ReflectedEulerRows.interlaces_of_legendreStirling_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.ReflectedEulerRows.interlaces_rows := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Tactic.RowParityDegree.A177040_leadingCoeff := by
  intros
  rr_row_leadingCoeff_pos

example : type_of% @RealRooted.Tactic.RowParityDegree.A177040_leadingCoeff_pos := by
  intros
  rr_row_leadingCoeff_pos

example : type_of% @RealRooted.Tactic.RowParityDegree.A177040_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Tactic.RowParityDegree.A177040_natDegree_eq_and_leadingCoeff_pos := by
  intros
  rr_row_leadingCoeff_pos

example : type_of% @RealRooted.Tactic.RowParityDegree.A177040_natDegree_of_recurrence := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Tactic.RowParityDegree.A330798_leadingCoeff_pos := by
  intros
  rr_row_leadingCoeff_pos

example : type_of% @RealRooted.Tactic.RowParityDegree.A330798_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Tactic.RowParityDegree.A330798_natDegree_eq_and_leadingCoeff_pos := by
  intros
  rr_row_leadingCoeff_pos

example : type_of% @RealRooted.UniformChow.augChowUniform_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.UniformChow.chowUniform_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.UniformChow.isRealRooted_augChowUniform := by
  intros
  rr_row_splits

example : type_of% @RealRooted.UniformChow.isRealRooted_chowUniform := by
  intros
  rr_row_splits

example : type_of% @RealRooted.a144696Auxiliary_diagonal_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.a144696Auxiliary_interlaces_of_strictInterl := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.a144696BernsteinImage_horizontal_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.a144696BernsteinImage_horizontal_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.a144696BernsteinImage_shifted_step := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.a144696BernsteinImage_shifted_step := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.a144696BernsteinImage_shifted_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.a144696BernsteinImage_shifted_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.a144696BernsteinImage_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.a144696BernsteinImage_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.a144696BernsteinImage_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.a144696BernsteinImage_vertical_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.a144696BernsteinImage_vertical_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.a144696Polynomial_reciprocal_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.a144696Polynomial_reciprocal_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.harmonicDerivativeRow_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.harmonicDerivativeRow_hasPosLeadingCoeff := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.harmonicDerivativeRow_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.harmonicDerivativeRow_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.harmonicDerivativeRow_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.harmonicDerivativeRow_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

end RealRooted.TacticProbe
