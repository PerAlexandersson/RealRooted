module

import RealRooted.Applications.EulerianVariations.CyclicPathDescents
import RealRooted.Applications.EulerianVariations.TernaryRuns
import RealRooted.Applications.EulerianVariations.TernaryRuns.Recurrence
import RealRooted.Applications.OEIS.A046802
import RealRooted.Applications.OEIS.A056939
import RealRooted.Applications.OEIS.A079508
import RealRooted.Applications.OEIS.A080721
import RealRooted.Applications.OEIS.A259454
import RealRooted.Applications.OEIS.A286785
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

example : type_of% @RealRooted.A259454.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.A259454.row_interlaces_succ := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.A259454.row_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.A259454.row_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.A259454.row_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.A286785.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.A286785.rowPoly_leadingCoeff_pos := by
  intros
  rr_row_leadingCoeff_pos

example : type_of% @RealRooted.A286785.rowPoly_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.A286785.rowPoly_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.A286785.rowPoly_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.A286785.rowPoly_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.A286785.rowPoly_strictInterl_succ_of_splits := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.A286785.rowPoly_strictInterl_succ_of_splits := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.EulerianVariations.natDegree_cyclicPathDescentPolynomial := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.EulerianVariations.natDegree_ternaryRunPolynomial := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.EulerianVariations.ternaryRunPolynomial_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.EulerianVariations.ternaryRunPolynomial_pos_leadingCoeff := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.EulerianVariations.ternaryRunPolynomial_strictInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.EulerianVariations.ternaryRunPolynomial_strictInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A046802.binomial_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A046802.binomial_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A046802.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A056939.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A056939.polynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A056939.polynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A056939.polynomial_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A056939.polynomial_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A056939.splits_of_recurrence := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A079508.A079508_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A079508.A079508_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.Applications.OEIS.A079508.A079508_prec := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A079508.A079508_prec := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A079508.A079508_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A079508.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A079508.polynomial_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A079508.polynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A079508.reflectedModel_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A079508.reflectedModel_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A079508.splits_of_recurrence := by
  intros
  rr_row_splits

example : type_of% @RealRooted.Applications.OEIS.A080721.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A080721.legendre_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A080721.legendre_posLeadingCoeff := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.A080721.legendre_strictInterl_polynomial := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A080721.legendre_strictInterl_polynomial := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A080721.legendre_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A080721.legendre_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.Applications.OEIS.A080721.polynomial_interlaces_succ := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.Applications.OEIS.A080721.polynomial_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.Applications.OEIS.A080721.polynomial_posLeadingCoeff := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.Applications.OEIS.A080721.polynomial_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.Applications.OEIS.A080721.polynomial_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

end RealRooted.TacticProbe
