module

import RealRooted.Applications.EulerianCompendium.DeletionFamily
import RealRooted.Applications.EulerianCompendium.DerangementReciprocal
import RealRooted.Applications.EulerianCompendium.Derangements
import RealRooted.Applications.EulerianCompendium.EvenTop
import RealRooted.Applications.EulerianCompendium.EvenTopRoots
import RealRooted.Applications.EulerianCompendium.Peaks
import RealRooted.Applications.EulerianCompendium.Results
import RealRooted.Applications.OEIS.A046802
import RealRooted.Applications.OEIS.HarmonicDerivativeRows
import RealRooted.Applications.OEIS.PathPowerRows
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

example : type_of% @RealRooted.EulerianCompendium.Challenges.evenTopDescent_strictAlternation := by
  intros
  rr_row_splits

example : type_of% @RealRooted.EulerianCompendium.Challenges.peakPolynomial_interlaces := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.EulerianCompendium.Challenges.peakPolynomial_interlaces := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.EulerianCompendium.Challenges.peakPolynomial_realRooted := by
  intros
  rr_row_splits

example : type_of% @RealRooted.EulerianCompendium.Challenges.peakPolynomial_roots := by
  intros
  rr_row_splits

example : type_of% @RealRooted.EulerianCompendium.Challenges.superEulerian_gamma := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.EulerianCompendium.Challenges.superEulerian_interlaces := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.EulerianCompendium.Challenges.ternaryRun_realRooted_interlaces := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.EulerianCompendium.Challenges.ternaryRun_realRooted_interlaces := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.EulerianCompendium.Challenges.ternaryWordRun_realRooted_interlaces := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.EulerianCompendium.Challenges.ternaryWordRun_realRooted_interlaces := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.EulerianCompendium.Challenges.weightedPeak_interlaces := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.EulerianCompendium.Challenges.weightedPeak_interlaces := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.EulerianCompendium.Challenges.zigzagEulerian_coefficients := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.EulerianCompendium.deletionPolynomial_degree_nonneg := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.EulerianCompendium.derangementDescentPolynomial_natDegree_le := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.EulerianCompendium.derangementDescentPolynomial_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.EulerianCompendium.derangementDescentPolynomial_nonneg := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.EulerianCompendium.derangementDescentPolynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.EulerianCompendium.evenTopDescentCount_insertMaximum := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.EulerianCompendium.evenTopDescentCount_insertMaximum_by_slots := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.EulerianCompendium.evenTopDescentPolynomial_natDegree_lt := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.EulerianCompendium.evenTopDescentPolynomial_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.EulerianCompendium.evenTopDescentPolynomial_nonneg_coeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.EulerianCompendium.evenTopDescentPolynomial_pos_leadingCoeff := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.EulerianCompendium.evenTopDescentPolynomial_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.EulerianCompendium.exists_derangement := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.EulerianCompendium.insertMaximum_new_evenTop_iff := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.EulerianCompendium.insertMaximum_old_evenTop_iff := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.EulerianCompendium.peakPolynomial_hasNonnegCoeffs := by
  intros
  rr_row_nonneg_coeffs

example : type_of% @RealRooted.EulerianCompendium.peakPolynomial_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.EulerianCompendium.peakPolynomial_weakInterl := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.EulerianCompendium.peakPolynomial_weakInterl := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.EulerianCompendium.reciprocalDerangementPolynomial_eq_ascent_sum := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.EulerianCompendium.reciprocalDerangementPolynomial_natDegree := by
  intros
  rr_row_natDegree

example : type_of% @RealRooted.EulerianCompendium.surviving_evenTop_positions_card := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.HarmonicDerivativeRows.interlaces_of_recurrence := by
  intros
  rr_row_interlaces

example : type_of% @RealRooted.OEIS.A046802_ne_zero := by
  intros
  rr_row_ne_zero

example : type_of% @RealRooted.OEIS.A046802_realRooted := by
  intros
  rr_row_splits

example : type_of% @RealRooted.OEIS.A046802_refined_realRooted := by
  intros
  rr_row_splits

example : type_of% @RealRooted.OEIS.A046802_splits := by
  intros
  rr_row_splits

example : type_of% @RealRooted.OEIS.A046802_strictInterl_succ := by
  intros
  rr_row_strictInterl

example : type_of% @RealRooted.OEIS.A046802_strictInterl_succ := by
  intros
  (apply Interlaces.toStrictInterl; rr_row_interlaces)

example : type_of% @RealRooted.PathPowerRows.splits_a109955 := by
  intros
  rr_row_splits

example : type_of% @RealRooted.PathPowerRows.splits_a109960 := by
  intros
  rr_row_splits

example : type_of% @RealRooted.PathPowerRows.splits_a116088 := by
  intros
  rr_row_splits

end RealRooted.TacticProbe
