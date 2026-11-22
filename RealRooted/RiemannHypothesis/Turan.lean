module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import RealRooted.BrandenLC.Sequence
import RealRooted.RiemannHypothesis.TotalPositivity
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Turan

/-!
# Raw xi derivative inequalities under RH

Craven--Csordas's cubic and second iterated Turán inequalities apply to every
derivative of the normalized xi function under Mathlib's RH. The coefficient
statements use raw `riemannXiCoeff` values, without factorial division.
They do not assert arbitrary iteration of the raw coefficient sequence.
-/

public section

namespace RealRooted

/-- Every xi derivative satisfies the cubic derivative inequality under RH
at every nonnegative real argument. -/
theorem cubic_iteratedDeriv_riemannXiTheta_nonneg
    (hRH : RiemannHypothesis) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 2 * (iteratedDeriv (n + 1) riemannXiTheta x).re ^ 3 -
      3 * (iteratedDeriv n riemannXiTheta x).re *
        (iteratedDeriv (n + 1) riemannXiTheta x).re *
        (iteratedDeriv (n + 2) riemannXiTheta x).re +
      (iteratedDeriv n riemannXiTheta x).re ^ 2 *
        (iteratedDeriv (n + 3) riemannXiTheta x).re := by
  simpa only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.add_comm] using
    (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH n).cubic_derivative_nonneg hx

/-- RH gives a cubic inequality between four consecutive raw xi coefficients. -/
theorem cubic_riemannXiCoeff_nonneg (hRH : RiemannHypothesis) (n : ℕ) :
    0 ≤ 2 * riemannXiCoeff (n + 1) ^ 3 -
      3 * riemannXiCoeff n * riemannXiCoeff (n + 1) * riemannXiCoeff (n + 2) +
      riemannXiCoeff n ^ 2 * riemannXiCoeff (n + 3) :=
  cubic_iteratedDeriv_riemannXiTheta_nonneg hRH n le_rfl

/-- Every xi derivative satisfies the second raw Turán inequality under RH
at every nonnegative real argument. -/
theorem second_turan_iteratedDeriv_riemannXiTheta_nonneg
    (hRH : RiemannHypothesis) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ((iteratedDeriv (n + 2) riemannXiTheta x).re ^ 2 -
        (iteratedDeriv (n + 1) riemannXiTheta x).re *
          (iteratedDeriv (n + 3) riemannXiTheta x).re) ^ 2 -
      ((iteratedDeriv (n + 1) riemannXiTheta x).re ^ 2 -
        (iteratedDeriv n riemannXiTheta x).re *
          (iteratedDeriv (n + 2) riemannXiTheta x).re) *
      ((iteratedDeriv (n + 3) riemannXiTheta x).re ^ 2 -
        (iteratedDeriv (n + 2) riemannXiTheta x).re *
          (iteratedDeriv (n + 4) riemannXiTheta x).re) := by
  simpa only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.add_comm] using
    (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH n).second_turan_nonneg hx

/-- The second log-concavity iterate of the raw xi coefficients is
nonnegative at every index at least two under RH. -/
theorem iterate_logConcavity_riemannXiCoeff_two_nonneg
    (hRH : RiemannHypothesis) (n : ℕ) :
    0 ≤ ((logConcavitySequence^[2]) riemannXiCoeff) (n + 2) := by
  have h := second_turan_iteratedDeriv_riemannXiTheta_nonneg hRH n (x := 0) le_rfl
  simpa [Function.iterate_succ_apply', logConcavitySequence, Nat.add_sub_assoc,
    Nat.add_assoc, riemannXiCoeff] using h

end RealRooted
