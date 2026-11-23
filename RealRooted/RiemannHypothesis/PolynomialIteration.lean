module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Coefficients
public import RealRooted.Hermite.FormalDifferential.Basic
public import RealRooted.SimpleRoots
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
import RealRooted.RiemannHypothesis.StrictCoefficient
import RealRooted.Hermite.FormalDifferential.NegativeVariance
import RealRooted.Hermite.FormalDifferential.Taylor
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Eventual simple roots under iterated xi differential operators

For each derivative of the normalized square-variable xi function, ordinary
symbol coefficients are `γ(n+k)/k!`. The second-cumulant condition is exactly
the strict raw Turán inequality, not the weaker factorial-normalized inequality.
RH supplies that condition here. The unconditional kernel proof remains separate.
-/

public section

open Polynomial Filter RealRooted.HermitePoulain

namespace RealRooted

/-- Under RH, iterating any shifted xi formal differential symbol eventually
makes every nonzero real polynomial simple-real-rooted. -/
theorem eventually_simple_formal_riemannXi_iterates (hRH : RiemannHypothesis)
    (n : ℕ) {P : ℝ[X]} (hP : P ≠ 0) :
    ∀ᶠ m : ℕ in atTop, IsSimpleRealRooted
      ((formalDifferentialOperator
        (PowerSeries.mk fun k => riemannXiCoeff (n + k) / k.factorial))^[m] P) := by
  apply eventually_simple_iterate_formalDifferentialOperator ?_ ?_ hP
  · simpa using (riemannXiCoeff_pos n).ne'
  · have h := riemannXiCoeff_strict_logConcave hRH n
    norm_num only [PowerSeries.constantCoeff_mk, PowerSeries.coeff_mk,
      Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two, Nat.cast_one,
      Nat.cast_ofNat, Nat.add_zero, div_one]
    linarith

/-- Under RH, the actual Taylor operator of each xi derivative eventually gives
simple real roots on every nonzero real polynomial, with no input root assumption. -/
theorem eventually_simple_taylor_riemannXi_iterates (hRH : RiemannHypothesis)
    (n : ℕ) {P : ℝ[X]} (hP : P ≠ 0) :
    ∀ᶠ m : ℕ in atTop, IsSimpleRealRooted
      ((taylorDifferentialOperator (iteratedDeriv n riemannXiTheta))^[m] P) := by
  have hop : formalDifferentialOperator
      (PowerSeries.mk fun k => riemannXiCoeff (n + k) / k.factorial) =
      taylorDifferentialOperator (iteratedDeriv n riemannXiTheta) := by
    funext Q
    apply formalDifferentialOperator_eq_taylor
    intro k
    simp only [PowerSeries.coeff_mk, Complex.div_natCast_re, riemannXiCoeff,
      iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, Nat.add_comm]
  simpa only [hop] using eventually_simple_formal_riemannXi_iterates hRH n hP

end RealRooted
