import RealRooted.Basic

/-!
# Hermite--Poulain challenge entry point

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#hermitePoulainTheorem

Original references include C. Hermite, G. Polya--I. Schur, N. Obreschkoff,
and B. Ya. Levin's account of entire functions.

This module records the finite-polynomial differential-operator theorem target:
if `f` and `g` are real-rooted, then applying `f(D)` to `g` preserves
real-rootedness, allowing the result to vanish.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace Challenges
namespace HermitePoulain

/-- The finite constant-coefficient differential operator `f(D)` applied to
`g`. -/
def applyAsDifferentialOperator (f g : ℝ[X]) : ℝ[X] :=
  (Finset.range (f.natDegree + 1)).sum fun k =>
    C (f.coeff k) * ((Polynomial.derivative^[k]) g)

/-- Hermite--Poulain theorem target, zero-aware because a differential operator
can annihilate a lower-degree polynomial. -/
theorem differentialOperator_preserves_realRooted {f g : ℝ[X]}
    (hf : f ≠ 0 ∧ f.Splits)
    (hg : g ≠ 0 ∧ g.Splits) :
    applyAsDifferentialOperator f g = 0 ∨
      (applyAsDifferentialOperator f g).Splits := by
  sorry

end HermitePoulain
end Challenges
end RealRooted
