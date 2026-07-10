import RealRooted.Basic

/-!
# Kurtz challenge entry point

Human statement:
https://www.symmetricfunctions.com/realRooted.htm#kurtzTheorem

Original references: J. I. Hutchinson, "On a remarkable class of entire
functions", Trans. Amer. Math. Soc. 25 (1923), 325--332, and D. C. Kurtz,
"A sufficient condition for all the roots of a polynomial to be real",
Amer. Math. Monthly 99 (1992), 259--263.

This module records the coefficient-inequality theorem-shaped target.  It is
currently an open challenge; see GitHub issue #72.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace Kurtz

/-- Kurtz's sufficient condition: positive coefficients and the strict
Hutchinson--Kurtz log-concavity inequalities imply real-rootedness. -/
theorem coefficientCriterion {p : ℝ[X]}
    (hdeg : 2 ≤ p.natDegree)
    (hpos : ∀ i ≤ p.natDegree, 0 < p.coeff i)
    (hineq : ∀ i : ℕ, 0 < i → i < p.natDegree →
      4 * p.coeff (i - 1) * p.coeff (i + 1) < (p.coeff i) ^ 2) :
    p.Splits := by
  sorry

end Kurtz
end Challenges
end RealRooted
