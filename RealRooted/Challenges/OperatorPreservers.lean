import RealRooted.EulerOperator
import RealRooted.EulerOperator.Polar.ProperPosition
import RealRooted.OperatorPreservesInterlacing
import RealRooted.ReciprocalShift.ProperPosition

open Polynomial

/-!
# Operator preservers challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "operator-preservers"
authors = ["Brändén"]
years = [2011]

[[definitions]]
name = "RealRooted.PreservesRealRootedOrZero"
module = "RealRooted.OperatorPreservesInterlacing"
label = "Real-rootedness preserver"

[[definitions]]
name = "RealRooted.theta"
module = "RealRooted.EulerOperator"
label = "The Euler operator θ = x d/dx"

[[definitions]]
name = "RealRooted.polarTheta"
module = "RealRooted.EulerOperator"
label = "The polar Euler operator N − θ"

[[definitions]]
name = "RealRooted.reciprocalShift"
module = "RealRooted.PFPolynomial"
label = "The reciprocal x^D p(1/x)"

[[theorems]]
name = """RealRooted.Challenges.OperatorPreservers.\
preservesInterlacing_of_preservesRealRootedOrZero"""
label = "Real-rootedness preservers preserve interlacing"

[[theorems]]
name = "RealRooted.Challenges.OperatorPreservers.Interl.theta"
label = "θ preserves interlacing of PF polynomials"

[[theorems]]
name = "RealRooted.Challenges.OperatorPreservers.Interl.polarTheta"
label = "N − θ preserves interlacing of PF polynomials of degree at most N"

[[theorems]]
name = "RealRooted.Challenges.OperatorPreservers.StrictInterl.reciprocalShift"
label = "The reciprocal reverses interlacing of PF polynomials"
-->

<!-- realrooted-catalog-content -->
# Operators preserving interlacing

Let $T$ be a real-linear operator that sends every nonzero real-rooted
polynomial to zero or to a real-rooted polynomial. If $f$ and $g$ interlace,
then $T f$ and $T g$ interlace in one of the two orientations, where the
images may vanish.

For PF polynomials (nonnegative coefficients and only real, nonpositive roots)
three concrete operators preserve the orientation. Here $p \ll q$ allows
either polynomial to be zero, except in the last statement.

- The Euler operator $\theta = x\, d/dx$: if $p \ll q$, then
  $\theta p \ll \theta q$.
- The polar operator $N - \theta$, that is, $p \mapsto N p - x p'$: if
  $p \ll q$ and both have degree at most $N$, then
  $(N - \theta) p \ll (N - \theta) q$.
- The reciprocal $p \mapsto x^D p(1/x)$ reverses the orientation: if
  $p \ll q$ are nonzero and both have degree at most $D$, then
  $x^D q(1/x) \ll x^D p(1/x)$.

## References

P. Brändén, “Iterated sequences and the geometry of zeros,” *Journal für die
reine und angewandte Mathematik* 658 (2011), 115–131.  See also the
[operator-preserver overview on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#operatorPreservesInterlacing).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#operatorPreservesInterlacing

Catalog reference: P. Branden, "Iterated sequences and the geometry of zeros",
J. Reine Angew. Math. 658 (2011), Theorem 9 in the operator-preserver notes
cited by the catalog.

This module exposes the checked Obreschkoff-level theorem: a linear operator
that preserves real-rootedness up to zero preserves interlacing pairs up to the
orientation ambiguity of the current `StrictInterl` convention.
-/

namespace RealRooted
namespace Challenges
namespace OperatorPreservers

/-- Real-rootedness-preserving linear operators preserve interlacing pairs up
to order and zero images. -/
theorem preservesInterlacing_of_preservesRealRootedOrZero (T : ℝ[X] →ₗ[ℝ] ℝ[X])
    (hT : PreservesRealRootedOrZero T) ⦃f g : ℝ[X]⦄ (hfg : StrictInterl f g) :
    Interl (T f) (T g) ∨ Interl (T g) (T f) :=
  RealRooted.operatorPreservesInterlacingPairsUpToOrder T hT hfg

/-- The Euler operator `θ = X d/dX` preserves interlacing of PF polynomials. -/
theorem Interl.theta {p q : ℝ[X]} (hp : IsPFPolynomial p) (hq : IsPFPolynomial q)
    (hpq : Interl p q) : Interl (RealRooted.theta p) (RealRooted.theta q) :=
  thetaPreservesInterl hp hq hpq

/-- The polar Euler operator `N - θ` preserves interlacing of PF polynomials of
degree at most `N`. -/
theorem Interl.polarTheta {N : ℕ} {p q : ℝ[X]} (hp : IsPFPolynomial p)
    (hq : IsPFPolynomial q) (hpd : p.natDegree ≤ N) (hqd : q.natDegree ≤ N)
    (hpq : Interl p q) :
    Interl (RealRooted.polarTheta N p) (RealRooted.polarTheta N q) :=
  polarTheta_preserves_interl hp hq hpd hqd hpq

/-- The reciprocal `X ^ D p(1 / X)` reverses interlacing of PF polynomials of
degree at most `D`. -/
theorem StrictInterl.reciprocalShift {D : ℕ} {p q : ℝ[X]} (hp : IsPFPolynomial p)
    (hq : IsPFPolynomial q) (hpd : p.natDegree ≤ D) (hqd : q.natDegree ≤ D)
    (hpq : StrictInterl p q) :
    StrictInterl (RealRooted.reciprocalShift D q) (RealRooted.reciprocalShift D p) :=
  reciprocalShift_reverses_strictInterl hp hq hpd hqd hpq

end OperatorPreservers
end Challenges
end RealRooted
