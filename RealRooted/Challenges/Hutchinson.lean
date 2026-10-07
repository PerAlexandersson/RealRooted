import RealRooted.Hutchinson

/-!
# Hutchinson's theorem challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "hutchinson"
authors = ["Hutchinson"]
years = [1923]

[[theorems]]
name = "RealRooted.Hutchinson.isLaguerrePolya_tsum"
module = "RealRooted.Hutchinson"
label = "Hutchinson: such power series are Laguerre–Pólya entire functions"
headline = true

[[theorems]]
name = "RealRooted.IsLaguerrePolya.of_tendstoLocallyUniformly"
module = "RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure"
label = "The Laguerre–Pólya class is closed under locally uniform limits"
-->

<!-- realrooted-catalog-content -->
# Hutchinson's theorem

**Theorem** (Hutchinson). If $a_k > 0$ and $a_{k+1}^2 \geq 4 a_k a_{k+2}$ for
all $k$, then $\sum_k a_k z^k$ is an entire function in the Laguerre–Pólya
class: a locally uniform limit of real-rooted real polynomials.

This is the entire-function form of [Kurtz's criterion](/RealRooted/theorems/kurtz/),
which needs strict inequalities and concerns polynomials.

## Proof idea

The coefficients decay like $4^{-k^2/2}$, so the series is entire and its
partial sums converge locally uniformly. On a disc we first approximate by a
partial sum, and then that partial sum by $\sum_{k<N} a_k q^{k^2} z^k$ with
$q < 1$ close to $1$. The perturbed coefficients satisfy Kurtz's strict
inequalities, so these polynomials are real-rooted. We also show that the
Laguerre–Pólya class is closed under locally uniform limits.

## References

J. I. Hutchinson, “On a remarkable class of entire functions,” *Transactions
of the American Mathematical Society* 25 (1923), 325–332; D. C. Kurtz, “A
sufficient condition for all the roots of a polynomial to be real,” *American
Mathematical Monthly* 99 (1992), 259–263.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in `RealRooted.Hutchinson`
and `RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure`.
-/
