import RealRooted.Laguerre.Favard
import RealRooted.Laguerre.Orthogonality.Integral
import RealRooted.Laguerre.Roots

/-!
# Generalized Laguerre polynomial challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "laguerre-polynomials"

[[definitions]]
name = "Polynomial.generalizedLaguerre"
module = "RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Basic"
label = "Generalized Laguerre polynomials"

[[theorems]]
name = "RealRooted.generalizedLaguerre_splits"
module = "RealRooted.Laguerre.Roots"
label = "Generalized Laguerre polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.generalizedLaguerre_roots_neg"
module = "RealRooted.Laguerre.Roots"
label = "Generalized Laguerre polynomials have negative roots for α > -1"

[[theorems]]
name = "RealRooted.generalizedLaguerre_hasSimpleRoots"
module = "RealRooted.Laguerre.Roots"
label = "Generalized Laguerre polynomials have simple roots"

[[theorems]]
name = "RealRooted.generalizedLaguerre_strictInterl_succ"
module = "RealRooted.Laguerre.Roots"
label = "Consecutive generalized Laguerre polynomials interlace"

[[theorems]]
name = "RealRooted.generalizedLaguerre_satisfiesFavardRecurrence"
module = "RealRooted.Laguerre.Favard"
label = "Generalized Laguerre polynomials satisfy a Favard recurrence"

[[theorems]]
name = "RealRooted.generalizedLaguerre_integral_orthogonal"
module = "RealRooted.Laguerre.Orthogonality.Integral"
label = "Generalized Laguerre polynomials are orthogonal on the half-line"
-->

<!-- realrooted-catalog-content -->
# Generalized Laguerre polynomials

The library uses the monic, sign-reversed normalization

$$P_n^{(\alpha)}(x) = n!\, L_n^{(\alpha)}(-x) = \sum_k \binom{n}{k} (\alpha+k+1)_{n-k}\, x^k,$$

so that the zeros are nonpositive. For $\alpha \geq -1$:

- every $P_n^{(\alpha)}$ has only real, simple zeros, and they are strictly negative
  when $\alpha > -1$;
- consecutive polynomials strictly interlace;
- the family satisfies a Favard three-term recurrence.

For $\alpha > -1$ the family is also orthogonal on the positive half-line:

$$\int_0^\infty P_m^{(\alpha)}(-x)\, P_n^{(\alpha)}(-x)\, x^\alpha e^{-x}\, dx = 0
  \qquad (m \neq n).$$

## References

G. Szegő, *Orthogonal Polynomials*, American Mathematical Society Colloquium
Publications 23 (1939), Chapter V.
The general three-term theory is on the
[Favard page](/RealRooted/theorems/favard/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in `RealRooted.Laguerre`.
-/
