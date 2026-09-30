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

[[theorems]]
name = "RealRooted.generalizedLaguerre_splits"
module = "RealRooted.Laguerre.Roots"

[[theorems]]
name = "RealRooted.generalizedLaguerre_roots_neg"
module = "RealRooted.Laguerre.Roots"

[[theorems]]
name = "RealRooted.generalizedLaguerre_hasSimpleRoots"
module = "RealRooted.Laguerre.Roots"

[[theorems]]
name = "RealRooted.generalizedLaguerre_strictInterl_succ"
module = "RealRooted.Laguerre.Roots"

[[theorems]]
name = "RealRooted.generalizedLaguerre_satisfiesFavardRecurrence"
module = "RealRooted.Laguerre.Favard"

[[theorems]]
name = "RealRooted.generalizedLaguerre_integral_orthogonal"
module = "RealRooted.Laguerre.Orthogonality.Integral"
-->

<!-- realrooted-catalog-content -->
# Generalized Laguerre polynomials

The library uses the monic, sign-reversed normalization

```text
P_n^{(α)}(x) = n! L_n^{(α)}(-x)
             = sum_k choose(n,k) (α+k+1)_{n-k} x^k,
```

so that the zeros are nonpositive. For `α ≥ -1` the following are formalized:

- every `P_n^{(α)}` has only real, simple zeros, and they are strictly negative
  when `α > -1`;
- consecutive polynomials strictly interlace;
- the family satisfies a Favard three-term recurrence.

For `α > -1` the family is also orthogonal on the positive half-line:

```text
∫_0^∞ P_m^{(α)}(-x) P_n^{(α)}(-x) x^α e^{-x} dx = 0   (m ≠ n).
```

## References

G. Szegő, *Orthogonal Polynomials*, American Mathematical Society Colloquium
Publications 23 (1939), Chapter V.
The general three-term theory is on the
[Favard page](/RealRooted/theorems/favard/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in `RealRooted.Laguerre`.
-/
