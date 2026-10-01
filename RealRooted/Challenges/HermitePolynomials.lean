import RealRooted.Hermite.Orthogonality.Integral
import RealRooted.Hermite.Roots

/-!
# Hermite polynomial challenge entry point

<!-- realrooted-catalog
version = 1
section = "families"
slug = "hermite-polynomials"

[[definitions]]
name = "RealRooted.hermiteReal"
module = "RealRooted.Hermite.Basic"
label = "Probabilists' Hermite polynomials"

[[definitions]]
name = "RealRooted.hermiteGaussianWeight"
module = "RealRooted.Hermite.Orthogonality.Integral"
label = "Gaussian weight"

[[theorems]]
name = "RealRooted.hermiteReal_isRealRooted"
module = "RealRooted.Hermite.Roots"
label = "Hermite polynomials are real-rooted"
headline = true

[[theorems]]
name = "RealRooted.hermiteReal_hasSimpleRoots"
module = "RealRooted.Hermite.Roots"
label = "Hermite polynomials have simple roots"

[[theorems]]
name = "RealRooted.hermiteReal_strictInterl_succ"
module = "RealRooted.Hermite.Roots"
label = "Consecutive Hermite polynomials interlace"

[[theorems]]
name = "RealRooted.hermiteReal_isSturmSeq"
module = "RealRooted.Hermite.Roots"
label = "Hermite polynomials form a Sturm sequence"

[[theorems]]
name = "RealRooted.hermiteReal_satisfiesFavardRecurrence"
module = "RealRooted.Hermite.Favard"
label = "Hermite polynomials satisfy a Favard recurrence"

[[theorems]]
name = "RealRooted.hermiteReal_integral_orthogonal"
module = "RealRooted.Hermite.Orthogonality.Integral"
label = "Hermite polynomials are orthogonal for the Gaussian weight"
-->

<!-- realrooted-catalog-content -->
# Hermite polynomials

The probabilists' Hermite polynomials satisfy `H_0 = 1`, `H_1 = x` and

```text
H_{n+2}(x) = x H_{n+1}(x) - (n + 1) H_n(x).
```

The following are formalized:

- each `H_n` is monic of degree `n`, with only real and simple zeros;
- consecutive polynomials strictly interlace, and `H_n, H_{n-1}, …, H_0` is a
  Sturm sequence;
- the recurrence is a Favard recurrence with diagonal `0` and subdiagonal
  `n`;
- the polynomials are orthogonal for the Gaussian weight:

  ```text
  ∫ H_i(x) H_j(x) e^{-x²/2} dx = δ_{ij} √(2π) i!.
  ```

The root and interlacing statements follow from the general
[Favard theory](/RealRooted/theorems/favard/), because the subdiagonal is
positive.

## References

G. Szegő, *Orthogonal Polynomials*, American Mathematical Society Colloquium
Publications 23 (1939).
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in `RealRooted.Hermite`.
-/
