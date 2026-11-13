module

import RealRooted.Hermite.Orthogonality.Integral
import RealRooted.Hermite.Roots

/-!
# Hermite polynomials

<!-- realrooted-catalog
version = 1
section = "families"
slug = "hermite-polynomials"
formalized = "2026-09-07"
authors = ["Szegő"]
tags = []
references = [
  "Szego1939",
]

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

[[theorems]]
name = "RealRooted.hermiteReal_hasSimpleRoots"
module = "RealRooted.Hermite.Roots"
label = "Hermite polynomials have simple roots"

[[theorems]]
name = "RealRooted.hermiteReal_strictInterl_succ"
module = "RealRooted.Hermite.Roots"
label = "Consecutive Hermite polynomials interlace"
headline = true

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

The probabilists' Hermite polynomials are real-rooted with simple roots, consecutive ones
interlace, and they are orthogonal for the Gaussian weight.

## Results

The probabilists' Hermite polynomials satisfy $H_0=1$, $H_1=x$ and
$$H_{n+2}(x)=x\,H_{n+1}(x)-(n+1)\,H_n(x).$$

**Theorem.** For all $n$:

- $H_n$ is monic of degree $n$ and has only real, simple roots;
- $H_n\ll H_{n+1}$, and $H_n,H_{n-1},\dots,H_0$ is a Sturm sequence, that is, each consecutive
  pair interlaces;
- the recurrence is a Favard recurrence with diagonal $0$ and subdiagonal $n$;
- $\displaystyle\int_{-\infty}^{\infty}H_i(x)H_j(x)\,e^{-x^2/2}\,dx=\delta_{ij}\sqrt{2\pi}\,i!$.

## Proof

The root and interlacing statements follow from the general
[Favard theory](rr:favard), because the subdiagonal is positive.

## References

[@Szego1939].
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in `RealRooted.Hermite`.
-/
