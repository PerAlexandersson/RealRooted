module

import RealRooted.Derivative.PowerShift

/-!
# The operator D^m (D + c) x^m

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "power-derivative-shift"
formalized = "2026-11-01"
authors = []
references = []
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.powerDerivativeShift"
module = "RealRooted.Derivative.PowerShift"
label = "The operator f ↦ D^m ((D + c)(X^m f))"

[[theorems]]
name = "RealRooted.powerDerivativeShift_splits"
module = "RealRooted.Derivative.PowerShift"
label = "The operator preserves real-rootedness for c ≠ 0"

[[theorems]]
name = "RealRooted.powerDerivativeShift_hasNonnegCoeffs"
module = "RealRooted.Derivative.PowerShift"
label = "The operator preserves nonnegative coefficients for c > 0"

[[theorems]]
name = "RealRooted.StrictInterl.powerDerivativeShift"
module = "RealRooted.Derivative.PowerShift"
label = "The operator transports directed interlacing"
headline = true

[[theorems]]
name = "RealRooted.leadingCoeff_powerDerivativeShift"
module = "RealRooted.Derivative.PowerShift"
label = "Degree is preserved; the leading coefficient is multiplied by c (deg f + m)!/(deg f)!"

[[theorems]]
name = "RealRooted.powerDerivativeShift_roots_nonpos"
module = "RealRooted.Derivative.PowerShift"
label = "For f with nonnegative coefficients and c > 0 all roots of the image are nonpositive"
-->

<!-- realrooted-catalog-content -->
# The operator D^m (D + c) x^m

For $c\ne0$, the operator $D^m(D+c)x^m$ maps real-rooted polynomials to real-rooted polynomials of
the same degree and preserves interlacing. For $m=1$ it is the second-order operator
$f\mapsto cf+(cx+2)f'+xf''$.

## Results

For $m\in\mathbb N$ and $c\in\mathbb R$ let $D=d/dx$ and
$$
T_{m,c}f=D^m\bigl((D+c)(x^mf)\bigr).
$$

**Theorem.** Let $c\ne0$ and let $f$ be a nonzero real-rooted polynomial. Then $T_{m,c}f$ is
real-rooted of degree $\deg f$, with leading coefficient
$c\,\frac{(\deg f+m)!}{(\deg f)!}\operatorname{lc}(f)$. If $f\ll g$, then
$T_{m,c}f\ll T_{m,c}g$.

**Proposition.** If $c>0$ and $f$ has nonnegative coefficients, then $T_{m,c}f$ has nonnegative
coefficients and no positive roots.

## Proof

Multiplication by $x^m$, the operator $D+c$ (by the [Hermite–Poulain theorem](rr:hermite-poulain))
and $D^m$ (by [derivative interlacing](rr:derivative-interlacing)) each preserve real-rootedness and
interlacing, and $D+c$ keeps the degree when $c\ne0$.

## References

- [Hermite–Poulain theorem](sf:hermitePoulainTheorem)
- [Interlacing of polynomials](sf:interlacesPolynomial)
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Derivative.PowerShift`.
-/
