module

import RealRooted.Derivative.PowerShift

/-!
# The operator D^m (D + c) x^m preserves real roots and interlacing

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
label = "The operator preserves splitting for c ≠ 0"

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
# The operator D^m (D + c) x^m preserves real roots and interlacing

For $c\ne0$, applying $D^m(D+c)x^m$ to a real-rooted polynomial gives a real-rooted
polynomial of the same degree, and the operator preserves interlacing.

## Results

For $m\in\mathbb N$ and $c\in\mathbb R$ let $D=d/dx$ and
$$
T_{m,c}f=D^m\bigl((D+c)(x^mf)\bigr),
$$
so that $T_{1,c}f=cf+(cx+2)f'+xf''$. We write $f\ll g$ if $f$ interlaces $g$; repeated and
common roots are allowed unless stated.

**Theorem.** Let $c\ne0$ and let $f$ be a nonzero real-rooted polynomial.

- $T_{m,c}f$ is real-rooted and has degree $\deg f$ and leading coefficient
  $c\,\frac{(\deg f+m)!}{(\deg f)!}\operatorname{lc}(f)$.
- If $f\ll g$ in the library's `StrictInterl` sense, then $T_{m,c}f\ll T_{m,c}g$ in the same
  sense.
- If $c>0$ and $f$ has nonnegative coefficients, then $T_{m,c}f$ has nonnegative
  coefficients and only nonpositive roots.

## References

For interlacing, see the [interlacing page](/RealRooted/concepts/interlacing/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Derivative.PowerShift`.
-/
