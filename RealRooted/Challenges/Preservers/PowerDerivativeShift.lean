module

import RealRooted.Derivative.PowerShift

/-!
# A power, derivative shift and iterated derivative operator

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "power-derivative-shift"
formalized = "2026-11-01"
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.powerDerivativeShift"
module = "RealRooted.Derivative.PowerShift"
label = "The operator f ↦ D^m ((D + c)(X^m f))"

[[theorems]]
name = "RealRooted.powerDerivativeShift_splits"
module = "RealRooted.Derivative.PowerShift"
label = "The operator preserves splitting for c ≠ 0"
headline = true

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
label = "Degree is preserved and the leading coefficient is multiplied by c (deg f + m)!/deg f!"

[[theorems]]
name = "RealRooted.powerDerivativeShift_roots_nonpos"
module = "RealRooted.Derivative.PowerShift"
label = "For f with nonnegative coefficients and c > 0 all roots of the image are nonpositive"
-->

<!-- realrooted-catalog-content -->
# A power, derivative shift and iterated derivative operator

For $m\in\mathbb N$ and $c\in\mathbb R$ let
$$
T_{m,c}f=D^m\bigl((D+c)(x^mf)\bigr),\qquad D=\frac d{dx},
$$
so that $T_{1,c}f=cf+(cx+2)f'+xf''$.

**Theorem.** For $c\ne0$ and a nonzero real-rooted polynomial $f$, the polynomial
$T_{m,c}f$ is nonzero and real-rooted with the same degree as $f$ and leading coefficient
$c\,\frac{(\deg f+m)!}{(\deg f)!}\operatorname{lc}(f)$. If $c>0$ and $f$ has nonnegative
coefficients, then so does $T_{m,c}f$, and all roots of $T_{m,c}f$ are nonpositive. The
operator also transports directed interlacing: if $f\ll g$ then $T_{m,c}f\ll T_{m,c}g$.

## What is new

This operator was developed in this library; no published source is cited, and we
attribute none.

## References

No published source is cited for these results in the formalization. For interlacing, see
the [interlacing page](/RealRooted/concepts/interlacing/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Derivative.PowerShift`.
-/
