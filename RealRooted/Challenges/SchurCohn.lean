import RealRooted.Mathlib.Analysis.Complex.Polynomial.SchurCohn

/-!
# Schur–Cohn challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "schur-cohn"
authors = ["Schur", "Cohn"]
years = [1917, 1922]

[[definitions]]
name = "Polynomial.IsSchurStable"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.SchurCohn"
label = "Schur stable: all zeros in the open unit disk"

[[definitions]]
name = "Polynomial.schurTransform"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.SchurCohn"
label = "Schur transform"

[[theorems]]
name = "Polynomial.isSchurStable_iff"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.SchurCohn"
label = "Schur–Cohn criterion"
headline = true
-->

<!-- realrooted-catalog-content -->
# The Schur–Cohn criterion

Let $p(z) = a_0 + a_1 z + \dotsb + a_n z^n$ be a complex polynomial of degree
$n \geq 1$ and let $p^*(z) = z^n \overline{p(1/\bar z)}$ be its conjugate
reciprocal. The **Schur transform** is
$$
T p(z) = \frac{\overline{a_n}\, p(z) - a_0\, p^*(z)}{z},
$$
a polynomial of degree at most $n - 1$.

**Theorem** (Schur–Cohn). All zeros of $p$ lie in the open unit disk if and
only if $|a_0| < |a_n|$ and all zeros of $T p$ lie in the open unit disk.

Iterating the transform decides disk stability in $n$ steps; this is the
disk analogue of the Routh–Hurwitz reduction for the half-plane.

## Proof idea

Write $p = a_n \prod (z - r_i)$. For $|r| < 1$ and $|z| \geq 1$, the Blaschke
inequality $|1 - \bar z r| \leq |z - r|$ gives $|p^*(z)| \leq |p(z)|$ outside
the disk, and $|a_0| = |a_n| \prod |r_i| < |a_n|$. Conversely, the identity
$(|a_n|^2 - |a_0|^2)\, p(z) = a_n z\, T p(z) + a_0\, (Tp)^*(z)$ shows that $p$
has no zero with $|z| \geq 1$ when $T p$ is stable.

## References

I. Schur, “Über Potenzreihen, die im Innern des Einheitskreises beschränkt
sind,” *J. Reine Angew. Math.* 147 (1917), 205–232; A. Cohn, “Über die
Anzahl der Wurzeln einer algebraischen Gleichung in einem Kreise,” *Math. Z.*
14 (1922), 110–148.
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Mathlib.Analysis.Complex.Polynomial.SchurCohn`.
-/
