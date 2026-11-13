module

import RealRooted.Mathlib.Analysis.Complex.Polynomial.SchurCohn

/-!
# Schur–Cohn criterion

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "schur-cohn"
formalized = "2026-10-07"
tags = []
references = [
  "Schur1917",
  "Cohn1922",
]
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
# Schur–Cohn criterion

A complex polynomial has all zeros in the open unit disk if and only if $|a_0|<|a_n|$ and its
Schur transform has all zeros in the open unit disk.

## Results

Let $p(z)=a_0+a_1z+\dotsb+a_nz^n$ be a complex polynomial of degree $n\ge1$ and let
$p^*(z)=z^n\overline{p(1/\bar z)}$ be its conjugate reciprocal. The *Schur transform* is
$$Tp(z)=\frac{\overline{a_n}\,p(z)-a_0\,p^*(z)}{z},$$
a polynomial of degree at most $n-1$. We call $p$ *Schur stable* if $p\ne0$ and all its zeros
lie in the open unit disk.

**Theorem (Schur–Cohn)** [@Schur1917; @Cohn1922]. The polynomial $p$ is Schur stable if and only
if $|a_0|<|a_n|$ and $Tp$ is Schur stable.

## Use

Iterating the transform decides disk stability in $n$ steps; this is the disk analogue of the
Routh–Hurwitz reduction for the half-plane.

## Proof

Write $p=a_n\prod(z-r_i)$. For $|r|<1$ and $|z|\ge1$ the inequality $|1-\bar zr|\le|z-r|$ gives
$|p^*(z)|\le|p(z)|$ outside the disk, and $|a_0|=|a_n|\prod|r_i|<|a_n|$. Conversely, the identity
$(|a_n|^2-|a_0|^2)\,p(z)=a_n z\,Tp(z)+a_0\,(Tp)^*(z)$ shows that $p$ has no zero with $|z|\ge1$
when $Tp$ is stable.

## References

[@Schur1917; @Cohn1922].
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Mathlib.Analysis.Complex.Polynomial.SchurCohn`.
-/
