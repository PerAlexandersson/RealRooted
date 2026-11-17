module

import RealRooted.Mathlib.Analysis.Complex.Polynomial.EnestromKakeya
import RealRooted.Mathlib.Analysis.Complex.Polynomial.SchurCohn

/-!
# Zeros in the unit disk: Eneström–Kakeya and Schur–Cohn

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "unit-disk-zeros"
formalized = "2026-10-07"
references = [
  "Schur1917",
  "Cohn1922",
]
authors = ["Eneström", "Kakeya", "Schur", "Cohn"]
years = [1893, 1912, 1917, 1922]

[[definitions]]
name = "Polynomial.IsSchurStable"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.SchurCohn"
label = "Schur stable: all zeros in the open unit disk"

[[definitions]]
name = "Polynomial.schurTransform"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.SchurCohn"
label = "Schur transform"

[[theorems]]
name = "Polynomial.norm_le_one_of_isRoot_of_coeff_monotone"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.EnestromKakeya"
label = "Eneström–Kakeya: increasing positive coefficients give zeros in the unit disk"
headline = true

[[theorems]]
name = "Polynomial.norm_mem_Icc_of_isRoot_of_coeff_pos"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.EnestromKakeya"
label = "Eneström–Kakeya annulus: coefficient ratios in [m, M] give m ≤ |z| ≤ M"

[[theorems]]
name = "Polynomial.isSchurStable_iff"
module = "RealRooted.Mathlib.Analysis.Complex.Polynomial.SchurCohn"
label = "Schur–Cohn: p is Schur stable iff |a₀| < |aₙ| and its Schur transform is"
-->

<!-- realrooted-catalog-content -->
# Zeros in the unit disk: Eneström–Kakeya and Schur–Cohn

A real polynomial with positive nondecreasing coefficients has all its zeros in the closed unit
disk (Eneström–Kakeya). For complex polynomials, the Schur–Cohn criterion decides whether all
zeros lie in the open unit disk by a reduction of the degree.

## Results

**Theorem (Eneström–Kakeya).** If $0<a_0\le a_1\le\dotsb\le a_n$, then every complex zero $z$
of $a_0+a_1z+\dotsb+a_nz^n$ satisfies $|z|\le1$. More generally, if $a_0,\dotsc,a_n>0$ and
$m\le a_i/a_{i+1}\le M$ for $0\le i<n$, then every zero satisfies $m\le|z|\le M$.

Let $p(z)=a_0+a_1z+\dotsb+a_nz^n$ be a complex polynomial of degree $n\ge1$ and
$p^*(z)=z^n\overline{p(1/\bar z)}$. The *Schur transform* is
$$
Tp(z)=\frac{\overline{a_n}\,p(z)-a_0\,p^*(z)}{z},
$$
a polynomial of degree at most $n-1$. We call $p$ *Schur stable* if $p\ne0$ and all its zeros
lie in the open unit disk.

**Theorem (Schur–Cohn).** [@Schur1917; @Cohn1922] The polynomial $p$ is Schur stable if and
only if $|a_0|<|a_n|$ and $Tp$ is Schur stable.

## Use

Iterating the Schur transform decides Schur stability in at most $n$ steps; it is the disk
analogue of the Routh–Hurwitz reduction for the half-plane on the
[Hermite–Biehler page](rr:hermite-biehler-hurwitz).

## Proof

For Eneström–Kakeya, $(z-1)p(z)=a_nz^{n+1}-\sum_{k=1}^n(a_k-a_{k-1})z^k-a_0$, where the
subtracted coefficients are nonnegative with sum $a_n$. For $|z|>1$ the triangle inequality
bounds the lower terms by $a_n|z|^n<a_n|z|^{n+1}$. For Schur–Cohn, $|p^*(z)|\le|p(z)|$ when
$|z|\ge1$ and all zeros lie in the open disk, and conversely the identity
$(|a_n|^2-|a_0|^2)\,p(z)=a_nz\,Tp(z)+a_0\,(Tp)^*(z)$ excludes zeros with $|z|\ge1$ when $Tp$ is
Schur stable.

## References

G. Eneström, “Härledning af en allmän formel för antalet pensionärer …,” *Öfversigt af Kongl.
Vetenskaps-Akademiens Förhandlingar* 50 (1893); S. Kakeya, “On the limits of the roots of an
algebraic equation with positive coefficients,” *Tôhoku Math. J.* 2 (1912), 140–142;
[@Schur1917; @Cohn1922].
<!-- /realrooted-catalog-content -->
-/
