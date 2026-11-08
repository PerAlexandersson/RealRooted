module

import RealRooted.Hermite.BesselOperatorFamily
import RealRooted.Hermite.ImaginaryCentralDifference

/-!
# Bessel operators and imaginary central differences

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "bessel-operators"
formalized = "2026-11-01"
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.besselOperator"
module = "RealRooted.Hermite.BesselOperatorFamily"
label = "The finite Bessel operator Σ (-λ)^k D^(2k+r) / (k! (k+r)!)"

[[definitions]]
name = "RealRooted.imaginaryCentralDifference"
module = "RealRooted.Hermite.ImaginaryCentralDifference"
label = "The normalized imaginary central difference"

[[theorems]]
name = "RealRooted.nonneg_iff_forall_besselOperator_splits"
module = "RealRooted.Hermite.BesselOperatorFamily"
label = "The Bessel operator preserves real-rootedness exactly when λ ≥ 0"
headline = true

[[theorems]]
name = "RealRooted.besselOperator_splits"
module = "RealRooted.Hermite.BesselOperatorFamily"
label = "For λ ≥ 0 the Bessel operator maps real-rooted polynomials to real-rooted polynomials"

[[theorems]]
name = "RealRooted.natDegree_besselOperator"
module = "RealRooted.Hermite.BesselOperatorFamily"
label = "The image has degree deg f - r and leading coefficient C(deg f, r) lc(f)"

[[theorems]]
name = "RealRooted.imaginaryCentralDifference_eq_sum_iterate_derivative"
module = "RealRooted.Hermite.ImaginaryCentralDifference"
label = "The central difference is a sum of odd derivatives"

[[theorems]]
name = "RealRooted.eval_complexify_imaginaryCentralDifference"
module = "RealRooted.Hermite.ImaginaryCentralDifference"
label = "The central difference is (p(z + ih) - p(z - ih)) / (2ih)"

[[theorems]]
name = "RealRooted.imaginaryCentralDifference_splits_and_hasSimpleRoots"
module = "RealRooted.Hermite.ImaginaryCentralDifference"
label = "The imaginary central difference of a real-rooted polynomial has simple real roots"
headline = true
-->

<!-- realrooted-catalog-content -->
# Bessel operators and imaginary central differences

## The finite Bessel operator family

For $\lambda\in\mathbb R$ and $r\in\mathbb N$ let
$$
B_{\lambda,r}=\sum_{k\ge0}\frac{(-\lambda)^k}{k!\,(k+r)!}\,D^{2k+r},\qquad D=\frac d{dx},
$$
a finite sum on each polynomial. For a polynomial $f$ of degree at least $r$ the
image $B_{\lambda,r}f$ has degree $\deg f-r$ and leading coefficient
$\binom{\deg f}{r}\operatorname{lc}(f)$, and it vanishes if $\deg f<r$.

**Theorem.** The operator $B_{\lambda,r}$ maps every real-rooted polynomial to a
real-rooted polynomial if and only if $\lambda\ge0$.

For $\lambda\ge0$ the proof builds, for each degree bound $N$, the auxiliary
bivariate polynomial
$\sum_mf_m\,z_0^{N-m}(z_1z_0+z_0^2-\lambda)^m$, shows that it is stable in the upper
half-plane because $f$ splits, and reads off $B_{\lambda,r}f$ as a coefficient.

## Imaginary central differences

For $h\in\mathbb R$ let
$$
\delta_hp(x)=\sum_{k\ge0}(-1)^kh^{2k}\,p^{[2k+1]}(x)=\frac{p(x+ih)-p(x-ih)}{2ih},
$$
where $p^{[j]}=p^{(j)}/j!$ is the Hasse derivative; equivalently it is the sum of odd
derivatives $\sum_k\frac{(-1)^kh^{2k}}{(2k+1)!}p^{(2k+1)}$. If $h>0$ and $p$ is a real-rooted
polynomial of degree at least one, then $\delta_hp$ has degree $\deg p-1$, leading
coefficient $\deg p\cdot\operatorname{lc}(p)$, only real roots, and all roots simple;
the proof uses the Hermite--Biehler theorem.

## What is new

These results were developed in this library; no published source is cited, and we
attribute none.

## References

No published source is cited for these results in the formalization. For the
Hermite--Biehler theorem, see the
[Hermite–Biehler page](/RealRooted/theorems/hermite-biehler-hurwitz/).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Hermite.BesselOperatorFamily`
and `RealRooted.Hermite.ImaginaryCentralDifference`.
-/
