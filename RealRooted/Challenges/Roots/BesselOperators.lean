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
authors = []
references = []
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
-->

<!-- realrooted-catalog-content -->
# Bessel operators and imaginary central differences

The finite Bessel operators map real-rooted polynomials to real-rooted polynomials exactly
when $\lambda\ge0$, and the imaginary central difference of a real-rooted polynomial has only
simple real roots. Both are differential operators $\varphi(D)$ whose symbol is an entire
function with only real zeros: a rescaled Bessel function $J_r$, and $\sin(hx)/h$.

## Results

**Theorem (Bessel operators).** For $\lambda\in\mathbb R$ and $r\in\mathbb N$ let $D=d/dx$ and
$$
B_{\lambda,r}=\sum_{k\ge0}\frac{(-\lambda)^k}{k!\,(k+r)!}\,D^{2k+r},
$$
a finite sum on each polynomial. For a nonzero polynomial $f$ with $\deg f\ge r$, the image
$B_{\lambda,r}f$ has degree $\deg f-r$ and leading coefficient
$\binom{\deg f}{r}\operatorname{lc}(f)$. For every $r$, the operator $B_{\lambda,r}$ maps every
real-rooted polynomial to a real-rooted polynomial, with $0$ counted as real-rooted, if and
only if $\lambda\ge0$.

**Theorem (imaginary central difference).** For $h\in\mathbb R$ let $p^{[j]}=p^{(j)}/j!$ be
the Hasse derivative and
$$
\delta_hp=\sum_{k\ge0}(-1)^kh^{2k}\,p^{[2k+1]}
=\sum_{k\ge0}\frac{(-1)^kh^{2k}}{(2k+1)!}\,p^{(2k+1)} .
$$
If $h\ne0$, then $\delta_hp(z)=\dfrac{p(z+ih)-p(z-ih)}{2ih}$ for every complex $z$. If $h>0$
and $p$ is a nonzero real-rooted polynomial of degree at least one, then $\delta_hp$ is
real-rooted with only simple roots. If $\deg p\ge1$, then $\delta_hp$ has degree $\deg p-1$
and leading coefficient $\deg p\cdot\operatorname{lc}(p)$.

## Use

For $\lambda>0$ the symbol of $B_{\lambda,r}$ is $\lambda^{-r/2}J_r(2\sqrt\lambda\,x)$. The
sufficiency of $\lambda\ge0$ is therefore an explicit case of the fact that $\varphi(D)$
preserves real-rootedness for every $\varphi$ in the
[Laguerre–Pólya class](rr:laguerre-polya-class).

## Proof

The roots of $\delta_hp$ are real and simple by the
[Hermite–Biehler theorem](rr:hermite-biehler-hurwitz).

## References

See the [Hermite–Biehler theorem](rr:hermite-biehler-hurwitz) and the
[Laguerre–Pólya class](rr:laguerre-polya-class).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Hermite.BesselOperatorFamily`
and `RealRooted.Hermite.ImaginaryCentralDifference`.
-/
