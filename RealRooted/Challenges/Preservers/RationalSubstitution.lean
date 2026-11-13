module

import RealRooted.Transforms.RationalSubstitution
import RealRooted.Transforms.RationalSubstitutionDerivative

/-!
# Rational substitutions

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "rational-substitution"
formalized = "2026-11-01"
authors = []
references = []
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.rationalSubstitution"
module = "RealRooted.Transforms.RationalSubstitution"
label = "The substitution B^deg(p) p(A/B), cleared of denominators"

[[definitions]]
name = "RealRooted.homogenizedSubstitution"
module = "RealRooted.Transforms.RationalSubstitution"
label = "The same substitution in a fixed ambient degree N"

[[definitions]]
name = "RealRooted.HasNonconstantRatio"
module = "RealRooted.Transforms.RationalSubstitution"
label = "The pair (A, B) is not proportional over the complex numbers"

[[definitions]]
name = "RealRooted.quadraticSubstitution"
module = "RealRooted.Transforms.RationalSubstitution"
label = "The substitution x ↦ x / (1 + s x)²"

[[definitions]]
name = "RealRooted.dicksonSubstitution"
module = "RealRooted.Transforms.RationalSubstitutionDerivative"
label = "The substitution x ↦ (x² + a) / x"

[[theorems]]
name = "RealRooted.rationalSubstitution_eq_prod_of_splits"
module = "RealRooted.Transforms.RationalSubstitution"
label = "For a split p, the substitution is lc(p) times the product of A - r B over the roots r"

[[theorems]]
name = "RealRooted.rationalSubstitution_splits_iff"
module = "RealRooted.Transforms.RationalSubstitution"
label = "The substitution splits exactly when p splits and every fiber A - r B splits"
headline = true

[[theorems]]
name = "RealRooted.exists_mem_eq_eval_div_of_isRoot"
module = "RealRooted.Transforms.RationalSubstitution"
label = "Every root of p is a value A(x) / B(x) at a root x of the substitution"

[[theorems]]
name = "RealRooted.quadraticSubstitution_splits_iff"
module = "RealRooted.Transforms.RationalSubstitution"
label = "The quadratic substitution splits iff p splits and 1 - 4 s r ≥ 0 at every root r"

[[theorems]]
name = "RealRooted.quadraticSubstitution_splits_and_roots_nonpos_iff_of_nonneg"
module = "RealRooted.Transforms.RationalSubstitution"
label = "For s ≥ 0, nonpositive roots are preserved exactly for split p with nonpositive roots"

[[theorems]]
name = "RealRooted.quadraticSubstitution_splits_and_roots_nonpos_iff_of_neg"
module = "RealRooted.Transforms.RationalSubstitution"
label = "For s < 0, the exact condition is that the roots of p lie in [1/(4s), 0]"

[[theorems]]
name = "RealRooted.dicksonSubstitution_splits_iff"
module = "RealRooted.Transforms.RationalSubstitutionDerivative"
label = "The Dickson substitution splits iff p splits and 4a ≤ r² at every root r"

[[theorems]]
name = "RealRooted.homogenizedSubstitution_firstDerivative"
module = "RealRooted.Transforms.RationalSubstitutionDerivative"
label = "First-derivative transport through a homogeneous substitution"

[[theorems]]
name = "RealRooted.homogenizedSubstitution_iterateDerivative"
module = "RealRooted.Transforms.RationalSubstitutionDerivative"
label = "Iterated derivatives of the substitution in terms of derivatives of p"
-->

<!-- realrooted-catalog-content -->
# Rational substitutions

Substituting a rational function $A/B$ into a polynomial $p$ and clearing denominators gives a
real-rooted polynomial exactly when $p$ is real-rooted and every fiber $A-rB$ over a root $r$
of $p$ is real-rooted. Two classical cases are the substitution $x/(1+x)^2$ of the
[gamma transform](rr:gamma-transform) and the substitution $x+1/x$ for palindromic polynomials.

## Results

For polynomials $A,B$ and $p=\sum_kp_kx^k$ of degree $d$ put
$$
(A,B)\ast p=\sum_{k=0}^dp_k\,A^kB^{d-k}=B^d\,p(A/B).
$$
For $N\ge d$ let $H_N[p]=B^{N-d}\,(A,B)\ast p$ be the version in ambient degree $N$. It is
additive in $p$ for $\deg p\le N$, and $H_{M+N}[pq]=H_M[p]\,H_N[q]$ when $\deg p\le M$ and
$\deg q\le N$.

**Theorem (factorization).** If $p$ splits over $\mathbb R$, then
$(A,B)\ast p=\operatorname{lc}(p)\prod_r(A-rB)$ over the roots $r$ of $p$ with multiplicity.

**Theorem (root descent).** Let $p\ne0$ and $B\ne0$ be real polynomials, with $A$ and $B$
coprime and not proportional over $\mathbb C$. Then
$$
(A,B)\ast p\text{ splits}\iff p\text{ splits and }A-rB\text{ splits for every root }r\text{ of }p.
$$
If moreover $(A,B)\ast p$ splits with all roots in a set $I$, then every root $r$ of $p$ whose
fiber $A-rB$ is nonconstant equals $A(x)/B(x)$ for some $x\in I$ with $B(x)\ne0$.

**Corollary (quadratic substitution).** Let $p\ne0$, $s\in\mathbb R$, $A=x$ and
$B=(1+sx)^2$. The fiber $x-r(1+sx)^2$ has discriminant $1-4sr$, and
$$
(A,B)\ast p\text{ splits}\iff p\text{ splits and }1-4sr\ge0\text{ for every root }r\text{ of }p .
$$
For $s\ge0$, the substitution splits with only nonpositive roots if and only if $p$ splits
with only nonpositive roots. For $s<0$, it splits with only nonpositive roots if and only if
$p$ splits and all its roots lie in $[1/(4s),0]$. For $s=1$, $H_N[p]$ is the gamma transform
$\Gamma_{2N}(p)$.

**Corollary (Dickson substitution).** Let $p\ne0$, $a\ne0$, $A=x^2+a$ and $B=x$. Then
$(A,B)\ast p$ splits if and only if $p$ splits and $4a\le r^2$ for every root $r$ of $p$.

The derivatives of $H=H_N[p]$ are also expressed through those of $p$: with $W=A'B-AB'$, over
any commutative ring,
$$
B^2H'=N\,BB'\,H+W\,H_N[p'] ,
$$
and for every $r$ the product $B^{2r}H^{(r)}$ equals $\sum_{j\le r}c_{r,j}\,H_N[p^{(j)}]$ with
polynomials $c_{r,j}$ defined by an explicit recursion in $A,B,N$ and $c_{r,r}=W^r$.

## Proof

When $p$ splits, the factorization shows that $(A,B)\ast p$ splits exactly when every fiber
does. If $p$ has a nonreal root $z$, then every root of $A-zB$ is a nonreal root of
$(A,B)\ast p$, because $A$ and $B$ are coprime and $A/B$ is real at real points.

## References

- [Gamma polynomials](sf:gammaPolynomial) on symmetricfunctions.com
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Transforms.RationalSubstitution`
and `RealRooted.Transforms.RationalSubstitutionDerivative`.
-/
