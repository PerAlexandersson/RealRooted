module

import RealRooted.Transforms.RationalSubstitution
import RealRooted.Transforms.RationalSubstitutionDerivative

/-!
# Denominator-cleared rational substitution

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
# Denominator-cleared rational substitution

For polynomials $A,B$ and $p=\sum_kp_kx^k$ of degree $d$ we put
$$
(A,B)\ast p=\sum_{k=0}^dp_k\,A^kB^{d-k}=B^d\,p(A/B),
$$
the substitution $x\mapsto A/B$ cleared of denominators, and we also use the
version $H_N[p]$ in a fixed ambient degree $N\ge d$, which equals $B^{N-d}(A,B)\ast p$.
The ambient version is additive in $p$ and satisfies
$H_{M+N}[pq]=H_M[p]\,H_N[q]$ when $\deg p\le M$ and $\deg q\le N$.

## Real-rootedness of substitutions

If $p$ splits, then $(A,B)\ast p=\mathrm{lc}(p)\prod_r(A-rB)$ over the roots $r$
of $p$ with multiplicity. Suppose that $p\ne0$, $B\ne0$, that $A,B$ are coprime and
that the quotient $A/B$ is nonconstant. Then
$$
(A,B)\ast p\text{ splits}\iff p\text{ splits and }A-rB\text{ splits for every root }r\text{ of }p .
$$
Moreover, if all roots of the substitution lie in a set $I$ and the fiber
$A-rB$ is nonconstant, then each root $r$ of $p$ equals $A(x)/B(x)$ for some
$x\in I$ with $B(x)\ne0$.

**Quadratic substitution.** For $A=x$ and $B=(1+sx)^2$ the fiber $x-r(1+sx)^2$ has
discriminant $1-4sr$, so
$$
(A,B)\ast p\text{ splits}\iff p\text{ splits and }1-4sr\ge0\text{ for every root }r .
$$
For $s\ge0$ the substitution splits with nonpositive roots exactly when $p$ does.
For $s<0$ it splits with nonpositive roots exactly when $p$ splits and all its roots
lie in $[1/(4s),0]$.

**Dickson substitution.** For $A=x^2+a$ and $B=x$ with $a\ne0$, the substitution
splits if and only if $p$ splits and $4a\le r^2$ for every root $r$ of $p$.

## Derivative transport

Write $H=H_N[p]$ for $\deg p\le N$ and $W=A'B-AB'$. Then
$$
B^2H'=N\,BB'\,H+W\,H_N[p'] ,
$$
and for every $r$ the product $B^{2r}H^{(r)}$ is a combination of the
substitutions $H_N[p^{(j)}]$, $j\le r$, with explicit polynomial coefficients defined
by a recursion; the coefficient of the top term $j=r$ is $W^r$.

## What is new

The substitution lemmas were developed in this library; no published source is
cited, and we attribute none.

## References

No published source is cited for these results in the formalization.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in `RealRooted.Transforms.RationalSubstitution`
and `RealRooted.Transforms.RationalSubstitutionDerivative`.
-/
