module

import RealRooted.ClassicalHurwitzMatrix.Stability.BinomialPerturbation

/-!
# Binomial perturbations, Hurwitz stability and a common interlacer

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "binomial-perturbations"
formalized = "2026-11-01"
authors = []
references = []
tags = ["realrooted-original"]

[[definitions]]
name = "RealRooted.binomialCoefficientPerturbation"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.BinomialPerturbation"
label = "The perturbation of (1 + X)^n with prescribed lower coefficients"

[[definitions]]
name = "RealRooted.binomialPerturbationFamily"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.BinomialPerturbation"
label = "The even-binomial section with γ-basis perturbations"

[[theorems]]
name = "RealRooted.binomialCoefficientPerturbation_isRightHalfPlaneStable"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.BinomialPerturbation"
label = "Weighted coefficient bounds give right-half-plane stability of perturbations of (1 + X)^n"

[[theorems]]
name = "RealRooted.binomialCoefficientPerturbation_boundary"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.BinomialPerturbation"
label = "A zero with nonnegative real part is 0 and forces c₀ = -1 and all other cₖ = 0"

[[theorems]]
name = "RealRooted.binomialPerturbationFamily_negativeRoots_interlaced"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.BinomialPerturbation"
label = "The family is real-rooted with negative roots and interlaced by the odd binomial section"
headline = true

[[theorems]]
name = "RealRooted.oddEvenPolynomial_binomialPerturbationFamily_strictlyStable"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.BinomialPerturbation"
label = "x O_n(x²) + G_a(x²) is strictly Hurwitz stable away from one exceptional parameter"

[[theorems]]
name = "RealRooted.binomialPerturbationFamily_simpleRoots_noCommonRoot"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.BinomialPerturbation"
label = "Away from the exceptional parameter the roots are simple and disjoint from the odd section"

[[theorems]]
name = "RealRooted.binomialPerturbationFamily_compatible"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.BinomialPerturbation"
label = "Any two members of the family are compatible"
-->

<!-- realrooted-catalog-content -->
# Binomial perturbations, Hurwitz stability and a common interlacer

A perturbation of $(1+z)^n$ with weighted-small lower coefficients has no zero in the open right
half-plane, and a corresponding family of perturbations of the even binomial section is
real-rooted and interlaced by the odd section.

## Results

**Theorem (right-half-plane stability).** Let $n\ge0$ and let $c_0,\dots,c_{n-1}$ be complex
numbers with $\sum_{k<n}|c_k|^2/\binom nk\le1$. Then
$$
q(z)=(1+z)^n+\sum_{k<n}c_kz^k
$$
has no zero with $\operatorname{Re}z>0$. If $n\ge1$ and $q$ has a zero with
$\operatorname{Re}z\ge0$, then that zero is $0$, $c_0=-1$ and $c_k=0$ for $0<k<n$.

**Theorem (common interlacer).** Let $n\ge1$, let $E_n(x)=\sum_k\binom{2n}{2k}x^k$ and
$O_n(x)=\sum_k\binom{2n}{2k+1}x^k$ be the even and odd binomial sections, and for real $a_j$
put
$$
G_a(x)=E_n(x)+\sum_{j=1}^{\lfloor n/2\rfloor}a_j\,x^j(1+x)^{n-2j},
\qquad
\sum_{j=1}^{\lfloor n/2\rfloor}\frac{a_j^2}{16^j\binom n{2j}}\le1 .
$$
Then $G_a$ is real-rooted with only negative roots and $O_n\ll G_a$. For any two such vectors
$a$, $b$, the polynomials $G_a$ and $G_b$ are compatible: every combination
$\alpha G_a+\beta G_b$ with $\alpha,\beta\ge0$ is zero or real-rooted.

**Theorem (away from one parameter).** Call $a$ exceptional if $n=2m$, $a_m=-2^n$ and
$a_j=0$ for all other $j\le n/2$. Let $n\ge1$ and let $a$ be non-exceptional with the bound
above. Then $x\,O_n(x^2)+G_a(x^2)$ has all zeros in the open left half-plane, the roots of $O_n$
are simple, the roots of $G_a$ are simple, and $O_n$ and $G_a$ have no common root.

## Use

We obtain the second theorem from the first via a Joukowski substitution. For $a=0$ the
polynomial $x\,O_n(x^2)+E_n(x^2)$ is $(1+x)^{2n}$. For Hurwitz-stability background, see the
[Garloff–Wagner page](rr:garloff-wagner-hurwitz).

## References

No published source is cited for these results.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.ClassicalHurwitzMatrix.Stability.BinomialPerturbation`.
-/
