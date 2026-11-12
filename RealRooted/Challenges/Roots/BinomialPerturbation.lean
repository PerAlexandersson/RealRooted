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
label = "On the boundary of the bound, the only zero on the closed right half-plane is 0"

[[theorems]]
name = "RealRooted.binomialPerturbationFamily_negativeRoots_interlaced"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.BinomialPerturbation"
label = "The family is real-rooted with negative roots and interlaced by the odd binomial section"
headline = true

[[theorems]]
name = "RealRooted.oddEvenPolynomial_binomialPerturbationFamily_strictlyStable"
module = "RealRooted.ClassicalHurwitzMatrix.Stability.BinomialPerturbation"
label = "The odd–even polynomial is strictly Hurwitz stable away from one exceptional parameter"

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

**Right-half-plane stability.** For $n\ge0$ and complex numbers $c_0,\dots,c_{n-1}$ let
$$
q(z)=(1+z)^n+\sum_{k<n}c_kz^k .
$$
If $\sum_{k<n}|c_k|^2/\binom nk\le1$, then $q$ has no zero in the open right half-plane,
and on the boundary of this bound the only zero in the closed right half-plane is $0$,
attained exactly for $c_0=-1$ and all other $c_k=0$.

**A common interlacer.** Let $E_n(x)=\sum_k\binom{2n}{2k}x^k$ and
$O_n(x)=\sum_k\binom{2n}{2k+1}x^k$ be the even and odd binomial sections, so that the odd--even
polynomial $\sum_kO_{n,k}x^{2k+1}+\sum_kE_{n,k}x^{2k}$ built from them is $(1+x)^{2n}$. For real
$a_j$ put
$$
G_a(x)=E_n(x)+\sum_{j=1}^{\lfloor n/2\rfloor}a_j\,x^j(1+x)^{n-2j},
$$
and require the ellipsoidal condition
$\sum_{j}a_j^2/\bigl(16^j\binom n{2j}\bigr)\le1$. Via a Joukowski substitution, the
stability statement shows that $G_a$ is real-rooted with only negative roots and is
interlaced by the fixed odd section $O_n$. Away from the single exceptional parameter
vector ($n=2m$, $a_m=-2^n$, all other $a_j=0$), the odd--even polynomial built from
$O_n$ and $G_a$ is strictly Hurwitz stable, the roots of $O_n$ and $G_a$ are simple and
disjoint, and any two members of the family are compatible.

## What is new

These results were developed in this library; no published source is cited, and we
attribute none. For the Hurwitz-stability background, see the
[Garloff–Wagner page](/RealRooted/theorems/garloff-wagner-hurwitz/).

## References

No published source is cited for these results in the formalization.
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.ClassicalHurwitzMatrix.Stability.BinomialPerturbation`.
-/
