module

import RealRooted.CombinatorialExamples.BigDescents321

/-!
# Real roots of big-descent polynomials of 321-avoiding permutations

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "big-descents-321"
formalized = "2026-10-06"
tags = ["realrooted-original"]
references = [
  "ElizaldeRiveraZhuang2026",
]
authors = ["Elizalde", "Rivera", "Zhuang", "Alexandersson"]
years = [2024, 2026]

[[definitions]]
name = "RealRooted.BigDescents321.bigDescentPoly"
module = "RealRooted.CombinatorialExamples.BigDescents321.Basic"
label = "Big-descent polynomial of 321-avoiders"

[[definitions]]
name = "RealRooted.BigDescents321.motzkinRef"
module = "RealRooted.CombinatorialExamples.BigDescents321.Basic"
label = "Reference Motzkin polynomial"

[[theorems]]
name = "RealRooted.BigDescents321.motzkinRef_interl_bigDescentPoly_and_noCommonRoots"
module = "RealRooted.CombinatorialExamples.BigDescents321"
label = "For n ≥ 3, M_{n-2} interlaces A_n; both have simple roots and no common root"
headline = true

[[theorems]]
name = "RealRooted.BigDescents321.bigDescentPoly_splits"
module = "RealRooted.CombinatorialExamples.BigDescents321"
label = "A_n is real-rooted for every n"

[[theorems]]
name = "RealRooted.BigDescents321.neg_of_isRoot_bigDescentPoly"
module = "RealRooted.CombinatorialExamples.BigDescents321"
label = "Every root of A_n is negative"
-->

<!-- realrooted-catalog-content -->
# Real roots of big-descent polynomials of 321-avoiding permutations

The big-descent polynomials of 321-avoiding permutations are real-rooted with negative roots, and
the Motzkin reference polynomials interlace them.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
A *big descent* of a permutation $\pi$ is an index $i$ with $\pi(i)>\pi(i+1)+1$. Let $A_n(t)$
be the big-descent polynomial of the 321-avoiding permutations of length $n$. We define it by
the first-return recurrence $A_0=1$, $A_n=\sum_{j=1}^n I_jA_{n-j}$, where $I_1=I_2=1$ and
$I_j=t\,M_{j-2}$ for $j\ge3$. The reference Motzkin polynomials are $M_0=1$, $M_1=2$ and
$$
M_{k+2}=2M_{k+1}+t\sum_{i=0}^{k}M_iM_{k-i},\qquad
M_k=\sum_a\binom{k}{2a}\mathrm{Cat}_a\,2^{k-2a}t^a.
$$

**Theorem.** For every $n\ge0$, $A_n$ is real-rooted and all its roots are negative. For $n\ge3$,
$M_{n-2}\ll A_n$, both polynomials have simple roots, and they have no common root.

## Use

By [@ElizaldeRiveraZhuang2026], the recurrence-defined $A_n$ is the big-descent enumerator of
321-avoiding permutations of length $n$. Together with that identification the theorem proves
the case $\Pi=\{321\}$ of [@ElizaldeRiveraZhuang2026, Conj. 4.4]. See also
[big descents on symmetricfunctions.com](sf:bigDescent).

## Proof

For $n\ge25$ we expand $(c/2)^nA_n(1-c^{-2})$ in Gegenbauer polynomials and show
$A_n(\rho)M_{n-2}'(\rho)<0$ at every zero $\rho$ of $M_{n-2}$, which gives interlacing. The cases
$3\le n\le24$ are exact certificates.

## References

- [@ElizaldeRiveraZhuang2026]
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CombinatorialExamples.BigDescents321`.
-/
