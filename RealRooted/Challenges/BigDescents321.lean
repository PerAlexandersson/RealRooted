module

public import RealRooted.CombinatorialExamples.BigDescents321

/-!
# 321-avoiding permutations by big descents challenge entry point

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
label = "Motzkin interlacing, simple roots and no common roots"
headline = true

[[theorems]]
name = "RealRooted.BigDescents321.bigDescentPoly_splits"
module = "RealRooted.CombinatorialExamples.BigDescents321"
label = "The big-descent polynomials are real-rooted"

[[theorems]]
name = "RealRooted.BigDescents321.neg_of_isRoot_bigDescentPoly"
module = "RealRooted.CombinatorialExamples.BigDescents321"
label = "All roots are negative"
-->

<!-- realrooted-catalog-content -->
# 321-avoiding permutations by big descents

A *big descent* of a permutation $\pi$ is an index $i$ with $\pi(i) > \pi(i+1) + 1$. Let
$A_n(t) = \sum_{\pi} t^{\operatorname{bdes}(\pi)}$, summed over 321-avoiding permutations of
length $n$. Its generating function is
$$
\sum_{n \ge 0} A_n(t)\, x^n = \frac{2}{1 - 2(1-t)x^2 + \sqrt{1 - 4x + 4(1-t)x^2}},
$$
and in Lean $A_n$ is defined by the equivalent first-return recurrence. Let
$M_k(t) = \sum_a \binom{k}{2a} \mathrm{Cat}_a\, 2^{k-2a} t^a$ be the reference Motzkin
polynomials.

**Theorem.** For every $n \ge 0$, $A_n$ is real-rooted. For $n \ge 3$, all roots of $A_n$ are
simple and strictly negative, $M_{n-2}$ interlaces $A_n$, and the two polynomials have no common
root.

Together with the recurrence identification of Elizalde, Rivera and Zhuang,
this proves the case $\Pi = \{321\}$ of their Conjecture 4.4
[@ElizaldeRiveraZhuang2026, Conj. 4.4]. Lean verifies the recurrence-defined
polynomials; the identification with the permutation enumerator is taken from
their paper. See also
[big descents on symmetricfunctions.com](sf:bigDescent).

## Proof idea

Put $Q_n(c) = (c/2)^n A_n(1 - c^{-2})$ and expand it in the Gegenbauer polynomials
$G_j = C_j^{(3/2)}$. A kernel formula writes the coordinates $q_{n,j}$ through moments of
$\sqrt{1 - v(2-v)y + (v/4)y^2}$.

1. A universal polynomial certificate with natural-number Bernstein coefficients, checked by
   kernel reduction, proves $(J+1)q_{J+2r,J} > J\,q_{J+2r,J-2}$ for $r \ge 6$.
2. The residual $R_n = ((\alpha_n c^2 + \beta_n)G_{n-2} - Q_n)/c$ then has negative coordinates
   in its tail, using Lucas closed forms for the bottom coordinates.
3. A moving interval for $z_n = \beta_n/\alpha_n$, from exact bases $25 \le n \le 70$ and a
   scalar recurrence, controls the top coordinates.
4. A weighted-path envelope for the backward Gegenbauer recurrence turns these signs into the
   positivity of $-Q_n(a)/(a\,G_{n-3}(a))$ at every zero $a$ of $G_{n-2}$.
5. The substitution $\rho = 1 - a^{-2}$ gives $A_n(\rho) M_{n-2}'(\rho) < 0$ at every zero of
   $M_{n-2}$, which yields interlacing.

The cases $n \le 24$ are exact interlacing and Bezout certificates.

## References

See [@ElizaldeRiveraZhuang2026].
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.CombinatorialExamples.BigDescents321`.
-/

public section
