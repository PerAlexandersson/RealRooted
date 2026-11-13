module

import RealRooted.Applications.PeakPolynomials.PeakInduction

/-!
# Peak polynomials on Ferrers boards challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "peak-polynomials"
formalized = "2026-07-01"
references = []
tags = ["coauthored-paper"]
authors = ["Alexandersson", "Jal", "Quemener"]

[[definitions]]
name = "RealRooted.Applications.PeakPolynomials.PeakFamily"
module = "RealRooted.Applications.PeakPolynomials.PeakInduction"
label = "A peak family of width m"

[[definitions]]
name = "RealRooted.Applications.PeakPolynomials.PeakFamily.A"
module = "RealRooted.Applications.PeakPolynomials.PeakInduction"
label = "A_k = D_k + U_k"

[[definitions]]
name = "RealRooted.Applications.PeakPolynomials.PeakFamily.W"
module = "RealRooted.Applications.PeakPolynomials.PeakInduction"
label = "W_k = x D_k + U_k"

[[definitions]]
name = "RealRooted.Applications.PeakPolynomials.PeakFamily.P"
module = "RealRooted.Applications.PeakPolynomials.PeakInduction"
label = "The total peak polynomial"

[[definitions]]
name = "RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions"
module = "RealRooted.Applications.PeakPolynomials.PeakInduction"
label = "The six interlacing conditions"

[[definitions]]
name = "RealRooted.Applications.PeakPolynomials.PeakFamily.next"
module = "RealRooted.Applications.PeakPolynomials.PeakInduction"
label = "The next-level family along a map of cut positions"

[[definitions]]
name = "RealRooted.Applications.PeakPolynomials.PeakFamily.nextBoundary"
module = "RealRooted.Applications.PeakPolynomials.PeakInduction"
label = "The next-level family with an extra boundary index"

[[definitions]]
name = "RealRooted.Applications.PeakPolynomials.PeakFamily.base"
module = "RealRooted.Applications.PeakPolynomials.PeakInduction"
label = "The base family"

[[definitions]]
name = "RealRooted.Applications.PeakPolynomials.PeakFamily.IsReachable"
module = "RealRooted.Applications.PeakPolynomials.PeakInduction"
label = "Families reachable from the base family"

[[theorems]]
name = "RealRooted.Applications.PeakPolynomials.PeakFamily.IsReachable.isRealRooted_P"
module = "RealRooted.Applications.PeakPolynomials.PeakInduction"
label = "The total peak polynomial of a reachable family is real-rooted"
headline = true

[[theorems]]
name = "RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.next"
module = "RealRooted.Applications.PeakPolynomials.PeakInduction"
label = "The six conditions pass to the next-level family"

[[theorems]]
name = "RealRooted.Applications.PeakPolynomials.PeakFamily.Conditions.nextBoundary"
module = "RealRooted.Applications.PeakPolynomials.PeakInduction"
label = "The six conditions pass to the boundary family"

[[theorems]]
name = "RealRooted.Applications.PeakPolynomials.PeakFamily.conditions_base"
module = "RealRooted.Applications.PeakPolynomials.PeakInduction"
label = "The base family satisfies the six conditions"
-->

<!-- realrooted-catalog-content -->
# Peak polynomials on Ferrers boards

The total peak polynomial of a peak family built by the Ferrers-board recursion is real-rooted.

## Results

We use the [zero-aware interlacing convention](rr:about). A *peak family* of width $m$ consists of
polynomials $D_k$ and
$U_k$, $0\le k<m$, with nonnegative coefficients. Put
$$
A_k = D_k + U_k, \qquad W_k = x D_k + U_k, \qquad
S_k = \sum_{j < k} A_j, \qquad T_k = \sum_{j \ge k} W_j,
$$
and let $P=\sum_k A_k$ be the *total peak polynomial*. The family satisfies the *six conditions* if

- (a) $D_j \ll U_l$ for all $j, l$;
- (b) $U_j \ll U_l$ for $j \le l$;
- (c) $A_j \ll W_l$ for all $j, l$;
- (d) $D_j \ll D_{j'}$ for $j' < j$;
- (e) $A_j \ll A_{j'}$ for $j' < j$;
- (f) $W_j \ll W_l$ for $j \le l$.

For a map $\iota\colon\{0,\dots,m'-1\}\to\{0,\dots,m-1\}$, the *next-level family* of width $m'$ has
$D^+_k=S_{\iota(k)}$ and $U^+_k=T_{\iota(k)}$. The *boundary family* of width $m+1$ has
$D^+_k=S_k$ and $U^+_k=T_k$ for $k<m$, and $D^+_m=P$, $U^+_m=0$. The *base family* has width
$1$, $D_0=0$ and $U_0=1$. A family is *reachable* if it arises from the base family by finitely
many next-level steps along monotone maps $\iota$ and boundary steps.

**Proposition (recursion).** The base family satisfies the six conditions. If a family satisfies
them, so do its boundary family and its next-level family along every monotone $\iota$. Hence
every reachable family satisfies the six conditions.

**Theorem.** Let a peak family satisfy the six conditions, in particular any reachable family.
If some $A_k$ is nonzero, then $P$ is nonzero and real-rooted.

## Proof

By the shift lemma, if $h\ll f$ have nonnegative coefficients, $f$ is real-rooted and
$h(0)\le f(0)$, then $f\ll f+(x-1)h$. The differences $W^+_l-A^+_k$, $A^+_{k'}-A^+_k$ and
$W^+_l-W^+_k$ of a next-level family are $(x-1)H$ with $H$ having nonnegative coefficients, and
the shift lemma reduces conditions (c), (e) and (f) to interlacings of such $H$. Finally
$P\ll W_k$ for every $k$, and $W_k\ne0$ when $A_k\ne0$.

## References

The recursion is that of P. Alexandersson, A. Jal and M. Quemener, “Rook-Eulerian polynomials
and permutation ideals,” manuscript (2026), Theorem `thm:peak_rr_ferrers` and Lemma
`lem:t_minus_1`. The identification of the refined peak polynomials of a Ferrers board with this
recursion is their Lemma `lem:peakDURecursion`. For peaks of permutations, see the
[entry on symmetricfunctions.com](sf:permutationPeak).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.Applications.PeakPolynomials.PeakInduction`.
-/
