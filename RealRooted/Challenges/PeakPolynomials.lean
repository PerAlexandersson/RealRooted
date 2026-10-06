import RealRooted.Applications.PeakPolynomials.PeakInduction

/-!
# Peak polynomials on Ferrers boards challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "peak-polynomials"
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

We formalize the algebraic induction behind the real-rootedness of peak
polynomials on Ferrers boards.

A **peak family** of width $m$ consists of polynomials $D_k$ and $U_k$,
$0 \le k < m$, with nonnegative coefficients. We put
$$
A_k = D_k + U_k, \qquad W_k = x D_k + U_k, \qquad
S_k = \sum_{j < k} A_j, \qquad T_k = \sum_{j \ge k} W_j,
$$
and call $P = \sum_k A_k$ the **total peak polynomial**. We write $f \ll g$ for
weak interlacing in which either polynomial may be zero: either $f = 0$, or
$g = 0$, or both are nonzero and real-rooted and $f$ is interlaced by $g$: their
zeros alternate, and the largest zero belongs to $g$. The family satisfies the **six conditions** if

- (a) $D_j \ll U_l$ for all $j, l$;
- (b) $U_j \ll U_l$ for $j \le l$;
- (c) $A_j \ll W_l$ for all $j, l$;
- (d) $D_j \ll D_{j'}$ for $j' < j$;
- (e) $A_j \ll A_{j'}$ for $j' < j$;
- (f) $W_j \ll W_l$ for $j \le l$.

The recursion has two steps. For a map $\iota$ from $\{0, \dots, m' - 1\}$ to
$\{0, \dots, m - 1\}$, the **next-level family** of width $m'$ has
$D^+_k = S_{\iota(k)}$ and $U^+_k = T_{\iota(k)}$. The **boundary family** of
width $m + 1$ has $D^+_k = S_k$ and $U^+_k = T_k$ for $k < m$, together with
$D^+_m = P$ and $U^+_m = 0$. The **base family** has width $1$, $D_0 = 0$ and
$U_0 = 1$. A family is **reachable** if it is obtained from the base family by
finitely many next-level steps along monotone maps $\iota$ and boundary steps.

**Theorem.** If a peak family is reachable and some $A_k$ is nonzero, then its
total peak polynomial $P$ is nonzero and real-rooted.

Along the way we show that the base family satisfies the six conditions and
that both recursion steps preserve them, the next-level step for every monotone
map $\iota$. Every reachable family therefore satisfies the six conditions.

## Proof idea

The next-level differences have the form
$W^+_l - A^+_k = (x - 1) H$, $A^+_{k'} - A^+_k = (x - 1) H$ and
$W^+_l - W^+_k = (x - 1) H$ for explicit polynomials $H$ with nonnegative
coefficients. The shift lemma states that if $h \ll f$ are nonzero, have
nonpositive zeros and positive leading coefficients, and $h(0) \le f(0)$, then
$f \ll f + (x - 1) h$. It reduces each of the conditions (c), (e) and (f) to an
interlacing $H \ll A^+_k$ or $H \ll W^+_k$. We prove these with the left and
right cone lemmas for nonnegative sums and with Wagner's lemma that $f \ll g$
implies $g \ll x f$ when both have nonnegative coefficients. Conditions (a),
(b) and (d) follow from the cone lemmas alone. The real-rootedness of $P$
follows from (c), since $P \ll W_k$ with $W_k \ne 0$.

The paper's Ferrers boards and peak-generating permutations, and the
identification of their refined peak polynomials with this abstract recursion,
are not formalized. The related conditional step for restricted hit
polynomials depends on an open conjecture and is not part of this page.

## References

P. Alexandersson, A. Jal and M. Quemener, “Rook-Eulerian polynomials and
permutation ideals,” manuscript, Theorem `thm:peak_rr_ferrers` and
Lemma `lem:t_minus_1`. For peaks of permutations, see the
[entry on symmetricfunctions.com](https://www.symmetricfunctions.com/gammaPositivity.htm#permutationPeak).
<!-- /realrooted-catalog-content -->

This module is a catalog facade. The proofs live in
`RealRooted.Applications.PeakPolynomials.PeakInduction`.
-/
