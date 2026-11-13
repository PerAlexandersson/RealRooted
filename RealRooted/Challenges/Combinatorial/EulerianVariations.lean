module

import RealRooted.Applications.EulerianVariations.CyclicPathDescents
import RealRooted.Applications.EulerianVariations.TernaryRuns
import RealRooted.CombinatorialExamples.PeakValues.WeightedInterleaving
import RealRooted.CombinatorialExamples.SuperEulerian

/-!
# Eulerian variations challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "eulerian-variations"
formalized = "2026-09-09"
tags = ["coauthored-paper"]
references = [
  "Alexandersson2026Eulerian",
]
authors = ["Alexandersson", "Shankar"]
years = [2026]

[[definitions]]
name = "RealRooted.Applications.EulerianVariations.cyclicPathDescentPolynomial"
module = "RealRooted.Applications.EulerianVariations.CyclicPathDescents"
label = "Cyclic path descent polynomial Σ 2 C(n,k) C(n-1,k-1) x^k"

[[definitions]]
name = "RealRooted.Applications.EulerianVariations.ternaryRunPolynomial"
module = "RealRooted.Applications.EulerianVariations.TernaryRuns.Recurrence"
label = "Ternary run polynomials, defined by a first-order differential recurrence"

[[definitions]]
name = "RealRooted.peakValuePolynomial"
module = "RealRooted.CombinatorialExamples.PeakValues"
label = "Multivariate peak-value polynomial"

[[definitions]]
name = "RealRooted.SuperEulerian.superEulerian"
module = "RealRooted.CombinatorialExamples.SuperEulerian"
label = "Super-Eulerian polynomial"

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.cyclicPathDescentPolynomial_roots"
module = "RealRooted.Applications.EulerianVariations.CyclicPathDescents"
label = "Simple roots of the cyclic path descent polynomial: 0 and n - 1 negative"

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.cyclicPathDescentPolynomial_eq_derivative"
module = "RealRooted.Applications.EulerianVariations.CyclicPathDescents"
label = "The cyclic path descent polynomial is (2/n) x B_n'(x) for the type B Narayana B_n"

[[theorems]]
name = "RealRooted.peakValuePolynomial_mvRealStable"
module = "RealRooted.CombinatorialExamples.PeakValues.Stability"
label = "The peak-value polynomial K_n is real stable"
headline = true

[[theorems]]
name = "RealRooted.peakValueWeightedDiagonal_consecutive_strictInterl"
module = "RealRooted.CombinatorialExamples.PeakValues.WeightedInterleaving"
label = "Positive weighted diagonals of K_n and K_{n+1} interlace"

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.ternaryRunPolynomial_isPF"
module = "RealRooted.Applications.EulerianVariations.TernaryRuns"
label = "Ternary run polynomials are Pólya frequency polynomials"

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.ternaryRunPolynomial_strictInterl"
module = "RealRooted.Applications.EulerianVariations.TernaryRuns"
label = "Consecutive ternary run polynomials interlace"

[[theorems]]
name = "RealRooted.SuperEulerian.isRealRooted_superEulerian"
module = "RealRooted.CombinatorialExamples.SuperEulerian"
label = "For ℓ ≥ 1, super-Eulerian polynomials are nonzero and real-rooted"

[[theorems]]
name = "RealRooted.SuperEulerian.strictInterl_superEulerian_succ"
module = "RealRooted.CombinatorialExamples.SuperEulerian"
label = "For ℓ ≥ 1, consecutive super-Eulerian polynomials interlace, without common roots"

[[theorems]]
name = "RealRooted.SuperEulerian.exists_gamma_superEulerian"
module = "RealRooted.CombinatorialExamples.SuperEulerian"
label = "Super-Eulerian gamma-polynomials are real-rooted with nonnegative coefficients"
-->

<!-- realrooted-catalog-content -->
# Real-rooted Eulerian variations

Cyclic path descent polynomials, ternary-run polynomials and super-Eulerian polynomials are
real-rooted, the peak-value polynomial is real stable, and consecutive members of the families
interlace.

## Results

A polynomial is a *Pólya frequency (PF) polynomial* if it has nonnegative coefficients and only
real nonpositive roots.

**Cyclic path descents.** For $n\ge1$ let
$$
C_n(x)=\sum_{k=1}^{n}2\binom nk\binom{n-1}{k-1}x^k=\frac2n\,x\,B_n'(x),\qquad
B_n(x)=\sum_k\binom nk^2x^k,
$$
where $B_n$ is the type $B$ Narayana polynomial. Then $C_n$ has simple roots: $0$ and $n-1$
negative roots.

**Peak values.** For a permutation $\pi$, let $\operatorname{PeakVal}(\pi)$ be the set of values
at its interior peaks, and put
$K_n(\mathbf x)=\sum_{\pi\in\mathfrak S_n}\prod_{v\in\operatorname{PeakVal}(\pi)}x_v$. Then $K_n$
is real stable for every $n$. For $n\ge1$ and positive weights $w_1,\dots,w_{n+1}$,
$$
K_n(w_1x,\dots,w_nx)\ \ll\ K_{n+1}(w_1x,\dots,w_{n+1}x).
$$

**Ternary runs.** Let $T_0=1$ and
$$
(n+1)\,T_{n+1}=3x(1-x)\,T_n'+\bigl(-n+(4n+3)x\bigr)\,T_n .
$$
Then every $T_n$ is a PF polynomial and $T_n\ll T_{n+1}$. The polynomial $T_n$ is
$\sum_{w\in\{0,1,2\}^n}x^{\operatorname{runs}(w)}$, where $\operatorname{runs}(w)$ is the number of
maximal strictly increasing runs of $w$; see the
[Eulerian compendium](rr:eulerian-compendium).

**Super-Eulerian polynomials.** For an integer $\ell\ge1$ let $E_{1,0}=1$ and
$E_{n,k}=(k+1)^\ell E_{n-1,k}+(n-k)^\ell E_{n-1,k-1}$, with entries outside $0\le k\le n-1$
equal to zero, and put $E_n^{(\ell)}(x)=\sum_{k<n}E_{n,k}x^k$. For $n\ge1$, $E^{(\ell)}_n$ is
nonzero and real-rooted, $E^{(\ell)}_n\ll E^{(\ell)}_{n+1}$, and the two have no common root.
Moreover $E^{(\ell)}_{n+1}$ has a gamma-polynomial $\gamma$ with $\deg\gamma\le n/2$ that is
nonzero and real-rooted, with nonpositive roots and nonnegative coefficients.

## Use

The [Eulerian compendium](rr:eulerian-compendium) identifies $C_n$ with the
balanced cyclic-word polynomial and $T_n$ with the run enumerator of ternary words.

## References

- [@Alexandersson2026Eulerian]
<!-- /realrooted-catalog-content -->

This module is a catalog facade.  The proofs live in
`RealRooted.Applications.EulerianVariations`.
-/
