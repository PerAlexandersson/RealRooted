module

import RealRooted.Applications.EulerianCompendium.CyclicWords
import RealRooted.Applications.EulerianCompendium.Definitions
import RealRooted.Applications.EulerianCompendium.Results
import RealRooted.Applications.EulerianVariations.CyclicPathDescents
import RealRooted.Applications.EulerianVariations.TernaryRuns
import RealRooted.CombinatorialExamples.PeakValues
import RealRooted.CombinatorialExamples.SuperEulerian
import RealRooted.EulerianMixedCompatibility
import RealRooted.EulerianMixedCompatibility.Insertion

/-!
# Real-rootedness of Eulerian-type polynomials (Alexandersson 2026)

<!-- realrooted-catalog
version = 1
kind = "landmark"
section = "theorems"
slug = "eulerian-compendium"
formalized = "2026-10-24"
tags = ["coauthored-paper"]
references = [
  "Alexandersson2026Eulerian",
  "FuLinZeng2018",
  "Shankar2026x",
]
authors = ["Alexandersson", "Shankar"]
years = [2026]

[[definitions]]
name = "RealRooted.EulerianCompendium.derangementDescentPolynomial"
module = "RealRooted.Applications.EulerianCompendium.Definitions"
label = "Derangement descent polynomial Σ x^des π"

[[definitions]]
name = "RealRooted.EulerianCompendium.BalancedCyclic.balancedWordSum"
module = "RealRooted.Applications.EulerianCompendium.CyclicWords"
label = "Balanced cyclic-word polynomial Σ x^cdes w"

[[definitions]]
name = "RealRooted.EulerianCompendium.evenTopDescentPolynomial"
module = "RealRooted.Applications.EulerianCompendium.Definitions"
label = "Even-top descent polynomial of permutations"

[[definitions]]
name = "RealRooted.SuperEulerian.superEulerian"
module = "RealRooted.CombinatorialExamples.SuperEulerian"
label = "Super-Eulerian polynomial"

[[definitions]]
name = "RealRooted.EulerianCompendium.peakPolynomial"
module = "RealRooted.Applications.EulerianCompendium.Definitions"
label = "Peak polynomial of permutations"

[[definitions]]
name = "RealRooted.peakValuePolynomial"
module = "RealRooted.CombinatorialExamples.PeakValues"
label = "Multivariate peak-value polynomial"

[[definitions]]
name = "RealRooted.eulerInsertionStep"
module = "RealRooted.EulerianMixedCompatibility.Insertion"
label = "Euler insertion operator E_{c,d}"

[[theorems]]
objects = ["Descent polynomials of derangements"]
name = "RealRooted.EulerianCompendium.Challenges.derangementDescent_realRooted"
module = "RealRooted.Applications.EulerianCompendium.Results"
label = "Alexandersson: descent polynomials of derangements are real-rooted"
headline = true

[[theorems]]
objects = ["Cyclic descent polynomials of balanced binary words"]
name = "RealRooted.EulerianCompendium.Challenges.cyclicWordDescent_roots"
module = "RealRooted.Applications.EulerianCompendium.Results"
label = "Balanced cyclic-word polynomials: simple roots, one at 0, the rest negative"

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.cyclicPathDescentPolynomial_eq_derivative"
module = "RealRooted.Applications.EulerianVariations.CyclicPathDescents"
label = "The cyclic descent polynomial is (2/n) x B_n′(x) for the type B Narayana B_n"

[[theorems]]
objects = ["Even-top descent polynomials"]
property = "interlacing"
name = "RealRooted.EulerianCompendium.Challenges.evenTopDescent_strictAlternation"
module = "RealRooted.Applications.EulerianCompendium.Results"
label = "Even-top descent polynomials have negative roots that strictly alternate"

[[theorems]]
name = "RealRooted.SuperEulerian.isRealRooted_superEulerian"
module = "RealRooted.CombinatorialExamples.SuperEulerian"
label = "For ℓ ≥ 1, super-Eulerian polynomials are nonzero and real-rooted"

[[theorems]]
objects = ["Super-Eulerian polynomials"]
property = "interlacing"
name = "RealRooted.SuperEulerian.strictInterl_superEulerian_succ"
module = "RealRooted.CombinatorialExamples.SuperEulerian"
label = "For ℓ ≥ 1, consecutive super-Eulerian polynomials interlace, without common roots"

[[theorems]]
objects = ["Super-Eulerian polynomials"]
property = "gamma-positive"
name = "RealRooted.SuperEulerian.exists_gamma_superEulerian"
module = "RealRooted.CombinatorialExamples.SuperEulerian"
label = "Super-Eulerian gamma-polynomials are real-rooted with nonnegative coefficients"

[[theorems]]
name = "RealRooted.EulerianCompendium.Challenges.ternaryWordRun_realRooted_interlaces"
module = "RealRooted.Applications.EulerianCompendium.Results"
label = "Run polynomials of ternary words are real-rooted and interlace"

[[theorems]]
objects = ["Ternary-word run polynomials"]
property = "pf"
name = "RealRooted.Applications.EulerianVariations.ternaryRunPolynomial_isPF"
module = "RealRooted.Applications.EulerianVariations.TernaryRuns"
label = "Ternary run polynomials are Pólya frequency polynomials"

[[theorems]]
objects = ["Ternary-word run polynomials"]
property = "interlacing"
name = "RealRooted.Applications.EulerianVariations.ternaryRunPolynomial_strictInterl"
module = "RealRooted.Applications.EulerianVariations.TernaryRuns"
label = "Consecutive ternary run polynomials interlace"

[[theorems]]
objects = ["Peak polynomials of permutations"]
property = "interlacing"
name = "RealRooted.EulerianCompendium.Challenges.peakPolynomial_roots"
module = "RealRooted.Applications.EulerianCompendium.Results"
label = "Peak polynomials have negative roots that strictly alternate"

[[theorems]]
objects = ["Peak-value polynomials"]
property = "real-stable"
name = "RealRooted.EulerianCompendium.peakValue_stability_and_weightedInterlacing"
module = "RealRooted.Applications.EulerianCompendium.Results"
label = "Peak-value polynomials are real stable; weighted diagonals interlace"

[[theorems]]
name = "RealRooted.compatible_eulerInsertionStep_one_zero_succ"
module = "RealRooted.EulerianMixedCompatibility"
label = "Adjacent Euler insertion steps of an interlacing pair are compatible"
-->

<!-- realrooted-catalog-content -->
# Real-rootedness of Eulerian-type polynomials (Alexandersson 2026)

Alexandersson proves real-rootedness, mostly with interlacing of consecutive members, for seven
families of Eulerian type: descents of derangements, cyclic descents of balanced words,
even-top descents, super-Eulerian polynomials, runs of ternary words, peaks and peak values.
This settles the derangement part of a conjecture of Fu, Lin and Zeng.

## Results

The following are the main theorems of [@Alexandersson2026Eulerian].

1. **Derangements** (Thm. 2.1). For $n\ge2$, the polynomial
   $\sum_{\pi\in\mathfrak D_n}x^{\operatorname{des}\pi}$ over derangements is nonzero and
   real-rooted with all roots nonpositive. This is the derangement part of
   [@FuLinZeng2018, Conj. 5.2].
2. **Balanced cyclic words** (Thm. 3.1). For $n\ge1$, let $w$ range over binary words of length
   $2n$ with exactly $n$ ones, and let $\operatorname{cdes}w$ count the cyclic positions $i$ with
   $w_i=1$ and $w_{i+1}=0$. Then
   $$C_n(x)=\sum_w x^{\operatorname{cdes}w}=\sum_{k=1}^n2\binom nk\binom{n-1}{k-1}x^k
   =\frac2n\,x\,B_n'(x),$$
   where $B_n(x)=\sum_k\binom nk^2x^k$, has simple roots: $0$ and $n-1$ negative ones.
3. **Even-top descents** (Thm. 4.1). Let $\operatorname{edes}\pi$ count the descents
   $\pi_j>\pi_{j+1}$ with $\pi_j$ even. For $n\ge2$,
   $\sum_{\pi\in\mathfrak S_n}x^{\operatorname{edes}\pi}$ has simple negative roots, and its
   roots strictly alternate with those of the same polynomial for $n+1$.
4. **Super-Eulerian polynomials** (Thm. 5.1). Let $E^{(\ell)}_{1,0}=1$ and
   $E^{(\ell)}_{n,k}=(k+1)^\ell E^{(\ell)}_{n-1,k}+(n-k)^\ell E^{(\ell)}_{n-1,k-1}$, with entries
   outside $0\le k\le n-1$ equal to zero, and $A^{(\ell)}_n=\sum_{k<n}E^{(\ell)}_{n,k}x^k$. For
   $\ell\ge1$, $A^{(\ell)}_{n+1}$ is real-rooted, $A^{(\ell)}_{n+1}\ll A^{(\ell)}_{n+2}$ without
   common roots [@Shankar2026x, Thm. C], and
   $A^{(\ell)}_{n+1}(x)=\sum_{i}\gamma_i\,x^i(1+x)^{n-2i}$ with $\gamma$ real-rooted with
   nonnegative coefficients.
5. **Ternary words** (Thm. 6.1). For $w\in\{0,1,2\}^n$ let $\operatorname{run}w$ be the number
   of maximal strictly increasing runs. Then $T_n(x)=\sum_w x^{\operatorname{run}w}$ is a Pólya
   frequency polynomial and $T_n\ll T_{n+1}$.
6. **Peaks** (Thm. 6.2). The peak polynomial $\sum_{\pi\in\mathfrak S_n}x^{\operatorname{pk}\pi}$
   has negative roots for $n\ge3$, which strictly alternate with those for $n+1$. Real-rootedness
   and interlacing are due to D. Warren and E. Seneta, "Peaks and Eulerian numbers in a random
   sequence," *J. Appl. Probab.* 33 (1996), 101–114.
7. **Peak values** (Thm. 6.3). Let $K_n(z_1,\dots,z_n)=\sum_{\pi\in\mathfrak S_n}\prod z_v$, with
   $v$ ranging over the values at the peaks of $\pi$. Then $K_n$ is real stable, and for positive
   $w_1,w_2,\dots$ the polynomial $K_n(w_1x,\dots,w_nx)$ interlaces
   $K_{n+1}(w_1x,\dots,w_{n+1}x)$. This settles [@AlexanderssonNabawanda2021, Conj. 4.1].

The paper also proves the conjecture on [zig-zag Eulerian polynomials](rr:zigzag-eulerian).

**Theorem (compatible Euler steps).** Let $E_{c,d}\,p=\bigl(c+(d+1)x\bigr)p+(x-x^2)p'$. If $f,g$
have nonnegative coefficients and positive leading coefficients, $g\ll f$,
$\deg f=\deg g+1$ and $\deg f\le n+1$, then $E_{1,n}\,g$ and $E_{0,n+1}\,f$ are compatible:
every nonnegative combination of them is zero or real-rooted.

## Proof

The reciprocal derangement polynomials lie in a two-parameter family whose recurrence adds
$E_{1,n}$ and $E_{0,n+1}$ applied to an interlacing pair, so compatibility gives real-rootedness
by induction. The cyclic-word polynomial is a derivative of a real-rooted polynomial, and the
super-Eulerian theorem uses Hadamard products.

## References

[@Alexandersson2026Eulerian]; [@FuLinZeng2018, Conj. 5.2]; [@Shankar2026x, Thm. C].
<!-- /realrooted-catalog-content -->
-/
