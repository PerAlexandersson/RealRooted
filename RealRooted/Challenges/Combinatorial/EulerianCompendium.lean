module

public import RealRooted.Applications.EulerianCompendium.CyclicWords
public import RealRooted.Applications.EulerianCompendium.Definitions
public import RealRooted.Applications.EulerianCompendium.Results
public import RealRooted.Applications.EulerianCompendium.TernaryWords
public import RealRooted.Applications.EulerianVariations.CyclicPathDescents
public import RealRooted.Applications.EulerianVariations.TernaryRuns
public import RealRooted.CombinatorialExamples.PeakValues.WeightedInterleaving
public import RealRooted.CombinatorialExamples.SuperEulerian
public import RealRooted.CombinatorialExamples.ZigzagEulerian.Definitions
public import RealRooted.CombinatorialExamples.ZigzagEulerian.RealRooted
public import RealRooted.EulerianCompletion
public import RealRooted.EulerianMixedCompatibility
public import RealRooted.EulerianMixedCompatibility.Insertion

/-!
# Eulerian-type polynomials

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "eulerian-compendium"
formalized = "2026-10-24"
tags = ["coauthored-paper", "realrooted-original"]
references = ["Alexandersson2026Eulerian"]
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
name = "RealRooted.EulerianCompendium.ternaryWordRunEnumerator"
module = "RealRooted.Applications.EulerianCompendium.TernaryWords"
label = "Increasing-run polynomial of ternary words"

[[definitions]]
name = "RealRooted.EulerianCompendium.peakPolynomial"
module = "RealRooted.Applications.EulerianCompendium.Definitions"
label = "Peak polynomial of permutations"

[[definitions]]
name = "RealRooted.EulerianCompendium.StrictlyAlternatingRoots"
module = "RealRooted.Applications.EulerianCompendium.Definitions"
label = "Strict alternation of roots"

[[definitions]]
name = "RealRooted.eulerInsertionStep"
module = "RealRooted.EulerianMixedCompatibility.Insertion"
label = "Euler insertion operator E_{c,d}"

[[definitions]]
name = "RealRooted.loweringEulerStep"
module = "RealRooted.EulerianCompletion"
label = "Lowering Euler operator p ↦ Mp + (1 - x)p'"

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
name = "RealRooted.EulerianCompendium.Challenges.derangementDescent_realRooted"
module = "RealRooted.Applications.EulerianCompendium.Results"
label = "Derangement polynomials are real-rooted"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.Challenges.cyclicWordDescent_roots"
module = "RealRooted.Applications.EulerianCompendium.Results"
label = "Balanced cyclic-word polynomials: simple roots, one at 0, the rest negative"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.Challenges.evenTopDescent_strictAlternation"
module = "RealRooted.Applications.EulerianCompendium.Results"
label = "Even-top descent polynomials have negative roots that strictly alternate"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.superEulerian_roots_interlacing_gamma"
module = "RealRooted.Applications.EulerianCompendium.Results"
label = "Super-Eulerian polynomials: real roots, interlacing and gamma-expansion"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.Challenges.ternaryWordRun_realRooted_interlaces"
module = "RealRooted.Applications.EulerianCompendium.Results"
label = "Ternary-word run polynomials are real-rooted and interlace"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.Challenges.peakPolynomial_roots"
module = "RealRooted.Applications.EulerianCompendium.Results"
label = "Peak polynomials have negative roots that strictly alternate"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.peakValue_stability_and_weightedInterlacing"
module = "RealRooted.Applications.EulerianCompendium.Results"
label = "Peak-value polynomials are real stable; weighted diagonals interlace"
tags = ["coauthored-paper"]
headline = true

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.cyclicPathDescentPolynomial_roots"
module = "RealRooted.Applications.EulerianVariations.CyclicPathDescents"
label = "Simple roots of the cyclic path descent polynomial: 0 and n - 1 negative"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.cyclicPathDescentPolynomial_eq_derivative"
module = "RealRooted.Applications.EulerianVariations.CyclicPathDescents"
label = "The cyclic path descent polynomial is (2/n) x B_n'(x) for the type B Narayana B_n"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.peakValuePolynomial_mvRealStable"
module = "RealRooted.CombinatorialExamples.PeakValues.Stability"
label = "The peak-value polynomial K_n is real stable"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.peakValueWeightedDiagonal_consecutive_strictInterl"
module = "RealRooted.CombinatorialExamples.PeakValues.WeightedInterleaving"
label = "Positive weighted diagonals of K_n and K_{n+1} interlace"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.ternaryRunPolynomial_isPF"
module = "RealRooted.Applications.EulerianVariations.TernaryRuns"
label = "Ternary run polynomials are Pólya frequency polynomials"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.Applications.EulerianVariations.ternaryRunPolynomial_strictInterl"
module = "RealRooted.Applications.EulerianVariations.TernaryRuns"
label = "Consecutive ternary run polynomials interlace"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.SuperEulerian.isRealRooted_superEulerian"
module = "RealRooted.CombinatorialExamples.SuperEulerian"
label = "For ℓ ≥ 1, super-Eulerian polynomials are nonzero and real-rooted"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.SuperEulerian.strictInterl_superEulerian_succ"
module = "RealRooted.CombinatorialExamples.SuperEulerian"
label = "For ℓ ≥ 1, consecutive super-Eulerian polynomials interlace, without common roots"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.SuperEulerian.exists_gamma_superEulerian"
module = "RealRooted.CombinatorialExamples.SuperEulerian"
label = "Super-Eulerian gamma-polynomials are real-rooted with nonnegative coefficients"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.ZigzagEulerian.isRealRooted_and_roots_neg"
module = "RealRooted.CombinatorialExamples.ZigzagEulerian.RealRooted"
label = "Zig-zag Eulerian polynomials have simple negative roots"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.compatible_eulerInsertionStep_one_zero_succ"
module = "RealRooted.EulerianMixedCompatibility"
label = "Compatibility of two adjacent Euler insertion steps"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.mixedEulerStep_splits"
module = "RealRooted.EulerianMixedCompatibility"
label = "Positive mixtures of adjacent Euler insertion steps are real-rooted"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.loweringEulerStep_strictInterl"
module = "RealRooted.EulerianCompletion"
label = "The lowering Euler operator preserves interlacing of equal-degree PF polynomials"
tags = ["realrooted-original"]

[[theorems]]
name = "RealRooted.crossedEulerCompletion_commonLeftInterleaver"
module = "RealRooted.EulerianCompletion"
label = "Four Euler insertion images have a common left interleaver"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Eulerian-type polynomials

Descent and peak polynomials of derangements, words and permutations are real-rooted, and
consecutive members of most families interlace.

## Results

Results 1 to 7 are the theorems of [@Alexandersson2026Eulerian], in the order of the paper.
Result 8 concerns the [zig-zag Eulerian polynomials](rr:zigzag-eulerian).

1. **Derangements.** For $n\ge2$, the polynomial
   $\sum_{\pi\in\mathfrak D_n}x^{\operatorname{des}\pi}$ over derangements is nonzero and
   real-rooted with all roots nonpositive.
2. **Balanced cyclic words.** For $n\ge1$, let $w$ range over binary words of length $2n$ with
   exactly $n$ ones, and let $\operatorname{cdes}w$ count the cyclic positions $i$ with
   $w_i=1$ and $w_{i+1}=0$. Then $\sum_w x^{\operatorname{cdes}w}$ is real-rooted with simple
   roots: one root is $0$ and the other $n-1$ are negative. This polynomial is
   $$C_n(x)=\sum_{k=1}^n2\binom nk\binom{n-1}{k-1}x^k=\frac2n\,x\,B_n'(x),$$
   where $B_n(x)=\sum_k\binom nk^2x^k$ is the type $B$ Narayana polynomial.
3. **Even-top descents.** Let $\operatorname{edes}\pi$ count the descents $\pi_j>\pi_{j+1}$ with
   $\pi_j$ even. For $n\ge2$, the polynomial $\sum_{\pi\in\mathfrak S_n}x^{\operatorname{edes}\pi}$
   is real-rooted with negative roots. It strictly alternates with the same polynomial for
   $n+1$: both have simple roots, no root is shared, and one interlaces the other.
4. **Super-Eulerian polynomials.** Let $E^{(\ell)}_{1,0}=1$ and
   $E^{(\ell)}_{n,k}=(k+1)^\ell E^{(\ell)}_{n-1,k}+(n-k)^\ell E^{(\ell)}_{n-1,k-1}$, with entries
   outside $0\le k\le n-1$ equal to zero, and let $A^{(\ell)}_n=\sum_{k<n}E^{(\ell)}_{n,k}x^k$.
   For $\ell\ge1$ and $n\ge0$, the polynomial $A^{(\ell)}_{n+1}$ is real-rooted with nonpositive
   roots, and $A^{(\ell)}_{n+1}\ll A^{(\ell)}_{n+2}$ with no common root. Moreover
   $$A^{(\ell)}_{n+1}(x)=\sum_{0\le i\le n/2}\gamma_i\,x^i(1+x)^{n-2i},$$
   where $\gamma$ is nonzero, real-rooted, with nonpositive roots and nonnegative coefficients.
5. **Ternary words.** For $w\in\{0,1,2\}^n$, let $\operatorname{run}w$ be the number of maximal
   strictly increasing runs. Then $T_n(x)=\sum_w x^{\operatorname{run}w}$ is a Pólya frequency
   polynomial and $T_n\ll T_{n+1}$. These polynomials satisfy $T_0=1$ and
   $$(n+1)\,T_{n+1}=3x(1-x)\,T_n'+\bigl((4n+3)x-n\bigr)\,T_n.$$
6. **Peaks.** For $n\ge1$, the polynomial $\sum_{\pi\in\mathfrak S_n}x^{\operatorname{pk}\pi}$,
   where $\operatorname{pk}$ counts interior peaks, is real-rooted. For $n\ge3$ it has degree
   $\lfloor(n-1)/2\rfloor$ and negative roots, and it strictly alternates with the same
   polynomial for $n+1$.
7. **Peak values.** Let $K_n(z_1,\dots,z_n)=\sum_{\pi\in\mathfrak S_n}\prod z_v$, with $v$
   ranging over the values of the interior peaks of $\pi$. Then $K_n$ is real stable for every $n$.
   For $n\ge1$ and positive weights $w_1,\dots,w_{n+1}$, the polynomial $K_n(w_1x,\dots,w_nx)$
   interlaces $K_{n+1}(w_1x,\dots,w_{n+1}x)$.

8. **Zig-zag swaps.** Call $i$ a swap of a permutation $\pi$ of $[n]$ if
   $\pi^{-1}(i)+1<\pi^{-1}(i+1)$, and let $\operatorname{swap}\pi$ be the number of swaps. For
   $n\ge1$, the polynomial $\sum x^{\operatorname{swap}\pi}$ over up-down permutations
   $\pi_1<\pi_2>\pi_3<\dotsb$ is nonzero with simple negative roots, and has degree $n-2$ for
   $n\ge2$.

**Euler insertion operators.** Let
$$
E_{c,d}\,p=\bigl(c+(d+1)x\bigr)\,p+(x-x^2)\,p' .
$$

**Theorem (mixed compatibility).** Let $f,g$ have nonnegative coefficients and positive leading
coefficients, with $g\ll f$, $\deg f=\deg g+1$ and $\deg f\le n+1$. Then $E_{1,n}\,g$ and
$E_{0,n+1}\,f$ are compatible: every nonnegative combination of them is zero or real-rooted.
In particular $E_{0,n+1}f+\lambda\,E_{1,n}g$ is real-rooted for every $\lambda>0$.

**Theorem (oriented completion).** Let $L_Mp=Mp+(1-x)p'$. If $p\ll q$ are Pólya frequency
polynomials of the same degree $D\ge1$ and $M\ge D+1$, then $L_Mp\ll L_Mq$. Moreover, if $p$
and $p+1$ are Pólya frequency polynomials of degree $D\ge2$ and $M\ge D+2$, the four polynomials
$$
E_{1,M-2}\,p,\quad E_{1,M-2}(p+1),\quad E_{0,M-1}\,p,\quad E_{0,M-1}(p+1)
$$
have a common left interleaver.

## Proof

The two operator theorems give the proof for derangement descents.

## References

- [@Alexandersson2026Eulerian]
- U. Shankar, [*Multivariate stability of powered triangular recurrences and parametrised
  Eulerian polynomials*](https://arxiv.org/abs/2609.15651), Theorem C, for the absence of
  common roots in result 4.
<!-- /realrooted-catalog-content -->
-/
