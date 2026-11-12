module

import RealRooted.Applications.EulerianCompendium.Results
import RealRooted.EulerianMixedCompatibility
import RealRooted.EulerianCompletion
public import RealRooted.Applications.EulerianCompendium.TernaryWords
public import RealRooted.Applications.EulerianCompendium.CyclicWords
import RealRooted.CombinatorialExamples.ZigzagEulerian.RealRooted
public import RealRooted.CombinatorialExamples.ZigzagEulerian.Definitions

/-!
# Eulerian-type polynomials with real roots

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "eulerian-compendium"
formalized = "2026-10-24"
tags = ["coauthored-paper", "realrooted-original"]
references = ["Alexandersson2026Eulerian"]
authors = ["Alexandersson"]
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

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.derangementDescent_realRooted"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
label = "Derangement polynomials are real-rooted"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.cyclicWordDescent_roots"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
label = "Balanced cyclic-word polynomials: simple roots, one at 0, the rest negative"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.evenTopDescent_strictAlternation"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
label = "Even-top descent polynomials have negative roots that strictly alternate"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.superEulerian_roots_interlacing_gamma"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
label = "Super-Eulerian polynomials: real roots, interlacing and gamma-expansion"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.ternaryWordRun_realRooted_interlaces"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
label = "Ternary-word run polynomials are real-rooted and interlace"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.peakPolynomial_roots"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
label = "Peak polynomials have negative roots that strictly alternate"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.peakValue_stability_and_weightedInterlacing"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
label = "Peak-value polynomials are real stable; weighted diagonals interlace"
tags = ["coauthored-paper"]
headline = true

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.zigzagEulerian_roots"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
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
# Eulerian-type polynomials with real roots

Descent and peak polynomials of derangements, words and permutations are real-rooted, and
consecutive members of most families interlace.

## Results

We write $f\ll g$ if $f$ interlaces $g$; repeated and common roots are allowed unless stated.
Results 1 to 7 are the theorems of [@Alexandersson2026Eulerian], in the order of the paper;
result 8 is not in the paper.

1. **Derangements.** For $n\ge2$, the polynomial
   $\sum_{\pi\in\mathfrak D_n}x^{\operatorname{des}\pi}$ over derangements is nonzero and
   real-rooted with all roots nonpositive.
2. **Balanced cyclic words.** For $n\ge1$, let $w$ range over binary words of length $2n$ with
   exactly $n$ ones, and let $\operatorname{cdes}w$ count the cyclic positions $i$ with
   $w_i=1$ and $w_{i+1}=0$. Then $\sum_w x^{\operatorname{cdes}w}$ is real-rooted with simple
   roots: one root is $0$ and the other $n-1$ are negative.
3. **Even-top descents.** Let $\operatorname{edes}\pi$ count the descents $\pi_j>\pi_{j+1}$ with
   $\pi_j$ even. For $n\ge2$, the polynomial $\sum_{\pi\in\mathfrak S_n}x^{\operatorname{edes}\pi}$
   is real-rooted with negative roots. It strictly alternates with the same polynomial for
   $n+1$: both have simple roots, no root is shared, and one interlaces the other.
4. **Super-Eulerian polynomials.** Let $E^{(\ell)}_{1,0}=1$ and
   $E^{(\ell)}_{n,k}=(k+1)^\ell E^{(\ell)}_{n-1,k}+(n-k)^\ell E^{(\ell)}_{n-1,k-1}$, with entries
   outside $0\le k\le n-1$ equal to zero, and let $A^{(\ell)}_n=\sum_{k<n}E^{(\ell)}_{n,k}x^k$.
   For $\ell\ge1$ and $n\ge0$, the polynomial $A^{(\ell)}_{n+1}$ is real-rooted with nonpositive
   roots, and $A^{(\ell)}_{n+1}\ll A^{(\ell)}_{n+2}$. Moreover
   $$A^{(\ell)}_{n+1}(x)=\sum_{0\le i\le n/2}\gamma_i\,x^i(1+x)^{n-2i},$$
   where $\gamma$ is nonzero, real-rooted, with nonpositive roots and nonnegative coefficients.
5. **Ternary words.** For $w\in\{0,1,2\}^n$, let $\operatorname{run}w$ be the number of maximal
   strictly increasing runs. Then $\sum_w x^{\operatorname{run}w}$ is nonzero and real-rooted, and
   interlaces the same polynomial for $n+1$.
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

## Use

The two operator theorems drive the proof for derangement descents.

## References

- [@Alexandersson2026Eulerian]
<!-- /realrooted-catalog-content -->
-/

public section

open Polynomial RealRooted

open RealRooted.ZigzagEulerian

namespace RealRooted.EulerianCompendium.PaperChallenges

/-- Paper `thm:derangementRealRooted`. Verified for actual derangement descents. -/
theorem derangementDescent_realRooted (n : ℕ) (hn : 2 ≤ n) :
    derangementDescentPolynomial n ≠ 0 ∧
      (derangementDescentPolynomial n).Splits ∧
      ∀ r ∈ (derangementDescentPolynomial n).roots, r ≤ 0 := by
  exact Challenges.derangementDescent_realRooted n hn

/-- Paper `thm:cyclicDescents`. Verified for the actual balanced cyclic-word sum. -/
theorem cyclicWordDescent_roots (n : ℕ) (hn : 0 < n) :
    (BalancedCyclic.balancedWordSum n).Splits ∧
      HasSimpleRoots (BalancedCyclic.balancedWordSum n) ∧
      (BalancedCyclic.balancedWordSum n).IsRoot 0 ∧
      (∀ r ∈ (BalancedCyclic.balancedWordSum n).roots.erase 0, r < 0) ∧
      ((BalancedCyclic.balancedWordSum n).roots.erase 0).card = n - 1 := by
  exact Challenges.cyclicWordDescent_roots n hn

/-- Paper `thm:evenTopInterlacing`. Verified: actual sums and strict root alternation. -/
theorem evenTopDescent_strictAlternation (n : ℕ) (hn : 2 ≤ n) :
    (evenTopDescentPolynomial n).Splits ∧
      (∀ r ∈ (evenTopDescentPolynomial n).roots, r < 0) ∧
      StrictlyAlternatingRoots
        (evenTopDescentPolynomial n) (evenTopDescentPolynomial (n + 1)) := by
  exact Challenges.evenTopDescent_strictAlternation n hn

/-- Paper `thm:superEulerian`. All conclusions verified; the row is n+1. -/
theorem superEulerian_roots_interlacing_gamma (l n : ℕ) (hl : 0 < l) :
    (superEulerianPolynomial l (n + 1) ≠ 0 ∧
      (superEulerianPolynomial l (n + 1)).Splits ∧
      ∀ r ∈ (superEulerianPolynomial l (n + 1)).roots, r ≤ 0) ∧
    Interl (superEulerianPolynomial l (n + 1)) (superEulerianPolynomial l (n + 2)) ∧
    ∃ γ : ℝ[X], γ.natDegree ≤ n / 2 ∧
      IsGammaExpansion n (superEulerianPolynomial l (n + 1)) γ ∧
      (γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ ∧ HasNonnegCoeffs γ := by
  exact ⟨Challenges.superEulerian_realRooted l n hl,
    Challenges.superEulerian_interlaces l n hl, Challenges.superEulerian_gamma l n hl⟩

/-- Paper `thm:ternaryRuns`: real-rootedness and interlacing for actual ternary words. -/
theorem ternaryWordRun_realRooted_interlaces (n : ℕ) :
    (ternaryWordRunEnumerator n ≠ 0 ∧ (ternaryWordRunEnumerator n).Splits) ∧
      StrictInterl (ternaryWordRunEnumerator n) (ternaryWordRunEnumerator (n + 1)) := by
  exact Challenges.ternaryWordRun_realRooted_interlaces n

/-- Paper `thm:permutationPeaks`. Verified: degree, simplicity and strict alternation. -/
theorem peakPolynomial_roots (n : ℕ) (hn : 1 ≤ n) :
    (peakPolynomial n ≠ 0 ∧ (peakPolynomial n).Splits) ∧
    (3 ≤ n → (peakPolynomial n).natDegree = (n - 1) / 2 ∧
      (∀ r ∈ (peakPolynomial n).roots, r < 0) ∧
      StrictlyAlternatingRoots (peakPolynomial n) (peakPolynomial (n + 1))) := by
  exact Challenges.peakPolynomial_roots n hn

/-- Paper `thm:peakValueStability`. Both conclusions verified for actual permutations. -/
theorem peakValue_stability_and_weightedInterlacing :
    (∀ n : ℕ, MvRealStable (peakValuePolynomial n)) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (wt : Fin (n + 1) → ℝ), (∀ j, 0 < wt j) →
      StrictInterl (weightedPeakPolynomial (fun j : Fin n => wt j.castSucc))
        (weightedPeakPolynomial wt)) := by
  exact ⟨Challenges.peakValue_realStable, Challenges.weightedPeak_interlaces⟩

/-- Exact degree and distinct negative roots of the zig-zag swap enumerator. -/
theorem zigzagEulerian_roots (n : ℕ) (hn : 1 ≤ n) :
    zigzagEulerianPolynomial n ≠ 0 ∧
      (zigzagEulerianPolynomial n).natDegree = n - 2 ∧
      (zigzagEulerianPolynomial n).Splits ∧
      (zigzagEulerianPolynomial n).roots.Nodup ∧
      ∀ r ∈ (zigzagEulerianPolynomial n).roots, r < 0 := by
  exact ⟨zigzagEulerianPolynomial_ne_zero n, zigzagEulerianPolynomial_roots n hn⟩

end RealRooted.EulerianCompendium.PaperChallenges
