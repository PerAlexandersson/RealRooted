module

public import RealRooted.Applications.EulerianCompendium.Results

/-!
# Eulerian compendium: paper theorems and the zig-zag theorem

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
label = "Derangement descents"

[[definitions]]
name = "RealRooted.EulerianCompendium.BalancedCyclic.balancedWordSum"
module = "RealRooted.Applications.EulerianCompendium.CyclicWords"
label = "Balanced cyclic-word descents"

[[definitions]]
name = "RealRooted.EulerianCompendium.evenTopDescentPolynomial"
module = "RealRooted.Applications.EulerianCompendium.Definitions"
label = "Even-top descents"

[[definitions]]
name = "RealRooted.EulerianCompendium.ternaryWordRunEnumerator"
module = "RealRooted.Applications.EulerianCompendium.TernaryWords"
label = "Ternary-word runs"

[[definitions]]
name = "RealRooted.EulerianCompendium.peakPolynomial"
module = "RealRooted.Applications.EulerianCompendium.Definitions"
label = "Permutation peaks"

[[definitions]]
name = "RealRooted.EulerianCompendium.StrictlyAlternatingRoots"
module = "RealRooted.Applications.EulerianCompendium.Definitions"
label = "Strict root alternation"

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.derangementDescent_realRooted"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
label = "Derangement descent real-rootedness"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.cyclicWordDescent_roots"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
label = "Balanced cyclic-word roots"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.evenTopDescent_strictAlternation"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
label = "Even-top descents strictly alternate"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.superEulerian_roots_interlacing_gamma"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
label = "Super-Eulerian roots, interlacing and gamma-polynomials"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.ternaryWordRun_realRooted_interlaces"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
label = "Ternary-word runs are real-rooted and interlace"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.peakPolynomial_roots"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
label = "Permutation peaks have simple negative roots and strict alternation"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.peakValue_stability_and_weightedInterlacing"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
label = "Peak-value stability and weighted interlacing"
tags = ["coauthored-paper"]

[[theorems]]
name = "RealRooted.EulerianCompendium.PaperChallenges.zigzagEulerian_roots"
module = "RealRooted.Challenges.Combinatorial.EulerianCompendium"
label = "Zig-zag Eulerian simple negative roots"
tags = ["realrooted-original"]
-->

<!-- realrooted-catalog-content -->
# Eight Eulerian enumeration theorems

The first seven checked statements below follow the order of the six-family
paper *Real-rooted Eulerian polynomials from permutations, words, and paths*
[@Alexandersson2026Eulerian]. The permutation-peak family contributes both its
univariate root theorem and its multivariate stability theorem. The final
zig-zag theorem is a separate result first proved in this library.

The formalized models are the intended enumerators: derangements by descents,
cyclic paths by balanced binary words, ternary runs by words, even-top descents
and zig-zag swaps by permutation sums, and peak polynomials by specialization
of the peak-value enumerator. The super-Eulerian family is recurrence-defined.

The even-top and univariate peak statements require simple roots and exclude
common roots. The ternary and positive-weighted peak statements assert weak
interlacing: the library predicate `StrictInterl` permits equal roots.
The zig-zag theorem asserts simple negative roots, without consecutive interlacing.

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
