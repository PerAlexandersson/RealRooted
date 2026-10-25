import RealRooted.CombinatorialExamples.ZigzagEulerian.RealRooted
import RealRooted.CombinatorialExamples.ZigzagEulerian.Identification
import RealRooted.Applications.EulerianCompendium.Peaks
import RealRooted.Applications.EulerianCompendium.CyclicWords
import RealRooted.Applications.EulerianCompendium.EvenTopRoots
import RealRooted.Applications.EulerianCompendium.DerangementReciprocal
import RealRooted.Applications.EulerianCompendium.DeletionRoots
import RealRooted.Applications.EulerianCompendium.TernaryWords

/-!
# Eulerian enumeration root theorems

Public extraction of the checked compendium endpoints. Definitions and proofs
come from the author's AlexanderssonFormalizations development; generic theory
is imported from its existing RealRooted owners.
-/

open Polynomial RealRooted

open RealRooted.ZigzagEulerian

namespace RealRooted.EulerianCompendium.Challenges

/-- Paper `thm:derangementRealRooted`: the actual derangement descent sum. -/
theorem derangementDescent_realRooted (n : ℕ) (hn : 2 ≤ n) :
    derangementDescentPolynomial n ≠ 0 ∧
      (derangementDescentPolynomial n).Splits ∧
      ∀ r ∈ (derangementDescentPolynomial n).roots, r ≤ 0 := by
  exact ⟨derangementDescentPolynomial_ne_zero n hn,
    derangementDescentPolynomial_splits n hn,
    derangementDescentPolynomial_roots_nonpos n⟩

/-- Paper `thm:largerFamily`: compatibility of the two recurrence summands. -/
theorem deletionPolynomial_summands_compatible (a k : ℕ) :
    Compatible (eulerInsertionStep 1 (a + k) (deletionPolynomial a k))
      (eulerInsertionStep 0 (a + k + 1) (deletionPolynomial a (k + 1))) := by
  exact deletionComponents_compatible a k

/-- Paper `thm:largerFamily`: the deletion-stable family has nonpositive real roots. -/
theorem deletionPolynomial_realRooted (a r : ℕ) :
    deletionPolynomial a r ≠ 0 ∧ (deletionPolynomial a r).Splits ∧
      ∀ x ∈ (deletionPolynomial a r).roots, x ≤ 0 := by
  have hp := deletionPolynomial_isPF a r
  have hn := (deletionPolynomial_degree_nonneg a r).2.1.ne_zero
  exact ⟨hn, (hp.ne_zero_and_splits hn).2, hp.roots_nonpos⟩

/-- Paper `thm:cyclicDescents`. Cyclic paths: simple zero at zero and n-1 negative zeros
(coefficient model). -/
theorem cyclicPathDescent_roots (n : ℕ) (hn : 0 < n) :
    (cyclicPathDescentPolynomial n).Splits ∧
      HasSimpleRoots (cyclicPathDescentPolynomial n) ∧
      (cyclicPathDescentPolynomial n).IsRoot 0 ∧
      (∀ r ∈ (cyclicPathDescentPolynomial n).roots.erase 0, r < 0) ∧
      ((cyclicPathDescentPolynomial n).roots.erase 0).card = n - 1 := by
  have h := Applications.EulerianVariations.cyclicPathDescentPolynomial_roots n hn
  have hpf := Applications.EulerianVariations.cyclicPathDescentPolynomial_isPF n hn
  exact ⟨(hpf.ne_zero_and_splits h.1.ne_zero).2, h⟩

/-- Paper `thm:cyclicDescents`: the actual balanced cyclic binary-word sum. -/
theorem cyclicWordDescent_roots (n : ℕ) (hn : 0 < n) :
    (BalancedCyclic.balancedWordSum n).Splits ∧
      HasSimpleRoots (BalancedCyclic.balancedWordSum n) ∧
      (BalancedCyclic.balancedWordSum n).IsRoot 0 ∧
      (∀ r ∈ (BalancedCyclic.balancedWordSum n).roots.erase 0, r < 0) ∧
      ((BalancedCyclic.balancedWordSum n).roots.erase 0).card = n - 1 := by
  rw [balancedWordSum_eq_cyclicPathDescentPolynomial n hn]
  exact cyclicPathDescent_roots n hn

/-- Paper `thm:evenTopInterlacing`: strict alternation for actual even-top descents. -/
theorem evenTopDescent_strictAlternation (n : ℕ) (hn : 2 ≤ n) :
    (evenTopDescentPolynomial n).Splits ∧
      (∀ r ∈ (evenTopDescentPolynomial n).roots, r < 0) ∧
      StrictlyAlternatingRoots
        (evenTopDescentPolynomial n) (evenTopDescentPolynomial (n + 1)) := by
  exact ⟨evenTopDescentPolynomial_splits hn,
    (evenTopDescentPolynomial_hasSimpleNegativeRoots hn).2,
    evenTopDescentPolynomial_strictlyAlternates hn⟩

/-- Paper `thm:superEulerian`. Super-Eulerian polynomials: real-rooted with nonpositive zeros.
-/
theorem superEulerian_realRooted (l n : ℕ) (hl : 0 < l) :
    superEulerianPolynomial l (n + 1) ≠ 0 ∧
      (superEulerianPolynomial l (n + 1)).Splits ∧
      ∀ r ∈ (superEulerianPolynomial l (n + 1)).roots, r ≤ 0 := by
  exact ⟨(SuperEulerian.isRealRooted_superEulerian (Nat.ne_of_gt hl) n).1,
    (SuperEulerian.isRealRooted_superEulerian (Nat.ne_of_gt hl) n).2,
    SuperEulerian.roots_nonpos_superEulerian (Nat.ne_of_gt hl) (n + 1)⟩

/-- Paper `thm:superEulerian`. Super-Eulerian polynomials: consecutive interlacing. -/
theorem superEulerian_interlaces (l n : ℕ) (hl : 0 < l) :
    Interl (superEulerianPolynomial l (n + 1)) (superEulerianPolynomial l (n + 2)) := by
  exact SuperEulerian.interl_superEulerian_succ (Nat.ne_of_gt hl) (n + 1)

/-- Paper `thm:superEulerian`. Super-Eulerian gamma-polynomial: existence, real-rootedness and
coefficient nonnegativity. -/
theorem superEulerian_gamma (l n : ℕ) (hl : 0 < l) :
    ∃ γ : ℝ[X], γ.natDegree ≤ n / 2 ∧
      IsGammaExpansion n (superEulerianPolynomial l (n + 1)) γ ∧
      (γ ≠ 0 ∧ γ.Splits) ∧ HasRootsNonpos γ ∧ HasNonnegCoeffs γ := by
  exact SuperEulerian.exists_gamma_superEulerian (Nat.ne_of_gt hl) n

/-- Paper `thm:ternaryRuns`. Ternary runs: real-rootedness and weak interlacing (recurrence
model). -/
theorem ternaryRun_realRooted_interlaces (n : ℕ) :
    (ternaryRunPolynomial n ≠ 0 ∧ (ternaryRunPolynomial n).Splits) ∧
      StrictInterl (ternaryRunPolynomial n) (ternaryRunPolynomial (n + 1)) := by
  have h := Applications.EulerianVariations.ternaryRunPolynomial_strictInterl n
  exact ⟨h.1, h⟩

/-- Paper `thm:ternaryRuns`: real-rootedness and interlacing for actual ternary words. -/
theorem ternaryWordRun_realRooted_interlaces (n : ℕ) :
    (ternaryWordRunEnumerator n ≠ 0 ∧ (ternaryWordRunEnumerator n).Splits) ∧
      StrictInterl (ternaryWordRunEnumerator n) (ternaryWordRunEnumerator (n + 1)) := by
  simp only [ternaryWordRunEnumerator_eq_ternaryRunPolynomial]
  exact ternaryRun_realRooted_interlaces n

/-- Paper `thm:permutationPeaks`. Permutation peaks: real-rootedness.
-/
theorem peakPolynomial_realRooted (n : ℕ) (hn : 1 ≤ n) :
    peakPolynomial n ≠ 0 ∧ (peakPolynomial n).Splits := by
  exact (peakValueWeightedDiagonal_consecutive_strictInterl n hn
    (fun _ => 1) (fun _ => zero_lt_one)).1

/-- Paper `thm:permutationPeaks`. Permutation peaks: weak consecutive interlacing. -/
theorem peakPolynomial_interlaces (n : ℕ) (hn : 1 ≤ n) :
    StrictInterl (peakPolynomial n) (peakPolynomial (n + 1)) := by
  exact peakValueWeightedDiagonal_consecutive_strictInterl n hn
    (fun _ => 1) (fun _ => zero_lt_one)

/-- Paper `thm:permutationPeaks`: exact degree and simple, strictly alternating negative roots. -/
theorem peakPolynomial_roots (n : ℕ) (hn : 1 ≤ n) :
    (peakPolynomial n ≠ 0 ∧ (peakPolynomial n).Splits) ∧
    (3 ≤ n → (peakPolynomial n).natDegree = (n - 1) / 2 ∧
      (∀ r ∈ (peakPolynomial n).roots, r < 0) ∧
      StrictlyAlternatingRoots (peakPolynomial n) (peakPolynomial (n + 1))) := by
  refine ⟨(RealRooted.EulerianCompendium.peakPolynomial_weakInterl n hn).1, fun _ => ?_⟩
  exact ⟨RealRooted.EulerianCompendium.peakPolynomial_natDegree n,
    RealRooted.EulerianCompendium.peakPolynomial_roots_neg n hn,
    RealRooted.EulerianCompendium.peakPolynomial_strictlyAlternating n hn⟩

/-- Paper `thm:peakValueStability`. Peak values: multivariate real stability. -/
theorem peakValue_realStable (n : ℕ) :
    MvRealStable (peakValuePolynomial n) := by
  exact peakValuePolynomial_mvRealStable n

/-- Paper `thm:peakValueStability`. Peak values: positive weighted consecutive interlacing. -/
theorem weightedPeak_interlaces (n : ℕ) (hn : 1 ≤ n) (wt : Fin (n + 1) → ℝ)
    (hwt : ∀ j, 0 < wt j) :
    StrictInterl (weightedPeakPolynomial (fun j : Fin n => wt j.castSucc))
      (weightedPeakPolynomial wt) := by
  exact peakValueWeightedDiagonal_consecutive_strictInterl n hn wt hwt

/-- Supporting the new `thm:zigzagEulerian`: nonzero actual permutation enumerator,
nonnegative coefficients and the degree upper bound. This is not real-rootedness. -/
theorem zigzagEulerian_coefficients (n : ℕ) (hn : 2 ≤ n) :
    zigzagEulerianPolynomial n ≠ 0 ∧
      (∀ k, 0 ≤ (zigzagEulerianPolynomial n).coeff k) ∧
      (zigzagEulerianPolynomial n).natDegree ≤ n - 2 := by
  exact ⟨zigzagEulerianPolynomial_ne_zero n, zigzagEulerianPolynomial_coeff_nonneg n,
    zigzagEulerianPolynomial_natDegree_le_sub_two hn⟩

/-- Supporting `lem:zigzagIdentification`: the finite operator identity.
Identification with the centered generating series remains separate. -/
theorem zigzagEulerian_operator_identity (n : ℕ) (hn : 2 ≤ n)
    (z : ℝ) (hz : z + 1 ≠ 0) :
    (z + 1) ^ (n - 2) *
        (zigzagEulerianPolynomial n).eval ((z - 1) / (z + 1)) =
      (2 / (n.factorial : ℝ)) *
        (RealRooted.IntervalDifferential.zigzagTransform (zigzagCenteredQuotient n)).eval z := by
  exact zigzagCenteredQuotient_eval_identity n hn z hz

/-- Paper `thm:zigzagEulerian`: exact degree and distinct negative roots of the swap sum. -/
theorem zigzagEulerian_roots (n : ℕ) (hn : 1 ≤ n) :
    zigzagEulerianPolynomial n ≠ 0 ∧
      (zigzagEulerianPolynomial n).natDegree = n - 2 ∧
      (zigzagEulerianPolynomial n).Splits ∧
      (zigzagEulerianPolynomial n).roots.Nodup ∧
      ∀ r ∈ (zigzagEulerianPolynomial n).roots, r < 0 := by
  exact ⟨zigzagEulerianPolynomial_ne_zero n, zigzagEulerianPolynomial_roots n hn⟩

end RealRooted.EulerianCompendium.Challenges
