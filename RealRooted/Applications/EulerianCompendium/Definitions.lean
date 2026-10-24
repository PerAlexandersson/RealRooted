import RealRooted.Applications.EulerianVariations.CyclicPathDescents
import RealRooted.Applications.EulerianVariations.TernaryRuns
import RealRooted.CombinatorialExamples.SuperEulerian
import RealRooted.CombinatorialExamples.PeakValues.WeightedInterleaving

/-!
# Fixed definitions for the Eulerian compendium

The imported polynomial owners remain in RealRooted. Cyclic paths use the
coefficient formula and ternary runs use the differential recurrence: their
combinatorial identifications are proved locally in `CyclicWords` and `TernaryWords`.
The derangement and even-top enumerators below are actual permutation sums;
their root theorems are proved in `DerangementReciprocal` and `EvenTopRoots`.
-/

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.EulerianCompendium

/-- Paper `thm:derangementRealRooted`: descents of fixed-point-free permutations. -/
def derangementDescentPolynomial (n : ℕ) : ℝ[X] :=
  ∑ π : Equiv.Perm (Fin n), if ∀ i, π i ≠ i then X ^ π.descentCount else 0

/-- Paper `thm:cyclicDescents`: the explicit coefficient model, indexed by n. -/
abbrev cyclicPathDescentPolynomial :=
  RealRooted.Applications.EulerianVariations.cyclicPathDescentPolynomial

/-- Count descents with even top, translating zero-based values to 1,...,n. -/
def evenTopDescentCount {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun j : Fin n =>
    ((π j).val + 1) % 2 = 0 ∧
      ∃ k : Fin n, j.val + 1 = k.val ∧ π k < π j).card

/-- Paper `thm:evenTopInterlacing`: the actual even-top descent enumerator. -/
def evenTopDescentPolynomial (n : ℕ) : ℝ[X] :=
  ∑ π : Equiv.Perm (Fin n), X ^ evenTopDescentCount π

/-- Paper `thm:superEulerian`: the powered Eulerian recurrence, with E_1=1. -/
abbrev superEulerianPolynomial := RealRooted.SuperEulerian.superEulerian

/-- Paper `thm:ternaryRuns`: the normalized differential-recurrence model. -/
abbrev ternaryRunPolynomial :=
  RealRooted.Applications.EulerianVariations.ternaryRunPolynomial

/-- Paper `thm:peakValueStability`: the actual multivariate permutation sum. -/
abbrev peakValuePolynomial := RealRooted.peakValuePolynomial

/-- Positive weighted diagonal of the peak-value permutation enumerator. -/
abbrev weightedPeakPolynomial := @RealRooted.peakValueWeightedDiagonal

/-- Paper `thm:permutationPeaks`: the all-one diagonal counts interior peaks. -/
def peakPolynomial (n : ℕ) : ℝ[X] := weightedPeakPolynomial (fun _ : Fin n => 1)

/-- Strict root alternation, with either orientation and with no shared roots.
RealRooted's `StrictInterl` alone permits repeated and shared roots. -/
def StrictlyAlternatingRoots (p q : ℝ[X]) : Prop :=
  (RealRooted.StrictInterl p q ∨ RealRooted.StrictInterl q p) ∧
    RealRooted.HasSimpleRoots p ∧ RealRooted.HasSimpleRoots q ∧
    ∀ r ∈ p.roots, r ∉ q.roots

end RealRooted.EulerianCompendium
