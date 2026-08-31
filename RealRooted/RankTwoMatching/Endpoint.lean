import RealRooted.RankTwoMatching.Enumeration

open Polynomial

noncomputable section

namespace RealRooted.Graph

open scoped BigOperators
open RankTwoInternal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Orienting every edge of a complete-graph matching identifies it with two
disjoint vertex sets and a bijection between them. -/
theorem weightedMatchingNumber_completeGraph_rankTwo
    (a b : V → ℝ) (k : ℕ) :
    weightedMatchingNumber (_root_.SimpleGraph.completeGraph V)
        (completeGraphRankTwoWeight a b) k =
      (k.factorial : ℝ) *
        RankTwoMatchingModel.disjointSubsetWeight a b k := by
  rw [weightedMatchingNumber_eq_orientedMatchingWeightSum,
    orientedMatchingWeightSum_eq_disjointEquivWeightSum,
    disjointEquivWeightSum_eq_factorial_mul,
    disjointSelectionWeight_eq_disjointSubsetWeight]

/-- A constant-one PF polynomial of degree at most `M` supplies a nonnegative
rank-two weighting of the complete graph whose size-`k` matching numbers give
its binomial coefficient transform, up to the expected factorial. -/
theorem exists_nonneg_completeGraphRankTwoWeight_eq_coeff_sum
    {p : ℝ[X]} (hp : IsPFPolynomial p) (hconst : p.coeff 0 = 1)
    {M : ℕ} (hdegree : p.natDegree ≤ M) :
    ∃ a b : Fin M → ℝ,
      (∀ i, 0 ≤ a i) ∧
        (∀ i, 0 ≤ b i) ∧
          ∀ k,
            p.eval 1 * weightedMatchingNumber
                (_root_.SimpleGraph.completeGraph (Fin M))
                (completeGraphRankTwoWeight a b) k =
              (k.factorial : ℝ) *
                ∑ j ∈ Finset.range (p.natDegree + 1),
                  p.coeff j * (Nat.choose j k : ℝ) *
                    (Nat.choose (M - j) k : ℝ) := by
  obtain ⟨a, b, ha, hb, hmoment⟩ :=
    RankTwoMatchingModel.exists_nonneg_disjointSubsetWeight_eq_coeff_sum
      hp hconst hdegree
  refine ⟨a, b, ha, hb, ?_⟩
  intro k
  rw [weightedMatchingNumber_completeGraph_rankTwo]
  calc
    p.eval 1 *
        ((k.factorial : ℝ) *
          RankTwoMatchingModel.disjointSubsetWeight a b k) =
        (k.factorial : ℝ) *
          (p.eval 1 * RankTwoMatchingModel.disjointSubsetWeight a b k) := by
      ring
    _ = _ := by rw [hmoment k]

end RealRooted.Graph
