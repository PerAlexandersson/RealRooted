import RealRooted.RankTwoMatching

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.Graph

/-- The binomial coefficient transform realized by a rank-two weighted
complete-graph matching model. -/
def rankTwoBinomialTransform (p : ℝ[X]) (M : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (M + 1),
    monomial k
      ((k.factorial : ℝ) *
        ∑ j ∈ Finset.range (p.natDegree + 1),
          p.coeff j * (Nat.choose j k : ℝ) * (Nat.choose (M - j) k : ℝ))

theorem coeff_rankTwoBinomialTransform (p : ℝ[X]) (M k : ℕ) :
    (rankTwoBinomialTransform p M).coeff k =
      if k ≤ M then
        (k.factorial : ℝ) *
          ∑ j ∈ Finset.range (p.natDegree + 1),
            p.coeff j * (Nat.choose j k : ℝ) * (Nat.choose (M - j) k : ℝ)
      else 0 := by
  classical
  simp [rankTwoBinomialTransform, Polynomial.coeff_monomial]

theorem natDegree_rankTwoBinomialTransform_le (p : ℝ[X]) (M : ℕ) :
    (rankTwoBinomialTransform p M).natDegree ≤ p.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_rankTwoBinomialTransform]
  by_cases hkM : k ≤ M
  · rw [if_pos hkM]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro j hj
    have hjle : j ≤ p.natDegree := by
      simpa using Finset.mem_range.mp hj
    rw [Nat.choose_eq_zero_of_lt (by lia)]
    simp
  · rw [if_neg hkM]

/-- The rank-two binomial transform preserves PF polynomials with constant
coefficient one when the ambient size bounds the degree. -/
theorem rankTwoBinomialTransform_isPF
    {p : ℝ[X]} (hp : IsPFPolynomial p) (hconst : p.coeff 0 = 1)
    {M : ℕ} (hdegree : p.natDegree ≤ M) :
    IsPFPolynomial (rankTwoBinomialTransform p M) := by
  classical
  obtain ⟨a, b, ha, hb, hmoment⟩ :=
    exists_nonneg_completeGraphRankTwoWeight_eq_coeff_sum hp hconst hdegree
  let G := _root_.SimpleGraph.completeGraph (Fin M)
  let wt := completeGraphRankTwoWeight a b
  have hwt : ∀ e, 0 ≤ wt e :=
    completeGraphRankTwoWeight_nonneg a b ha hb
  have hmatching :
      IsPFPolynomial (weightedMatchingPolynomialByEdges G wt) :=
    weightedMatchingPolynomialByEdges_isPFPolynomial G wt hwt
  have hp0 : p ≠ 0 := by
    intro hpzero
    rw [hpzero] at hconst
    simp at hconst
  have heval : 0 < p.eval 1 :=
    eval_pos_of_hasNonnegCoeffs hp.hasNonnegCoeffs hp0 one_pos
  have hscaled := hmatching.const_mul heval
  suffices rankTwoBinomialTransform p M =
      C (p.eval 1) * weightedMatchingPolynomialByEdges G wt by
    simpa only [this] using hscaled
  ext k
  rw [coeff_rankTwoBinomialTransform, coeff_C_mul,
    coeff_weightedMatchingPolynomialByEdges]
  by_cases hk : k ≤ M
  · rw [if_pos hk]
    exact (hmoment k).symm
  · rw [if_neg hk]
    have hsum :
        ∑ j ∈ Finset.range (p.natDegree + 1),
            p.coeff j * (Nat.choose j k : ℝ) * (Nat.choose (M - j) k : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjle : j ≤ p.natDegree := by
        simpa using Finset.mem_range.mp hj
      have hlt : M - j < k := by
        lia
      rw [Nat.choose_eq_zero_of_lt hlt]
      simp
    have hm := hmoment k
    rw [hsum, mul_zero] at hm
    exact hm.symm

end RealRooted.Graph
