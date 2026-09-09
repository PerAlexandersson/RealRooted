import RealRooted.CombinatorialExamples.PeakValues.WeightedInterleaving

/-!
# Peak-value polynomials in the Eulerian variations paper

This module is the paper-facing entry point for the theorem labeled
`thm:peakValueStability` of P. Alexandersson, *Real-rooted Eulerian polynomials
from permutations, words, and paths*, [arXiv:2609.07325](https://arxiv.org/abs/2609.07325).

The core definitions and proofs remain in
`RealRooted.CombinatorialExamples.PeakValues`. The second theorem below uses
`n` for the smaller rank, so its ranks `n` and `n + 1` correspond to the
paper's ranks `N - 1` and `N`, where `N = n + 1 > 1`. A weight on `Fin (n + 1)`
records the paper's positive weights `λ₁, ..., λₙ₊₁`; the smaller specialization
uses their restriction along `Fin.castSucc`.
-/

namespace RealRooted.Applications.EulerianVariations

noncomputable section

/-- The multivariate peak-value enumerator is real stable in every positive
rank, as in the first assertion of `peakValueStability`. -/
theorem peakValuePolynomial_stable (n : ℕ) (_hn : 1 ≤ n) :
    MvRealStable (peakValuePolynomial n) :=
  RealRooted.peakValuePolynomial_mvRealStable n

/-- Positive weighted diagonal specializations in ranks `n` and `n + 1` are
in proper position. This is the second assertion of `peakValueStability`, with
the paper's larger rank equal to `n + 1`. -/
theorem peakValueWeightedDiagonal_consecutive_prec
    (n : ℕ) (hn : 1 ≤ n) (wt : Fin (n + 1) → ℝ)
    (hwt : ∀ j, 0 < wt j) :
    Prec
      (peakValueWeightedDiagonal (fun j : Fin n => wt j.castSucc))
      (peakValueWeightedDiagonal wt) :=
  RealRooted.peakValueWeightedDiagonal_consecutive_prec n hn wt hwt

end

end RealRooted.Applications.EulerianVariations
