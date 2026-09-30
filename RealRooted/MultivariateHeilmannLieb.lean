import RealRooted.Graph.MatchingPolynomial.Multivariate
import RealRooted.HeilmannLieb

/-!
# Multivariate-to-univariate Heilmann--Lieb specializations

This file connects the multivariate edge-matching polynomial to the existing
weighted univariate splitness and Pólya-frequency endpoints.
-/

noncomputable section

namespace RealRooted
namespace Graph

universe u

/-- The weighted multivariate edge-matching polynomial recovers the checked
univariate Heilmann--Lieb theorem under the unit common-phase specialization. -/
theorem commonPhaseRestriction_one_weightedMultivariateMatchingPolynomialByEdges_splits
    {V : Type u} [Fintype V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ)
    (hwt : ∀ e, 0 ≤ wt e) :
    (commonPhaseRestriction (fun _ => 1)
      (weightedMultivariateMatchingPolynomialByEdges G wt)).Splits := by
  classical
  rw [commonPhaseRestriction_one_weightedMultivariateMatchingPolynomialByEdges]
  exact weightedMatchingPolynomialByEdges_splits G wt hwt

/-- The same specialization recovers the existing Pólya-frequency endpoint. -/
theorem commonPhaseRestriction_one_weightedMultivariateMatchingPolynomialByEdges_isPFPolynomial
    {V : Type u} [Fintype V]
    (G : _root_.SimpleGraph V) (wt : G.edgeSet → ℝ)
    (hwt : ∀ e, 0 ≤ wt e) :
    IsPFPolynomial (commonPhaseRestriction (fun _ => 1)
      (weightedMultivariateMatchingPolynomialByEdges G wt)) := by
  classical
  rw [commonPhaseRestriction_one_weightedMultivariateMatchingPolynomialByEdges]
  exact weightedMatchingPolynomialByEdges_isPFPolynomial G wt hwt

end Graph
end RealRooted
