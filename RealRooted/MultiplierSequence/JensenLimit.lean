module

public import RealRooted.MultiplierSequence
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots.Real

/-!
# Coefficientwise limits of splitting Jensen polynomials
-/

public section

open Polynomial Complex Filter Topology

namespace RealRooted

/-- Splitting of a fixed-degree Jensen polynomial is closed under pointwise
limits of its defining real sequence. -/
theorem jensenPolynomial_splits_of_tendsto {a : ℕ → ℕ → ℝ} {b : ℕ → ℝ}
    (d : ℕ) (ha : ∀ n, (jensenPolynomial d (a n)).Splits)
    (hlim : ∀ k, Tendsto (fun n => a n k) atTop (𝓝 (b k))) :
    (jensenPolynomial d b).Splits := by
  have heval (z : ℂ) :
      Tendsto (fun n => ((jensenPolynomial d (a n)).map ofRealHom).eval z) atTop
        (𝓝 (((jensenPolynomial d b).map ofRealHom).eval z)) := by
    simp only [jensenPolynomial, Polynomial.map_sum, Polynomial.map_monomial,
      Polynomial.eval_finsetSum, Polynomial.eval_monomial, ofRealHom_eq_coe,
      ofReal_mul, ofReal_natCast]
    exact tendsto_finsetSum _ fun k _ =>
      (tendsto_const_nhds.mul (hlim k).ofReal).mul_const (z ^ k)
  rcases Polynomial.eq_zero_or_splits_of_tendsto_eval_of_natDegree_le
    (N := d) (fun n => natDegree_jensenPolynomial_le d (a n))
    (fun n => Or.inr (ha n)) heval with hz | hs
  · rw [hz]
    exact Splits.zero
  · exact hs

end RealRooted
