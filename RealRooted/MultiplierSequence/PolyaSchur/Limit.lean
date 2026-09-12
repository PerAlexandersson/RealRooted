import RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots.Real
import RealRooted.MultiplierSequence.PolyaSchur

/-!
# Pointwise limits of PF multiplier sequences

This file proves that Pólya-frequency multiplier sequences are closed under
pointwise limits.  For each fixed degree, the Jensen polynomials have bounded
degree and converge coefficientwise, so closedness of real splitting passes
to the limit.
-/

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-- A pointwise limit of PF multiplier sequences is a PF multiplier sequence. -/
theorem isPFMultiplierSequence_of_tendsto
    {gamma : ℕ → ℕ → ℝ} {gamma₀ : ℕ → ℝ}
    (hgamma : ∀ n, IsPFMultiplierSequence (gamma n))
    (hlim : ∀ k, Tendsto (fun n => gamma n k) atTop (𝓝 (gamma₀ k))) :
    IsPFMultiplierSequence gamma₀ := by
  rw [isPFMultiplierSequence_iff_jensenPolynomial_isPF]
  intro d
  have hnonneg (k : ℕ) : 0 ≤ gamma₀ k :=
    ge_of_tendsto (hlim k) (Eventually.of_forall fun n => (hgamma n).nonneg k)
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
  · exact hasNonnegCoeffs_jensenPolynomial hnonneg
  · apply Polynomial.eq_zero_or_splits_of_tendsto_eval_of_natDegree_le
      (p := fun n => jensenPolynomial d (gamma n)) (N := d)
    · exact fun n => natDegree_jensenPolynomial_le d (gamma n)
    · exact fun n =>
        (isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence (hgamma n) d).eq_zero_or_splits
    · intro z
      have hcoeff (k : ℕ) :
          Tendsto (fun n => (jensenPolynomial d (gamma n)).coeff k) atTop
            (𝓝 ((jensenPolynomial d gamma₀).coeff k)) := by
        simp only [coeff_jensenPolynomial]
        split_ifs
        · exact tendsto_const_nhds.mul (hlim k)
        · exact tendsto_const_nhds
      have hsum : Tendsto
          (fun n => ∑ k ∈ Finset.range (d + 1),
            (((jensenPolynomial d (gamma n)).coeff k : ℝ) : ℂ) * z ^ k)
          atTop
          (𝓝 (∑ k ∈ Finset.range (d + 1),
            (((jensenPolynomial d gamma₀).coeff k : ℝ) : ℂ) * z ^ k)) := by
        refine tendsto_finsetSum _ fun k _ => ?_
        exact ((Complex.continuous_ofReal.tendsto _).comp (hcoeff k)).mul_const (z ^ k)
      rw [show (fun n => ((jensenPolynomial d (gamma n)).map Complex.ofRealHom).eval z) =
          fun n => ∑ k ∈ Finset.range (d + 1),
            (((jensenPolynomial d (gamma n)).coeff k : ℝ) : ℂ) * z ^ k by
        funext n
        rw [Polynomial.eval_map,
          Polynomial.eval₂_eq_sum_range' Complex.ofRealHom
            (Nat.lt_succ_of_le (natDegree_jensenPolynomial_le d (gamma n))) z]
        simp only [Nat.succ_eq_add_one, Complex.ofRealHom_eq_coe]]
      rw [show ((jensenPolynomial d gamma₀).map Complex.ofRealHom).eval z =
          ∑ k ∈ Finset.range (d + 1),
            (((jensenPolynomial d gamma₀).coeff k : ℝ) : ℂ) * z ^ k by
        rw [Polynomial.eval_map,
          Polynomial.eval₂_eq_sum_range' Complex.ofRealHom
            (Nat.lt_succ_of_le (natDegree_jensenPolynomial_le d gamma₀)) z]
        simp only [Nat.succ_eq_add_one, Complex.ofRealHom_eq_coe]]
      exact hsum

end RealRooted
