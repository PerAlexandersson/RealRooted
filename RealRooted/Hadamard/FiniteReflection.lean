import RealRooted.MultiplierSequence.PolyaSchur

/-!
# Finite multiplier sequences with alternating signs

Human statement:
https://www.symmetricfunctions.com/realRooted.htm#finiteMultiplierSequenceCriterion

The finite Pólya--Schur theorem `finitePolyaSchur_nonneg` treats nonnegative
sequences, whose Jensen polynomials have their zeros in `(-∞, 0]`.  The
reflection `x ↦ -x` multiplies the `k`-th coefficient by `(-1)^k`.  It
preserves real-rootedness, so it transports the theorem to sequences with
`0 ≤ (-1)^k γ_k`, whose Jensen polynomials have their zeros in `[0, ∞)`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Composition with `-X` preserves and reflects being zero or real-rooted. -/
theorem comp_neg_X_eq_zero_or_splits_iff {p : ℝ[X]} :
    (p.comp (-X) = 0 ∨ (p.comp (-X)).Splits) ↔ (p = 0 ∨ p.Splits) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with h | h
    · exact .inl (comp_neg_X_eq_zero_iff.mp h)
    · exact .inr (by simpa [comp_neg_X_comp_neg_X] using h.comp_neg_X)
  · rcases h with h | h
    · exact .inl (by simp [h])
    · exact .inr h.comp_neg_X

/-- Alternating the signs of a sequence reflects its Jensen polynomial in
`x ↦ -x`. -/
theorem jensenPolynomial_alternating (n : ℕ) (gamma : ℕ → ℝ) :
    jensenPolynomial n (fun k ↦ (-1) ^ k * gamma k) =
      (jensenPolynomial n gamma).comp (-X) := by
  rw [jensenPolynomial_mul_sequence_eq_diagonalOperator]
  simpa using diagonalOperator_alternating (fun _ ↦ 1) (jensenPolynomial n gamma)

/-- Alternating the signs of a sequence preserves and reflects the finite
multiplier-sequence property. -/
theorem isFiniteMultiplierSequence_alternating_iff {n : ℕ} {gamma : ℕ → ℝ} :
    IsFiniteMultiplierSequence n (fun k ↦ (-1) ^ k * gamma k) ↔
      IsFiniteMultiplierSequence n gamma := by
  refine ⟨fun h p hp hsplits ↦ ?_, IsFiniteMultiplierSequence.alternating⟩
  simpa [← mul_assoc, ← mul_pow] using h.alternating hp hsplits

/-- Finite Pólya--Schur theorem, `[0, ∞)` case (Brändén, Thm. 3.14): if
`(-1)^k γ_k ≥ 0` for all `k`, then `γ` is a multiplier sequence on polynomials
of degree at most `n` if and only if its Jensen polynomial
`∑ₖ (n choose k) γₖ xᵏ` is zero or real-rooted with all zeros nonnegative. -/
theorem isFiniteMultiplierSequence_iff_jensenPolynomial_roots_nonneg
    {n : ℕ} {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ (-1) ^ k * gamma k) :
    IsFiniteMultiplierSequence n gamma ↔
      (jensenPolynomial n gamma = 0 ∨ (jensenPolynomial n gamma).Splits) ∧
        ∀ r ∈ (jensenPolynomial n gamma).roots, 0 ≤ r := by
  rw [← isFiniteMultiplierSequence_alternating_iff, finitePolyaSchur_nonneg hgamma,
    jensenPolynomial_alternating, IsPFPolynomial, roots_comp_neg_X,
    comp_neg_X_eq_zero_or_splits_iff]
  have hnn : HasNonnegCoeffs ((jensenPolynomial n gamma).comp (-X)) := by
    rw [← jensenPolynomial_alternating]
    exact hasNonnegCoeffs_jensenPolynomial hgamma
  simp only [Multiset.forall_mem_map_iff, neg_nonpos]
  exact ⟨And.right, And.intro hnn⟩

end RealRooted
