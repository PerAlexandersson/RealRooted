import RealRooted.Hadamard.Grace

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

private theorem coeff_comp_neg_X (p : ℝ[X]) (k : ℕ) :
    (p.comp (-X)).coeff k = (-1) ^ k * p.coeff k := by
  rw [mul_comm]
  simpa using Polynomial.comp_C_mul_X_coeff (p := p) (r := (-1 : ℝ)) (n := k)

private theorem eq_zero_or_splits_comp_neg_X_iff {p : ℝ[X]} :
    (p.comp (-X) = 0 ∨ (p.comp (-X)).Splits) ↔ (p = 0 ∨ p.Splits) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h with h | h
    · exact .inl (comp_neg_X_eq_zero_iff.mp h)
    · exact .inr (by simpa [comp_neg_X_comp_neg_X] using h.comp_neg_X)
  · rcases h with h | h
    · exact .inl (by simp [h])
    · exact .inr h.comp_neg_X

/-- Multiplying a diagonal sequence by `(-1)^k` reflects its output in
`x ↦ -x`. -/
theorem diagonalOperator_neg_one_pow_mul (gamma : ℕ → ℝ) (p : ℝ[X]) :
    diagonalOperator (fun k ↦ (-1) ^ k * gamma k) p =
      (diagonalOperator gamma p).comp (-X) := by
  ext k
  rw [coeff_diagonalOperator, coeff_comp_neg_X, coeff_diagonalOperator, mul_assoc]

/-- Multiplying a sequence by `(-1)^k` reflects its Jensen polynomial in
`x ↦ -x`. -/
theorem jensenPolynomial_neg_one_pow_mul (n : ℕ) (gamma : ℕ → ℝ) :
    jensenPolynomial n (fun k ↦ (-1) ^ k * gamma k) =
      (jensenPolynomial n gamma).comp (-X) := by
  ext k
  rw [coeff_jensenPolynomial, coeff_comp_neg_X, coeff_jensenPolynomial]
  split_ifs <;> ring

/-- Finite multiplier sequences are invariant under multiplication by
`(-1)^k`. -/
theorem isFiniteMultiplierSequence_neg_one_pow_mul_iff {n : ℕ} {gamma : ℕ → ℝ} :
    IsFiniteMultiplierSequence n (fun k ↦ (-1) ^ k * gamma k) ↔
      IsFiniteMultiplierSequence n gamma := by
  simp only [IsFiniteMultiplierSequence, diagonalOperator_neg_one_pow_mul,
    eq_zero_or_splits_comp_neg_X_iff]

/-- Finite Pólya--Schur theorem, `[0, ∞)` case (Brändén, Thm. 3.14): if
`(-1)^k γ_k ≥ 0` for all `k`, then `γ` is a multiplier sequence on polynomials
of degree at most `n` if and only if its Jensen polynomial
`∑ₖ (n choose k) γₖ xᵏ` is zero or real-rooted with all zeros nonnegative. -/
theorem isFiniteMultiplierSequence_iff_jensenPolynomial_roots_nonneg
    {n : ℕ} {gamma : ℕ → ℝ} (hgamma : ∀ k, 0 ≤ (-1) ^ k * gamma k) :
    IsFiniteMultiplierSequence n gamma ↔
      (jensenPolynomial n gamma = 0 ∨ (jensenPolynomial n gamma).Splits) ∧
        ∀ r ∈ (jensenPolynomial n gamma).roots, 0 ≤ r := by
  rw [← isFiniteMultiplierSequence_neg_one_pow_mul_iff, finitePolyaSchur_nonneg hgamma,
    jensenPolynomial_neg_one_pow_mul, IsPFPolynomial, roots_comp_neg_X,
    eq_zero_or_splits_comp_neg_X_iff]
  have hnn : HasNonnegCoeffs ((jensenPolynomial n gamma).comp (-X)) := by
    rw [← jensenPolynomial_neg_one_pow_mul]
    exact hasNonnegCoeffs_jensenPolynomial hgamma
  simp only [Multiset.forall_mem_map_iff, neg_nonpos]
  exact ⟨And.right, And.intro hnn⟩

end RealRooted
