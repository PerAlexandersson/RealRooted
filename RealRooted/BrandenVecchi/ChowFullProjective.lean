import RealRooted.BrandenVecchi.ChowInfinitePF
import RealRooted.BrandenVecchi.ChowProjectiveRegularization

/-!
# Full ASW--Edrei projective Chow boundary

This file packages the scalar and zero-prefix boundary around the generic
projective regularization. A zero outer scalar has zero output. Every nonzero
outer scalar represents the same projective class, so the positive-scalar
branch is independent of its magnitude.
-/

open Polynomial

namespace RealRooted.BrandenVecchi

noncomputable section

/-- Projective Chow row for the full ASW--Edrei symbol. A zero outer scalar
has zero projective output; every nonzero scalar represents the same class. -/
def aswEdreiFullProjectiveChow
    (outer : ℝ) (N : ℕ) (gamma : ℝ) (alpha beta : ℕ → ℝ)
    (epsilon : ℝ) (n : ℕ) : ℝ[X] :=
  if outer = 0 then 0 else
    projectiveRegularizedChow N (aswEdreiCoeff gamma alpha beta) epsilon n

@[simp]
theorem aswEdreiFullProjectiveChow_zero_outer
    (N : ℕ) (gamma : ℝ) (alpha beta : ℕ → ℝ) (epsilon : ℝ) (n : ℕ) :
    aswEdreiFullProjectiveChow 0 N gamma alpha beta epsilon n = 0 := by
  simp [aswEdreiFullProjectiveChow]

/-- Nonzero outer scalars are projectively invisible. -/
theorem aswEdreiFullProjectiveChow_of_ne
    {outer : ℝ} (houter : outer ≠ 0) (N : ℕ)
    (gamma : ℝ) (alpha beta : ℕ → ℝ) (epsilon : ℝ) (n : ℕ) :
    aswEdreiFullProjectiveChow outer N gamma alpha beta epsilon n =
      projectiveRegularizedChow N
        (aswEdreiCoeff gamma alpha beta) epsilon n := by
  simp [aswEdreiFullProjectiveChow, houter]

/-- The nonzero-scalar special fiber is the finite binomial-symbol row. -/
theorem aswEdreiFullProjectiveChow_at_zero_of_ne
    {outer : ℝ} (houter : outer ≠ 0) {gamma : ℝ}
    {alpha beta : ℕ → ℝ}
    (halpha : ∀ i, 0 ≤ alpha i) (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i) (N n : ℕ) :
    aswEdreiFullProjectiveChow outer N gamma alpha beta 0 n =
      binomialSymbolChow N n := by
  rw [aswEdreiFullProjectiveChow_of_ne houter]
  exact projectiveRegularizedChow_at_zero
    (aswEdreiCoeff_zero halpha hbeta hsum) N n

/-- With no zero prefix and at parameter one, the projective row is the
existing constant-origin ASW--Edrei Chow row. -/
theorem aswEdreiFullProjectiveChow_zero_prefix_one_of_ne
    {outer : ℝ} (houter : outer ≠ 0)
    (gamma : ℝ) (alpha beta : ℕ → ℝ) (n : ℕ) :
    aswEdreiFullProjectiveChow outer 0 gamma alpha beta 1 n =
      aswEdreiChow gamma alpha beta n := by
  simp [aswEdreiFullProjectiveChow, houter, projectiveRegularizedChow,
    aswEdreiChow, aswEdreiToeplitz]

/-- Every nonzero epsilon fiber is `epsilon ^ n` times the rank-`n` Chow row
of the unit-normalized raw approximant. -/
theorem aswEdreiFullProjectiveChow_eq_scaled_normalized
    {outer epsilon : ℝ} (houter : outer ≠ 0) (hepsilon : epsilon ≠ 0)
    (N : ℕ) (gamma : ℝ) (alpha beta : ℕ → ℝ) (n : ℕ) :
    aswEdreiFullProjectiveChow outer N gamma alpha beta epsilon n =
      C (epsilon ^ n) *
        chowPolynomial
          (toeplitz (unitNormalizedRegularizedSequence N
            (aswEdreiCoeff gamma alpha beta) epsilon)) n := by
  rw [aswEdreiFullProjectiveChow_of_ne houter]
  exact projectiveRegularizedChow_eq_scaled_normalized
    hepsilon N (aswEdreiCoeff gamma alpha beta) n

/-- Corrected full ASW--Edrei Chow theorem. For a nonnegative outer scalar,
the zero branch is literal zero and every positive branch is represented by
the projective regularization. All nonnegative epsilon fibers are PF and
consecutive ranks are in zero-aware proper position. -/
theorem aswEdreiFullProjectiveChow_theorem
    {outer gamma epsilon : ℝ} {N : ℕ} {alpha beta : ℕ → ℝ}
    (houter : 0 ≤ outer) (hgamma : 0 ≤ gamma)
    (halpha : ∀ i, 0 ≤ alpha i)
    (hbeta : ∀ i, 0 ≤ beta i)
    (hsum : Summable fun i => alpha i + beta i)
    (hepsilon : 0 ≤ epsilon) (n : ℕ) :
    IsPFPolynomial
        (aswEdreiFullProjectiveChow outer N gamma alpha beta epsilon n) ∧
      Prec0
        (aswEdreiFullProjectiveChow outer N gamma alpha beta epsilon n)
        (aswEdreiFullProjectiveChow outer N gamma alpha beta epsilon
          (n + 1)) := by
  rcases eq_or_lt_of_le houter with rfl | houter_pos
  · constructor
    · simpa using IsPFPolynomial.zero
    · simpa using prec0_zero_zero
  · have houter_ne : outer ≠ 0 := ne_of_gt houter_pos
    rw [aswEdreiFullProjectiveChow_of_ne houter_ne,
      aswEdreiFullProjectiveChow_of_ne houter_ne]
    have hpf := aswEdreiCoeff_isPolyaFreqSeq hgamma halpha hbeta hsum
    have hzero : aswEdreiCoeff gamma alpha beta 0 = 1 :=
      aswEdreiCoeff_zero halpha hbeta hsum
    exact ⟨projectiveRegularizedChow_isPFPolynomial
        hpf hzero hepsilon N n,
      projectiveRegularizedChow_prec0_succ
        hpf hzero hepsilon N n⟩

end

end RealRooted.BrandenVecchi
