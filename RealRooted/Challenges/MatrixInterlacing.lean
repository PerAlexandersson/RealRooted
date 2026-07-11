import RealRooted.MatrixInterlacing

/-!
# Matrix interlacing challenge entry point

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#matrixPreservesInterlacingSequences

Reference: P. Branden, *Unimodality, log-concavity, real-rootedness and
beyond*, Handbook of Enumerative Combinatorics (2015), Theorem 7.8.5.

This module exposes the checked forward matrix-preserver theorem and the
zero-aware variant.  The sparse test families and 2-by-2 reduction machinery
remain in `RealRooted.MatrixInterlacing`.
-/

open Polynomial

namespace RealRooted
namespace Challenges
namespace MatrixInterlacing

/-- Challenge-facing name for a rectangular matrix of real polynomials,
represented by rows. -/
abbrev PolynomialMatrix : Type :=
  List (List ℝ[X])

/-- Challenge-facing name for the matrix action on a polynomial sequence. -/
noncomputable abbrev PolynomialMatrix.action
    (G : PolynomialMatrix) (fs : List ℝ[X]) : List ℝ[X] :=
  matPolyAction G fs

/-- Challenge-facing accessor for a rectangular polynomial matrix. -/
noncomputable abbrev PolynomialMatrix.entry {n : Nat} (G : PolynomialMatrix)
    (hG_rect : ∀ row ∈ G, row.length = n) (i : Fin G.length) (j : Fin n) :
    ℝ[X] :=
  (G.get i).get ⟨j, by
    have hrow := hG_rect (G.get i) (List.get_mem G i)
    simpa [← hrow] using j.2⟩

/-- Challenge-facing name for the affine `2 × 2` condition in Brändén's
matrix criterion. -/
abbrev AffineTwoByTwoInterlaces (a b c d : ℝ[X]) : Prop :=
  Has2x2InterlacingProperty a b c d

/-- Zero-aware version of the affine `2 × 2` condition. -/
abbrev AffineTwoByTwoInterlacesOrZero (a b c d : ℝ[X]) : Prop :=
  Has2x2InterlacingProperty0 a b c d

/-- Entrywise affine `2 × 2` condition for all ordered row and column pairs. -/
abbrev PolynomialMatrix.AffineTwoByTwoCondition {n : Nat} (G : PolynomialMatrix)
    (hG_rect : ∀ row ∈ G, row.length = n)
    (R : ℝ[X] → ℝ[X] → ℝ[X] → ℝ[X] → Prop) : Prop :=
  ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
    i₁ ≤ i₂ → j₁ ≤ j₂ →
      R (G.entry hG_rect i₁ j₁) (G.entry hG_rect i₁ j₂)
        (G.entry hG_rect i₂ j₁) (G.entry hG_rect i₂ j₂)

/-- Branden's matrix criterion, forward direction: the affine 2-by-2
conditions imply preservation of nonnegative interlacing sequences. -/
theorem preserves_interlacing_sequences :
    ∀ {n : Nat} (_hn : 0 < n) (G : PolynomialMatrix)
      (hG_rect : ∀ row ∈ G, row.length = n)
      (_hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
      (_hG_affine : G.AffineTwoByTwoCondition hG_rect AffineTwoByTwoInterlaces)
      (fs : List ℝ[X]) (_hfs_len : fs.length = n)
      (_hfs : IsInterlacingSeqNonneg fs),
        IsInterlacingSeqNonneg (G.action fs) :=
  RealRooted.matrix_preserves_interlacing_seq

/-- Zero-aware forward direction, useful when some output rows vanish. -/
theorem preserves_interlacing_sequences_zeroAware :
    ∀ {n : Nat} (G : PolynomialMatrix)
      (hG_rect : ∀ row ∈ G, row.length = n)
      (_hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
      (_hG_affine :
        G.AffineTwoByTwoCondition hG_rect AffineTwoByTwoInterlacesOrZero)
      (fs : List ℝ[X]) (_hfs_len : fs.length = n)
      (_hfs : IsInterlacingSeqNonneg fs),
        IsInterlacingSeq0Nonneg (G.action fs) :=
  RealRooted.matrix_preserves_interlacing_seq0_of_2x2

end MatrixInterlacing
end Challenges
end RealRooted
