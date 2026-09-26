import RealRooted.MatrixInterlacing

/-!
# Matrix interlacing challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "matrix-interlacing"
authors = ["Brändén"]
years = [2015]

[[definitions]]
name = "RealRooted.matPolyAction"
module = "RealRooted.MatrixInterlacing.Action"

[[definitions]]
name = "RealRooted.Has2x2InterlacingProperty"
module = "RealRooted.AffineFamily.Basic"

[[definitions]]
name = "RealRooted.Has2x2InterlacingProperty0"
module = "RealRooted.AffineFamily.Basic"

[[theorems]]
name = "RealRooted.Challenges.MatrixInterlacing.preserves_interlacing_sequences"

[[theorems]]
name = "RealRooted.Challenges.MatrixInterlacing.preserves_interlacing_sequences_zeroAware"
-->

<!-- realrooted-catalog-content -->
# Matrices preserving interlacing sequences

A nonnegative polynomial matrix preserves interlacing sequences when every
ordered `2 × 2` submatrix satisfies Brändén’s affine interlacing condition.
A zero-aware form allows output rows to vanish.

## References

P. Brändén, “Unimodality, log-concavity, real-rootedness and beyond,” in
*Handbook of Enumerative Combinatorics*, 2015, Theorem 7.8.5.  See the
[matrix criterion on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#matrixPreservesInterlacingSequences).
<!-- /realrooted-catalog-content -->

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

/-- Branden's matrix criterion, forward direction: the affine 2-by-2
conditions imply preservation of nonnegative interlacing sequences. -/
theorem preserves_interlacing_sequences :
    ∀ {n : Nat} (_hn : 0 < n) (G : List (List ℝ[X]))
      (hG_rect : ∀ row ∈ G, row.length = n)
      (_hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
      (_hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
        i₁ ≤ i₂ → j₁ ≤ j₂ →
        Has2x2InterlacingProperty
          ((G.get i₁).get ⟨j₁, by simp_all⟩)
          ((G.get i₁).get ⟨j₂, by simp_all⟩)
          ((G.get i₂).get ⟨j₁, by simp_all⟩)
          ((G.get i₂).get ⟨j₂, by simp_all⟩))
      (fs : List ℝ[X]) (_hfs_len : fs.length = n)
      (_hfs : IsInterlacingSeqNonneg fs),
        IsInterlacingSeqNonneg (matPolyAction G fs) :=
  RealRooted.matrix_preserves_interlacing_seq

/-- Zero-aware forward direction, useful when some output rows vanish. -/
theorem preserves_interlacing_sequences_zeroAware :
    ∀ {n : Nat} (G : List (List ℝ[X]))
      (hG_rect : ∀ row ∈ G, row.length = n)
      (_hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
      (_hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
        i₁ ≤ i₂ → j₁ ≤ j₂ →
        Has2x2InterlacingProperty0
          ((G.get i₁).get ⟨j₁, by simp_all⟩)
          ((G.get i₁).get ⟨j₂, by simp_all⟩)
          ((G.get i₂).get ⟨j₁, by simp_all⟩)
          ((G.get i₂).get ⟨j₂, by simp_all⟩))
      (fs : List ℝ[X]) (_hfs_len : fs.length = n)
      (_hfs : IsInterlacingSeqNonneg fs),
        IsInterlacingSeq0Nonneg (matPolyAction G fs) :=
  RealRooted.matrix_preserves_interlacing_seq0_of_2x2

end MatrixInterlacing
end Challenges
end RealRooted
