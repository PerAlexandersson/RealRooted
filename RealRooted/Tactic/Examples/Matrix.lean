import RealRooted.Tactic.Matrix

/-!
# `rr_matrix` examples

Abstract smoke tests for the matrix-transfer dispatcher tactics.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {n : ℕ} (hn : 0 < n) (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeqNonneg (matPolyAction G fs) := by
  rr_matrix using hn, G, hG_rect, hG_nonneg, hG_affine, fs, hfs_len, hfs

example {n : ℕ} (hn : 0 < n) (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeqNonneg (matPolyAction G fs) := by
  rr_matrix using
    n_pos := hn,
    matrix := G,
    rectangular := hG_rect,
    entry_nonneg := hG_nonneg,
    two_by_two := hG_affine,
    input := fs,
    input_length := hfs_len,
    input_interlacing := hfs

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) := by
  rr_matrix0

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) := by
  rr_matrix0 using
    matrix := G,
    rectangular := hG_rect,
    entry_nonneg := hG_nonneg,
    two_by_two := hG_affine,
    input := fs,
    input_length := hfs_len,
    input_interlacing := hfs

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeqNonneg ((matPolyAction G fs).filter (· ≠ 0)) := by
  rr_matrix0_filter_ne_zero using
    G, hG_rect, hG_nonneg, hG_affine, fs, hfs_len, hfs

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeqNonneg ((matPolyAction G fs).filter (· ≠ 0)) := by
  rr_matrix0_filter_ne_zero using
    matrix := G,
    rectangular := hG_rect,
    entry_nonneg := hG_nonneg,
    two_by_two := hG_affine,
    input := fs,
    input_length := hfs_len,
    input_interlacing := hfs

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) ∧
      ∀ f ∈ matPolyAction G fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  rr_matrix0_realrooted using G, hG_rect, hG_nonneg, hG_affine, fs, hfs_len, hfs

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) ∧
      ∀ f ∈ matPolyAction G fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  rr_matrix0_realrooted using
    matrix := G,
    rectangular := hG_rect,
    entry_nonneg := hG_nonneg,
    two_by_two := hG_affine,
    input := fs,
    input_length := hfs_len,
    input_interlacing := hfs

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) ∧
      ∀ f ∈ matPolyAction G fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  rr_matrix0_weak

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) ∧
      ∀ f ∈ matPolyAction G fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  rr_matrix0_weak using
    matrix := G,
    rectangular := hG_rect,
    entry_nonneg := hG_nonneg,
    two_by_two := hG_affine,
    input := fs,
    input_length := hfs_len,
    input_interlacing := hfs,
    input_real_rooted := hfs_real

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeqNonneg ((matPolyAction G fs).filter (· ≠ 0)) := by
  rr_matrix0_filter_ne_zero_weak using
    G, hG_rect, hG_nonneg, hG_affine, fs, hfs_len, hfs, hfs_real

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeqNonneg ((matPolyAction G fs).filter (· ≠ 0)) := by
  rr_matrix0_filter_ne_zero_weak using
    matrix := G,
    rectangular := hG_rect,
    entry_nonneg := hG_nonneg,
    two_by_two := hG_affine,
    input := fs,
    input_length := hfs_len,
    input_interlacing := hfs,
    input_real_rooted := hfs_real

example {n : ℕ} (hn : 0 < n) (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_threshold : HasRowThresholdLinearStructure G)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeqNonneg (matPolyAction G fs) := by
  rr_row_threshold_matrix using
    n_pos := hn,
    matrix := G,
    rectangular := hG_rect,
    row_threshold := hG_threshold,
    two_by_two := hG_affine,
    input := fs,
    input_length := hfs_len,
    input_interlacing := hfs

example {n : ℕ} (hn : 0 < n) (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_threshold : HasRowThresholdLinearStructure G)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeqNonneg (matPolyAction G fs) := by
  rr_row_threshold_matrix using
    hn, G, hG_rect, hG_threshold, hG_affine, fs, hfs_len, hfs

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_threshold : HasRowThresholdLinearStructure G)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) := by
  rr_row_threshold_matrix0 using
    matrix := G,
    rectangular := hG_rect,
    row_threshold := hG_threshold,
    two_by_two := hG_affine,
    input := fs,
    input_length := hfs_len,
    input_interlacing := hfs

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_threshold : HasRowThresholdLinearStructure G)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) := by
  rr_row_threshold_matrix0

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_threshold : HasRowThresholdLinearStructure G)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) ∧
      ∀ f ∈ matPolyAction G fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  rr_row_threshold_matrix0_weak using
    matrix := G,
    rectangular := hG_rect,
    row_threshold := hG_threshold,
    two_by_two := hG_affine,
    input := fs,
    input_length := hfs_len,
    input_interlacing := hfs,
    input_real_rooted := hfs_real

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_threshold : HasRowThresholdLinearStructure G)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) ∧
      ∀ f ∈ matPolyAction G fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  rr_row_threshold_matrix0_weak

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_threshold : HasRowThresholdLinearStructure G)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeqNonneg ((matPolyAction G fs).filter (· ≠ 0)) := by
  rr_row_threshold_matrix0_filter_ne_zero_weak using
    matrix := G,
    rectangular := hG_rect,
    row_threshold := hG_threshold,
    two_by_two := hG_affine,
    input := fs,
    input_length := hfs_len,
    input_interlacing := hfs,
    input_real_rooted := hfs_real

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_threshold : HasRowThresholdLinearStructure G)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeqNonneg ((matPolyAction G fs).filter (· ≠ 0)) := by
  rr_row_threshold_matrix0_filter_ne_zero_weak using
    G, hG_rect, hG_threshold, hG_affine, fs, hfs_len, hfs, hfs_real

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_threshold : HasRowThresholdLinearStructure G)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) ∧
      ∀ f ∈ matPolyAction G fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  rr_row_threshold_matrix0_realrooted using
    matrix := G,
    rectangular := hG_rect,
    row_threshold := hG_threshold,
    two_by_two := hG_affine,
    input := fs,
    input_length := hfs_len,
    input_interlacing := hfs

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_threshold : HasRowThresholdLinearStructure G)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) ∧
      ∀ f ∈ matPolyAction G fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  rr_row_threshold_matrix0_realrooted using
    G, hG_rect, hG_threshold, hG_affine, fs, hfs_len, hfs

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_threshold : HasRowThresholdLinearStructure G)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeqNonneg ((matPolyAction G fs).filter (· ≠ 0)) := by
  rr_row_threshold_matrix0_filter_ne_zero using
    matrix := G,
    rectangular := hG_rect,
    row_threshold := hG_threshold,
    two_by_two := hG_affine,
    input := fs,
    input_length := hfs_len,
    input_interlacing := hfs

example {n : ℕ} (G : List (List ℝ[X])) (fs : List ℝ[X])
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_threshold : HasRowThresholdLinearStructure G)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeqNonneg ((matPolyAction G fs).filter (· ≠ 0)) := by
  rr_row_threshold_matrix0_filter_ne_zero using
    G, hG_rect, hG_threshold, hG_affine, fs, hfs_len, hfs

example {G : List (List ℝ[X])}
    (hG_threshold : HasRowThresholdLinearStructure G) :
    ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p := by
  rr_row_threshold_entry_nonneg using row_threshold := hG_threshold

example {G : List (List ℝ[X])}
    (hG_threshold : HasRowThresholdLinearStructure G) :
    ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p := by
  rr_row_threshold_entry_nonneg

namespace MatrixInferenceSmoke

def baseMatrix : List (List ℝ[X]) := []

def decoyMatrix : List (List ℝ[X]) := [[]]

theorem baseMatrix_rect : ∀ row ∈ baseMatrix, row.length = 0 := by
  simp [baseMatrix]

theorem decoyMatrix_rect : ∀ row ∈ decoyMatrix, row.length = 0 := by
  simp [decoyMatrix]

theorem baseMatrix_wrongWidth_rect (h : False) :
    ∀ row ∈ baseMatrix, row.length = 1 := by
  contradiction

theorem baseMatrix_nonneg :
    ∀ row ∈ baseMatrix, ∀ p ∈ row, HasNonnegCoeffs p := by
  simp [baseMatrix]

theorem decoyMatrix_nonneg :
    ∀ row ∈ decoyMatrix, ∀ p ∈ row, HasNonnegCoeffs p := by
  simp [decoyMatrix]

def ZeroWidthTwoByTwo (G : List (List ℝ[X])) : Prop :=
    ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin 0),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by exact Fin.elim0 j₁⟩)
        ((G.get i₁).get ⟨j₂, by exact Fin.elim0 j₂⟩)
        ((G.get i₂).get ⟨j₁, by exact Fin.elim0 j₁⟩)
        ((G.get i₂).get ⟨j₂, by exact Fin.elim0 j₂⟩)

theorem zeroWidth_twoByTwo (G : List (List ℝ[X])) :
    ZeroWidthTwoByTwo G := by
  unfold ZeroWidthTwoByTwo
  intro _ _ j₁
  exact Fin.elim0 j₁

theorem baseMatrix_twoByTwo : ZeroWidthTwoByTwo baseMatrix :=
  zeroWidth_twoByTwo baseMatrix

theorem decoyMatrix_twoByTwo : ZeroWidthTwoByTwo decoyMatrix :=
  zeroWidth_twoByTwo decoyMatrix

theorem baseMatrix_threshold : HasRowThresholdLinearStructure baseMatrix := by
  simp [HasRowThresholdLinearStructure, baseMatrix]

theorem decoyMatrix_threshold :
    HasRowThresholdLinearStructure decoyMatrix := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro i
    fin_cases i
    simp [HasRowThreshold, decoyMatrix]
  · intro i j _
    simp

attribute [rr_matrix_rect]
  baseMatrix_wrongWidth_rect baseMatrix_rect decoyMatrix_rect
attribute [rr_matrix_nonneg] baseMatrix_nonneg decoyMatrix_nonneg
attribute [rr_matrix_2x2] baseMatrix_twoByTwo decoyMatrix_twoByTwo
attribute [rr_matrix_threshold] baseMatrix_threshold decoyMatrix_threshold

example (hfs_len : ([] : List ℝ[X]).length = 0)
    (hfs : IsInterlacingSeqNonneg ([] : List ℝ[X])) :
    IsInterlacingSeq0Nonneg (matPolyAction baseMatrix []) := by
  rr_matrix0

example (hfs_len : ([] : List ℝ[X]).length = 0)
    (hfs : IsInterlacingSeqNonneg ([] : List ℝ[X])) :
    IsInterlacingSeq0Nonneg (matPolyAction decoyMatrix []) := by
  rr_matrix0

example (hfs_len : ([] : List ℝ[X]).length = 0)
    (hfs : IsInterlacingSeqNonneg ([] : List ℝ[X])) :
    IsInterlacingSeq0Nonneg (matPolyAction baseMatrix []) := by
  rr_row_threshold_matrix0

example (hfs_len : ([] : List ℝ[X]).length = 0)
    (hfs : IsInterlacingSeq0Nonneg ([] : List ℝ[X]))
    (hfs_real : ∀ f ∈ ([] : List ℝ[X]), f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction baseMatrix []) ∧
      ∀ f ∈ matPolyAction baseMatrix [], f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  rr_matrix0_weak

example : ∀ row ∈ baseMatrix, ∀ p ∈ row, HasNonnegCoeffs p := by
  rr_row_threshold_entry_nonneg

end MatrixInferenceSmoke

end Tactic
end RealRooted
