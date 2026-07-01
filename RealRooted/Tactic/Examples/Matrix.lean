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
  rr_matrix0 using G, hG_rect, hG_nonneg, hG_affine, fs, hfs_len, hfs

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
    G, hG_rect, hG_nonneg, hG_affine, fs, hfs_len, hfs, hfs_real

end Tactic
end RealRooted
