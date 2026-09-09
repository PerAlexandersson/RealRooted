import RealRooted.MatrixInterlacing.Action
import RealRooted.MatrixInterlacing.SparseTests

open Polynomial

noncomputable section

namespace RealRooted

/-- Weak zero-aware converse, entrywise nonnegativity half.

This is the clean handbook-style target for recovering condition (1) from a
matrix action hypothesis in the presence of zero polynomials. The intended proof
uses single-support test vectors (`1` in one position, `0` elsewhere), which do
not belong to the current strict `IsInterlacingSeqNonneg` family but do belong
to the weak `IsInterlacingSeq0Nonneg` family introduced above. -/
theorem matrix_preserves_interlacing_seq0_nonneg_entries
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hpres0 : ∀ (fs : List ℝ[X]), fs.length = n → IsInterlacingSeq0Nonneg fs →
      IsInterlacingSeq0Nonneg (matPolyAction G fs)) :
    ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p := fun row hrow p hp => by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hp
  let fs := oneSupportSeq row.length i
  have hfs_len : fs.length = n := by simp [fs, hG_rect _ hrow]
  have hfs : IsInterlacingSeq0Nonneg fs := by
    simpa [fs] using isInterlacingSeq0Nonneg_oneSupportSeq i
  have himage : IsInterlacingSeq0Nonneg (matPolyAction G fs) := hpres0 fs hfs_len hfs
  have hrow_eval :
      (row.zipWith (· * ·) fs).sum = row.get i := by
    simpa [fs] using zipWith_mul_oneSupportSeq_sum_eq_get row i
  have hmem_eval : (row.zipWith (· * ·) fs).sum ∈ matPolyAction G fs :=
    List.mem_map.2 ⟨row, hrow, rfl⟩
  simpa [hrow_eval] using himage.2 _ hmem_eval

theorem matrix_preserves_interlacing_seq0_sparse_pair_prec0
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hpres0 : ∀ (fs : List ℝ[X]), fs.length = n → IsInterlacingSeq0Nonneg fs →
      IsInterlacingSeq0Nonneg (matPolyAction G fs))
    (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n)
    (hi : i₁ < i₂) (hj : j₁ < j₂)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Prec0
      (((G.get i₁).get ⟨j₁, by simp_all⟩
          + (C a * X + C b)
            * ((G.get i₁).get ⟨j₂, by simp_all⟩)))
      (((G.get i₂).get ⟨j₁, by simp_all⟩
          + (C a * X + C b)
            * ((G.get i₂).get ⟨j₂, by simp_all⟩))) := by
  let fs := sparseLinearPairSeq n j₁ j₂ a b
  have hfs_len : fs.length = n := by simp [fs]
  have hfs : IsInterlacingSeq0Nonneg fs := by
    simpa [fs] using isInterlacingSeq0Nonneg_sparseLinearPairSeq hj ha hb
  have himage : IsInterlacingSeq0Nonneg (matPolyAction G fs) := hpres0 fs hfs_len hfs
  let iG : Fin (matPolyAction G fs).length := ⟨i₁, by simp [matPolyAction]⟩
  let iRowJ₁ : Fin (G.get i₁).length := ⟨j₁, by simp_all⟩
  let iRowJ₂ : Fin (G.get i₁).length := ⟨j₂, by simp_all⟩
  let jG : Fin (matPolyAction G fs).length := ⟨i₂, by simp [matPolyAction]⟩
  let jRowJ₁ : Fin (G.get i₂).length := ⟨j₁, by simp_all⟩
  let jRowJ₂ : Fin (G.get i₂).length := ⟨j₂, by simp_all⟩
  have hpair : Prec0 ((matPolyAction G fs).get iG) ((matPolyAction G fs).get jG) :=
    himage.1.prec0 (i := iG) (j := jG) (by grind)
  have hleft :
      (matPolyAction G fs).get iG
        = (G.get i₁).get iRowJ₁ + (C a * X + C b) * (G.get i₁).get iRowJ₂ := by
    simpa [matPolyAction, fs, iG, iRowJ₁, iRowJ₂] using
      zipWith_mul_sparseLinearPairSeq_sum_eq_of_length
        (row := G.get i₁) (n := n) (hrow_len := hG_rect _ (G.get_mem i₁))
        j₁ j₂ (ne_of_lt hj) a b
  have hright :
      (matPolyAction G fs).get jG
        = (G.get i₂).get jRowJ₁ + (C a * X + C b) * (G.get i₂).get jRowJ₂ := by
    simpa [matPolyAction, fs, jG, jRowJ₁, jRowJ₂] using
      zipWith_mul_sparseLinearPairSeq_sum_eq_of_length
        (row := G.get i₂) (n := n) (hrow_len := hG_rect _ (G.get_mem i₂))
        j₁ j₂ (ne_of_lt hj) a b
  lia

/-- Weak handbook-style converse package: a matrix preserving the zero-aware
family `𝓕ₙ⁰⁺` must have entrywise nonnegative coefficients, and its 2×2 affine
sparse test images satisfy the corresponding weak `Prec0` relation. -/
theorem matrix_preserves_interlacing_seq0_necessary_conditions
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hpres0 : ∀ (fs : List ℝ[X]), fs.length = n → IsInterlacingSeq0Nonneg fs →
      IsInterlacingSeq0Nonneg (matPolyAction G fs)) :
    (∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p) ∧
    (∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ < i₂ → j₁ < j₂ →
      ∀ {a b : ℝ}, 0 < a → 0 < b →
      Prec0
        (((G.get i₁).get ⟨j₁, by
            simp_all⟩)
          + (C a * X + C b) * ((G.get i₁).get ⟨j₂, by
            simp_all⟩))
        (((G.get i₂).get ⟨j₁, by
            simp_all⟩)
          + (C a * X + C b) * ((G.get i₂).get ⟨j₂, by
            simp_all⟩))) :=
  ⟨matrix_preserves_interlacing_seq0_nonneg_entries (n := n) G hG_rect hpres0,
    fun i₁ i₂ j₁ j₂ hi hj _a _b ha hb =>
      matrix_preserves_interlacing_seq0_sparse_pair_prec0
        (n := n) G hG_rect hpres0 i₁ i₂ j₁ j₂ hi hj ha hb⟩


end RealRooted
