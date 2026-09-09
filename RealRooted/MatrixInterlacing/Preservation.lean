import RealRooted.MatrixInterlacing.Action
import RealRooted.MatrixInterlacing.AffinePair

open Polynomial

noncomputable section

namespace RealRooted

/-! ## Main characterization theorem -/

/-- **Forward direction**: If `n > 0`, `G` has non-negative coefficients, and
    Brändén's affine condition holds for all row/column choices (including the
    boundary cases with repeated indices), then `G` maps `𝓕ₙ⁺ → 𝓕ₘ⁺`. -/
theorem matrix_preserves_interlacing_seq
    (hn : 0 < n)
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (fs : List ℝ[X]) (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeqNonneg (matPolyAction G fs) := by
  /-
  Handbook proof structure (Brändén, §7.8, Theorem 7.8.5):

  For fixed output rows `i < j`, one considers, for each `s, t > 0`, the
  auxiliary column sequence

    h_k := ((C s * X + C t) * G[i,k]) + G[j,k].

  The affine matrix hypothesis is exactly what makes `(h_k)` an interlacing
  sequence. The non-strict index form is also what supplies the boundary cases
  needed to recover elementwise real-rootedness of the image when `m = 1` or
  `n = 1`.
  Then

    ((C s * X + C t) * (matPolyAction G fs).get i) + (matPolyAction G fs).get j
      = ∑ h_k * fs_k

  is real-rooted by Brändén's Lemma 7.8.3: the reversed product-sum of an
  interlacing sequence with an interlacing sequence of non-negative-coefficient
  polynomials is real-rooted. The remaining local gap is to package that
  Lemma 7.8.3 in this codebase and then route the affine family back to `Prec`
  through the already-developed affine-family machinery above.
  -/
  rcases hfs with ⟨hfs_mem, hfs_int⟩
  have hfs_nonneg : ∀ q ∈ fs, HasNonnegCoeffs q :=
    fun q hq => (hfs_mem q hq).2
  let j0 : Fin n := ⟨0, hn⟩
  have hentry_head_ne (iG : Fin G.length) :
      (G.get iG).get ⟨0, by
        simp_all⟩ ≠ 0 := by
    have hdiag :
        Has2x2InterlacingProperty
          ((G.get iG).get ⟨j0, by simp_all⟩)
          ((G.get iG).get ⟨j0, by simp_all⟩)
          ((G.get iG).get ⟨j0, by simp_all⟩)
          ((G.get iG).get ⟨j0, by simp_all⟩) := by
      simp_all
    exact
      ne_zero_of_self_2x2
        ((G.get iG).get ⟨j0, by lia⟩)
        hdiag
  constructor
  · intro p hp
    rcases List.mem_map.mp hp with ⟨row, hrow_mem, rfl⟩
    have hrow_nonneg_sum :
        HasNonnegCoeffs ((row.zipWith (· * ·) fs).sum) :=
      hasNonnegCoeffs_zipWith_mul_sum (hG_nonneg row hrow_mem) hfs_nonneg
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hrow_mem
    let iG : Fin G.length := ⟨i, by lia⟩
    have hself :
        Prec (((G.get iG).zipWith (· * ·) fs).sum) (((G.get iG).zipWith (· * ·) fs).sum) :=
      prec_zipWith_sum_pair_of_2x2
        (n := n)
        (hn := hn)
        (row₁ := G.get iG)
        (row₂ := G.get iG)
        (fs := fs)
        (hrow₁_len := hG_rect _ (G.get_mem iG))
        (hrow₂_len := hG_rect _ (G.get_mem iG))
        (hrow₁_head_ne := hentry_head_ne iG)
        (hrow₂_head_ne := hentry_head_ne iG)
        (hrow₁_nonneg := hG_nonneg _ (G.get_mem iG))
        (hrow₂_nonneg := hG_nonneg _ (G.get_mem iG))
        (h2x2 := fun j₁ j₂ hj =>
          hG_affine iG iG j₁ j₂ le_rfl hj)
        (hfs_len := hfs_len)
        (hfs := ⟨hfs_mem, hfs_int⟩)
    exact ⟨hself.1, hrow_nonneg_sum⟩
  · rw [isInterlacingSeq_iff_pairwise]
    refine List.pairwise_iff_get.2 ?_
    intro i j hij
    let iG : Fin G.length := ⟨i, by simpa [matPolyAction] using i.2⟩
    let jG : Fin G.length := ⟨j, by simpa [matPolyAction] using j.2⟩
    have hpair :
        Prec (((G.get iG).zipWith (· * ·) fs).sum) (((G.get jG).zipWith (· * ·) fs).sum) :=
      prec_zipWith_sum_pair_of_2x2
        (n := n)
        (hn := hn)
        (row₁ := G.get iG)
        (row₂ := G.get jG)
        (fs := fs)
        (hrow₁_len := hG_rect _ (G.get_mem iG))
        (hrow₂_len := hG_rect _ (G.get_mem jG))
        (hrow₁_head_ne := hentry_head_ne iG)
        (hrow₂_head_ne := hentry_head_ne jG)
        (hrow₁_nonneg := hG_nonneg _ (G.get_mem iG))
        (hrow₂_nonneg := hG_nonneg _ (G.get_mem jG))
        (h2x2 := fun j₁ j₂ hj ↦
          hG_affine iG jG j₁ j₂ (by grind) hj)
        (hfs_len := hfs_len)
        (hfs := ⟨hfs_mem, hfs_int⟩)
    simpa [matPolyAction, iG, jG] using hpair

/-- **Weak zero-aware forward direction**: if `G` has non-negative coefficients
and satisfies the weak affine 2×2 condition `Has2x2InterlacingProperty0`, then
it maps strict nonnegative interlacing input sequences to weak zero-aware
nonnegative interlacing output sequences. The weak codomain is what makes zero
output rows harmless. -/
theorem matrix_preserves_interlacing_seq0_of_2x2
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (fs : List ℝ[X]) (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) := by
  rcases hfs with ⟨hfs_mem, hfs_int⟩
  have hfs_nonneg : ∀ q ∈ fs, HasNonnegCoeffs q :=
    fun q hq => (hfs_mem q hq).2
  refine ⟨?_, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise]
    refine List.pairwise_iff_get.2 ?_
    intro i j hij
    let iG : Fin G.length := ⟨i, by simpa [matPolyAction] using i.2⟩
    let jG : Fin G.length := ⟨j, by simpa [matPolyAction] using j.2⟩
    have hpair :
        Prec0 (((G.get iG).zipWith (· * ·) fs).sum)
          (((G.get jG).zipWith (· * ·) fs).sum) :=
      prec0_zipWith_sum_pair_of_2x2
        (n := n)
        (row₁ := G.get iG)
        (row₂ := G.get jG)
        (fs := fs)
        (hrow₁_len := hG_rect _ (G.get_mem iG))
        (hrow₂_len := hG_rect _ (G.get_mem jG))
        (hrow₁_nonneg := hG_nonneg _ (G.get_mem iG))
        (hrow₂_nonneg := hG_nonneg _ (G.get_mem jG))
        (h2x2 := fun j₁ j₂ hj ↦
          hG_affine iG jG j₁ j₂ (by grind) hj)
        (hfs_len := hfs_len)
        (hfs := ⟨hfs_mem, hfs_int⟩)
    simpa [matPolyAction, iG, jG] using hpair
  · intro p hp
    rcases List.mem_map.mp hp with ⟨row, hrow_mem, rfl⟩
    exact
      hasNonnegCoeffs_zipWith_mul_sum
        (hG_nonneg row hrow_mem)
        hfs_nonneg

/-- Weak zero-aware forward direction with zero-aware input.  The extra
conclusion records that each nonzero output entry is real-rooted, so this
statement can be iterated. -/
theorem matrix_preserves_interlacing_seq0_of_2x2_weak
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (fs : List ℝ[X]) (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) ∧
      ∀ f ∈ matPolyAction G fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [isInterlacingSeq0_iff_pairwise]
      refine List.pairwise_iff_get.2 ?_
      intro i j hij
      let iG : Fin G.length := ⟨i, by simpa [matPolyAction] using i.2⟩
      let jG : Fin G.length := ⟨j, by simpa [matPolyAction] using j.2⟩
      have hpair :
          Prec0 (((G.get iG).zipWith (· * ·) fs).sum)
            (((G.get jG).zipWith (· * ·) fs).sum) :=
        prec0_zipWith_sum_pair_of_2x2_weak
          (n := n)
          (row₁ := G.get iG)
          (row₂ := G.get jG)
          (fs := fs)
          (hrow₁_len := hG_rect _ (G.get_mem iG))
          (hrow₂_len := hG_rect _ (G.get_mem jG))
          (hrow₁_nonneg := hG_nonneg _ (G.get_mem iG))
          (hrow₂_nonneg := hG_nonneg _ (G.get_mem jG))
          (h2x2 := fun j₁ j₂ hj ↦
            hG_affine iG jG j₁ j₂ (by grind) hj)
          (hfs_len := hfs_len)
          (hfs := hfs)
          (hfs_real := hfs_real)
      simpa [matPolyAction, iG, jG] using hpair
    · intro p hp
      rcases List.mem_map.mp hp with ⟨row, hrow_mem, rfl⟩
      exact
        hasNonnegCoeffs_zipWith_mul_sum
          (hG_nonneg row hrow_mem)
          hfs.2
  · intro p hp hp0
    rcases List.mem_map.mp hp with ⟨row, hrow_mem, hp_eq⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 hrow_mem
    let iG : Fin G.length := i
    have hsum_eq_p : ((G.get iG).zipWith (· * ·) fs).sum = p := by lia
    have hself0 :
        Prec0 (((G.get iG).zipWith (· * ·) fs).sum)
          (((G.get iG).zipWith (· * ·) fs).sum) :=
      prec0_zipWith_sum_pair_of_2x2_weak
        (n := n)
        (row₁ := G.get iG)
        (row₂ := G.get iG)
        (fs := fs)
        (hrow₁_len := hG_rect _ (G.get_mem iG))
        (hrow₂_len := hG_rect _ (G.get_mem iG))
        (hrow₁_nonneg := hG_nonneg _ (G.get_mem iG))
        (hrow₂_nonneg := hG_nonneg _ (G.get_mem iG))
        (h2x2 := fun j₁ j₂ hj => hG_affine iG iG j₁ j₂ le_rfl hj)
        (hfs_len := hfs_len)
        (hfs := hfs)
        (hfs_real := hfs_real)
    have hp0' : ((G.get iG).zipWith (· * ·) fs).sum ≠ 0 := by lia
    simpa [← hsum_eq_p] using (hself0.toPrec_of_ne hp0' hp0').1

/-- Weak zero-aware forward direction with strict input, retaining the fact that
each nonzero output entry is real-rooted.  This is the form used when a matrix
step should be followed by another weak matrix step or by a scalar projection. -/
theorem matrix_preserves_interlacing_seq0_of_2x2_realRooted
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (fs : List ℝ[X]) (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction G fs) ∧
      ∀ f ∈ matPolyAction G fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  matrix_preserves_interlacing_seq0_of_2x2_weak
    G hG_rect hG_nonneg hG_affine fs hfs_len
    hfs.toIsInterlacingSeq0Nonneg (fun f hf _hne => hfs.realRooted f hf)

/-- Strict-output form of the weak matrix theorem with zero-aware input,
obtained by discarding zero output entries. -/
theorem matrix_preserves_interlacing_seq0_filter_ne_zero_of_2x2_weak
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (fs : List ℝ[X]) (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeqNonneg ((matPolyAction G fs).filter (· ≠ 0)) := by
  have h := matrix_preserves_interlacing_seq0_of_2x2_weak
    G hG_rect hG_nonneg hG_affine fs hfs_len hfs hfs_real
  exact h.1.filter_ne_zero_of_realRooted h.2

/-- Strict-output form of the weak matrix theorem, obtained by discarding zero
output entries. -/
theorem matrix_preserves_interlacing_seq0_filter_ne_zero_of_2x2
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hG_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p)
    (hG_affine : ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        ((G.get i₁).get ⟨j₁, by simp_all⟩)
        ((G.get i₁).get ⟨j₂, by simp_all⟩)
        ((G.get i₂).get ⟨j₁, by simp_all⟩)
        ((G.get i₂).get ⟨j₂, by simp_all⟩))
    (fs : List ℝ[X]) (hfs_len : fs.length = n)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeqNonneg ((matPolyAction G fs).filter (· ≠ 0)) := by
  have h := matrix_preserves_interlacing_seq0_of_2x2_realRooted
    G hG_rect hG_nonneg hG_affine fs hfs_len hfs
  exact h.1.filter_ne_zero_of_realRooted h.2


end RealRooted
