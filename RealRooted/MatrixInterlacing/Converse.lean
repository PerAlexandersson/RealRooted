import RealRooted.MatrixInterlacing.Preservation
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

theorem matrix_preserves_interlacing_seq0_sparse_pair_interl
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hpres0 : ∀ (fs : List ℝ[X]), fs.length = n → IsInterlacingSeq0Nonneg fs →
      IsInterlacingSeq0Nonneg (matPolyAction G fs))
    (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n)
    (hi : i₁ < i₂) (hj : j₁ < j₂)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Interl
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
  have hpair : Interl ((matPolyAction G fs).get iG) ((matPolyAction G fs).get jG) :=
    himage.1.interl (i := iG) (j := jG) (by grind)
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
sparse test images satisfy the corresponding weak `Interl` relation. -/
theorem matrix_preserves_interlacing_seq0_necessary_conditions
    (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n)
    (hpres0 : ∀ (fs : List ℝ[X]), fs.length = n → IsInterlacingSeq0Nonneg fs →
      IsInterlacingSeq0Nonneg (matPolyAction G fs)) :
    (∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p) ∧
    (∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n),
      i₁ < i₂ → j₁ < j₂ →
      ∀ {a b : ℝ}, 0 < a → 0 < b →
      Interl
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
      matrix_preserves_interlacing_seq0_sparse_pair_interl
        (n := n) G hG_rect hpres0 i₁ i₂ j₁ j₂ hi hj ha hb⟩

/-! ## Exact characterization for the zero-aware real-rooted family -/

/-- If two splitting polynomials with nonnegative coefficients interlace in the
zero-aware sense, then every positive affine combination `(s X + t) f + g`
splits. -/
theorem Interl.splits_affine_combo_of_nonneg {f g : ℝ[X]} (hfg : Interl f g)
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g) (hf_split : f.Splits)
    (hg_split : g.Splits) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ((C s * X + C t) * f + g).Splits := by
  rcases hfg with rfl | rfl | hfg
  · simpa using hg_split
  · simpa using (isRealRooted_affine_factor (t := t) hs).2.mul hf_split
  · exact (isRealRooted_affine_combo_of_strictInterl_nonneg hfg hf hg hs ht).2

/-- Zero-aware form of the affine-family criterion (Brändén, Theorem 7.8.4):
if `f` and `g` have nonnegative coefficients and `(s X + t) f + g` splits for all
`s, t > 0`, then `f` and `g` interlace. -/
theorem interl_of_forall_splits_affine_combo {f g : ℝ[X]}
    (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (h : ∀ s t : ℝ, 0 < s → 0 < t → ((C s * X + C t) * f + g).Splits) :
    Interl f g := by
  by_cases hf0 : f = 0
  · exact Or.inl hf0
  by_cases hg0 : g = 0
  · exact Or.inr (Or.inl hg0)
  refine (strictInterl_of_affine_family_nonneg hf0 hg0 hf hg
    fun {s t} hs ht => ⟨?_, h s t hs ht⟩).toInterl
  exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
    ((hasNonnegCoeffs_affine_linear hs.le ht.le).mul hf) hg hg0

/-- Every member of a zero-aware real-rooted interlacing sequence splits. -/
lemma IsInterlacingSeq0NonnegRealRooted.splits_of_mem {fs : List ℝ[X]}
    (hfs : IsInterlacingSeq0NonnegRealRooted fs) {f : ℝ[X]} (hf : f ∈ fs) :
    f.Splits := by
  by_cases hf0 : f = 0
  · exact hf0 ▸ Splits.zero
  · exact hfs.splits hf hf0

/-- Members `i ≤ j` of a zero-aware real-rooted interlacing sequence interlace;
the diagonal case holds because nonzero members split. -/
lemma IsInterlacingSeq0NonnegRealRooted.interl_of_le {fs : List ℝ[X]}
    (hfs : IsInterlacingSeq0NonnegRealRooted fs) {i j : Fin fs.length} (hij : i ≤ j) :
    Interl (fs.get i) (fs.get j) := by
  rcases hij.lt_or_eq with hij | rfl
  · exact hfs.1.1.interl hij
  · exact Interl.refl fun _ => hfs.splits_of_mem (List.get_mem _ _)

/-- A polynomial matrix `G` with `n` columns preserves the zero-aware
nonnegative real-rooted interlacing family: it maps every sequence of length
`n` in `IsInterlacingSeq0NonnegRealRooted` into the same family. -/
def PreservesInterlacingSeq0 (n : ℕ) (G : List (List ℝ[X])) : Prop :=
  ∀ fs : List ℝ[X], fs.length = n → IsInterlacingSeq0NonnegRealRooted fs →
    IsInterlacingSeq0NonnegRealRooted (matPolyAction G fs)

namespace PreservesInterlacingSeq0

variable {n : ℕ} {G : List (List ℝ[X])}

/-- Rows `i₁ ≤ i₂` of the image of a test sequence interlace and split. -/
private lemma interl_rowSum (hG : PreservesInterlacingSeq0 n G) {fs : List ℝ[X]}
    (hfs_len : fs.length = n) (hfs : IsInterlacingSeq0NonnegRealRooted fs)
    {i₁ i₂ : Fin G.length} (hi : i₁ ≤ i₂) :
    Interl ((G.get i₁).zipWith (· * ·) fs).sum ((G.get i₂).zipWith (· * ·) fs).sum ∧
      ((G.get i₁).zipWith (· * ·) fs).sum.Splits ∧
      ((G.get i₂).zipWith (· * ·) fs).sum.Splits := by
  have hout := hG fs hfs_len hfs
  rw [← get_matPolyAction, ← get_matPolyAction]
  exact ⟨hout.interl_of_le (i := ⟨i₁, by simp⟩) (j := ⟨i₂, by simp⟩) hi,
    hout.splits_of_mem (List.get_mem _ _), hout.splits_of_mem (List.get_mem _ _)⟩

/-- A matrix preserving the zero-aware real-rooted family has entrywise
nonnegative coefficients; the single-support test sequences detect each
entry. -/
theorem hasNonnegCoeffs (hG : PreservesInterlacingSeq0 n G)
    (hG_rect : ∀ row ∈ G, row.length = n) :
    ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p := fun row hrow p hp => by
  obtain ⟨j, rfl⟩ := List.mem_iff_get.1 hp
  have hrow_len := hG_rect row hrow
  let fs := oneSupportSeq n ⟨j, j.isLt.trans_eq hrow_len⟩
  have hout := hG fs (by simp [fs]) (isInterlacingSeq0NonnegRealRooted_oneSupportSeq _)
  have hmem : (row.zipWith (· * ·) fs).sum ∈ matPolyAction G fs :=
    List.mem_map.2 ⟨row, hrow, rfl⟩
  simpa [fs, zipWith_mul_oneSupportSeq_sum_eq_get_of_length row hrow_len] using
    hout.nonnegCoeffs _ hmem

/-- A matrix preserving the zero-aware real-rooted family satisfies the weak
affine 2×2 condition on every ordered submatrix.  Sparse test sequences
`(1 at j₁, s' X + t' at j₂)` give interlacing image rows; the affine-family
criterion turns them into the condition. -/
theorem has2x2InterlacingProperty0 (hG : PreservesInterlacingSeq0 n G)
    (hG_rect : ∀ row ∈ G, row.length = n)
    (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n) (hi : i₁ ≤ i₂) (hj : j₁ ≤ j₂) :
    Has2x2InterlacingProperty0
      ((G.get i₁).get ⟨j₁, by simp_all⟩)
      ((G.get i₁).get ⟨j₂, by simp_all⟩)
      ((G.get i₂).get ⟨j₁, by simp_all⟩)
      ((G.get i₂).get ⟨j₂, by simp_all⟩) := by
  have hnn (i : Fin G.length) (j : Fin n) :
      HasNonnegCoeffs ((G.get i).get ⟨j, by simp_all⟩) :=
    hG.hasNonnegCoeffs hG_rect _ (List.get_mem _ _) _ (List.get_mem _ _)
  have hℓ {s t : ℝ} (hs : 0 < s) (ht : 0 < t) := hasNonnegCoeffs_affine_linear hs.le ht.le
  intro s t hs ht
  rcases hj.lt_or_eq with hj | rfl
  · have e (i : Fin G.length) (s' t' : ℝ) :
        ((G.get i).zipWith (· * ·) (sparseLinearPairSeq n j₁ j₂ s' t')).sum =
          (G.get i).get ⟨j₁, by simp_all⟩
            + (C s' * X + C t') * (G.get i).get ⟨j₂, by simp_all⟩ :=
      zipWith_mul_sparseLinearPairSeq_sum_eq_of_length _ (hG_rect _ (List.get_mem _ _))
        j₁ j₂ hj.ne s' t'
    refine interl_of_forall_splits_affine_combo (((hℓ hs ht).mul (hnn i₁ j₂)).add (hnn i₂ j₂))
      (((hℓ hs ht).mul (hnn i₁ j₁)).add (hnn i₂ j₁)) fun s' t' hs' ht' => ?_
    obtain ⟨hint, hsplit₁, hsplit₂⟩ := hG.interl_rowSum (by simp)
      (isInterlacingSeq0NonnegRealRooted_sparseLinearPairSeq hj hs' ht') hi
    rw [e, e] at hint
    rw [e] at hsplit₁ hsplit₂
    convert hint.splits_affine_combo_of_nonneg
      ((hnn i₁ j₁).add ((hℓ hs' ht').mul (hnn i₁ j₂)))
      ((hnn i₂ j₁).add ((hℓ hs' ht').mul (hnn i₂ j₂))) hsplit₁ hsplit₂ hs ht using 1
    ring
  · have e (i : Fin G.length) :
        ((G.get i).zipWith (· * ·) (oneSupportSeq n j₁)).sum =
          (G.get i).get ⟨j₁, by simp_all⟩ :=
      zipWith_mul_oneSupportSeq_sum_eq_get_of_length _ (hG_rect _ (List.get_mem _ _)) j₁
    obtain ⟨hint, hsplit₁, hsplit₂⟩ := hG.interl_rowSum (by simp)
      (isInterlacingSeq0NonnegRealRooted_oneSupportSeq j₁) hi
    rw [e, e] at hint
    rw [e] at hsplit₁ hsplit₂
    exact Interl.refl fun _ =>
      hint.splits_affine_combo_of_nonneg (hnn i₁ j₁) (hnn i₂ j₁) hsplit₁ hsplit₂ hs ht

end PreservesInterlacingSeq0

/-- **Matrices preserving zero-aware interlacing** (Brändén, Handbook of
Enumerative Combinatorics, Theorem 7.8.5, zero-aware form).  A polynomial
matrix `G` with `n` columns maps the zero-aware nonnegative real-rooted
interlacing family of length `n` into itself if and only if its entries have
nonnegative coefficients and every ordered 2×2 submatrix, rows `i₁ ≤ i₂` and
columns `j₁ ≤ j₂`, satisfies `Has2x2InterlacingProperty0`. -/
theorem preservesInterlacingSeq0_iff {n : ℕ} (G : List (List ℝ[X]))
    (hG_rect : ∀ row ∈ G, row.length = n) :
    PreservesInterlacingSeq0 n G ↔
      (∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p) ∧
      ∀ (i₁ i₂ : Fin G.length) (j₁ j₂ : Fin n), i₁ ≤ i₂ → j₁ ≤ j₂ →
        Has2x2InterlacingProperty0
          ((G.get i₁).get ⟨j₁, by simp_all⟩)
          ((G.get i₁).get ⟨j₂, by simp_all⟩)
          ((G.get i₂).get ⟨j₁, by simp_all⟩)
          ((G.get i₂).get ⟨j₂, by simp_all⟩) :=
  ⟨fun hG => ⟨hG.hasNonnegCoeffs hG_rect, hG.has2x2InterlacingProperty0 hG_rect⟩,
    fun ⟨hnn, h2x2⟩ fs hfs_len hfs =>
      matrix_preserves_interlacing_seq0_of_2x2_weak G hG_rect hnn h2x2 fs hfs_len hfs.1 hfs.2⟩

end RealRooted
