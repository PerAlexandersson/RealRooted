import RealRooted.RowThreshold
import RealRooted.AffineProperPosition
import RealRooted.PFPolynomial
import RealRooted.StaircaseSum

/-!
# Generic threshold matrices

Reusable row-threshold entries, matrices, preservation theorems, and the
small polynomial lemmas shared by the Haglund--Zhang and Gustafsson--Solus
applications.
-/

open Polynomial

noncomputable section

namespace RealRooted

@[simp] lemma length_matPolyAction (G : List (List ℝ[X])) (fs : List ℝ[X]) :
    (matPolyAction G fs).length = G.length := by
  simp [matPolyAction]

/-! ## Generic threshold rows -/

/-- A threshold entry: `X` before the threshold, the marker `α` at the
threshold, and `1` after it. -/
def thresholdEntry (t : ℕ) (α : ℝ[X]) (j : ℕ) : ℝ[X] :=
  if j < t then X else if j = t then α else 1

lemma thresholdEntry_of_lt {t j : ℕ} (α : ℝ[X]) (h : j < t) :
    thresholdEntry t α j = X := by
  simp [thresholdEntry, h]

@[simp] lemma thresholdEntry_self (t : ℕ) (α : ℝ[X]) :
    thresholdEntry t α t = α := by
  simp [thresholdEntry]

lemma thresholdEntry_of_gt {t j : ℕ} (α : ℝ[X]) (h : t < j) :
    thresholdEntry t α j = 1 := by
  have hlt : ¬ j < t := by lia
  have hne : ¬ j = t := by lia
  simp [thresholdEntry, hlt, hne]

/-- The linear form `1 + X` has nonnegative coefficients. -/
lemma isNonnegLinearForm_one_add_X : IsNonnegLinearForm (1 + X : ℝ[X]) :=
  ⟨1, 1, by norm_num, by norm_num, by simp⟩

lemma thresholdEntry_hasNonnegCoeffs {t : ℕ} {α : ℝ[X]} (j : ℕ)
    (hα : HasNonnegCoeffs α) :
    HasNonnegCoeffs (thresholdEntry t α j) := by
  unfold thresholdEntry
  split_ifs
  · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_X
  · exact hα
  · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one

/-- A threshold row of width `q` with threshold `t` and marker `α`. -/
def thresholdRow (q t : ℕ) (α : ℝ[X]) : List ℝ[X] :=
  (List.range q).map (thresholdEntry t α)

@[simp] lemma length_thresholdRow (q t : ℕ) (α : ℝ[X]) :
    (thresholdRow q t α).length = q := by
  simp [thresholdRow]

lemma getElem_thresholdRow {q t : ℕ} {α : ℝ[X]} {j : ℕ}
    (hj : j < (thresholdRow q t α).length) :
    (thresholdRow q t α)[j] = thresholdEntry t α j := by
  simp only [thresholdRow, List.getElem_map, List.getElem_range]

lemma get_thresholdRow {q t : ℕ} {α : ℝ[X]}
    (j : Fin (thresholdRow q t α).length) :
    (thresholdRow q t α).get j = thresholdEntry t α j.1 := by
  simp only [List.get_eq_getElem]
  exact getElem_thresholdRow j.2

/-- A matrix built from threshold rows, encoded as `(threshold, marker)` data. -/
def thresholdMatrix (q : ℕ) (rows : List (ℕ × ℝ[X])) : List (List ℝ[X]) :=
  rows.map (fun p => thresholdRow q p.1 p.2)

@[simp] lemma length_thresholdMatrix (q : ℕ) (rows : List (ℕ × ℝ[X])) :
    (thresholdMatrix q rows).length = rows.length := by
  simp [thresholdMatrix]

lemma get_thresholdMatrix {q : ℕ} {rows : List (ℕ × ℝ[X])}
    (i : Fin (thresholdMatrix q rows).length) :
    (thresholdMatrix q rows).get i =
      thresholdRow q
        (rows.get ⟨i.1, by simpa using i.2⟩).1
        (rows.get ⟨i.1, by simpa using i.2⟩).2 := by
  simp only [thresholdMatrix, List.get_eq_getElem, List.getElem_map]

lemma mem_thresholdMatrix_length {q : ℕ} {rows : List (ℕ × ℝ[X])}
    (row : List ℝ[X]) (h : row ∈ thresholdMatrix q rows) :
    row.length = q := by
  simp only [thresholdMatrix, List.mem_map] at h
  obtain ⟨p, _, rfl⟩ := h
  simp

lemma thresholdMatrix_nonneg {q : ℕ} {rows : List (ℕ × ℝ[X])}
    (hα : ∀ p ∈ rows, HasNonnegCoeffs p.2) :
    ∀ row ∈ thresholdMatrix q rows, ∀ p ∈ row, HasNonnegCoeffs p := by
  intro row hrow p hp
  simp only [thresholdMatrix, List.mem_map] at hrow
  obtain ⟨r, hr_mem, rfl⟩ := hrow
  simp only [thresholdRow, List.mem_map] at hp
  obtain ⟨j, _, rfl⟩ := hp
  exact thresholdEntry_hasNonnegCoeffs j (hα r hr_mem)

lemma get_get_thresholdMatrix {q : ℕ} {rows : List (ℕ × ℝ[X])}
    (i : Fin (thresholdMatrix q rows).length) (j : Fin q) :
    ((thresholdMatrix q rows).get i).get
        ⟨j.1, by rw [get_thresholdMatrix]; simp⟩ =
      thresholdEntry
        (rows.get ⟨i.1, by simpa using i.2⟩).1
        (rows.get ⟨i.1, by simpa using i.2⟩).2 j.1 := by
  simp only [List.get_eq_getElem, thresholdMatrix, List.getElem_map,
    thresholdRow, List.getElem_range]

lemma thresholdMatrix_has2x2_of_entry
    {q : ℕ} {rows : List (ℕ × ℝ[X])}
    (hentry : ∀ (i₁ i₂ : Fin rows.length) (j₁ j₂ : Fin q),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (thresholdEntry (rows.get i₁).1 (rows.get i₁).2 j₁.1)
        (thresholdEntry (rows.get i₁).1 (rows.get i₁).2 j₂.1)
        (thresholdEntry (rows.get i₂).1 (rows.get i₂).2 j₁.1)
        (thresholdEntry (rows.get i₂).1 (rows.get i₂).2 j₂.1)) :
    ∀ (i₁ i₂ : Fin (thresholdMatrix q rows).length) (j₁ j₂ : Fin q),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (((thresholdMatrix q rows).get i₁).get ⟨j₁.1, by rw [get_thresholdMatrix]; simp⟩)
        (((thresholdMatrix q rows).get i₁).get ⟨j₂.1, by rw [get_thresholdMatrix]; simp⟩)
        (((thresholdMatrix q rows).get i₂).get ⟨j₁.1, by rw [get_thresholdMatrix]; simp⟩)
        (((thresholdMatrix q rows).get i₂).get
          ⟨j₂.1, by rw [get_thresholdMatrix]; simp⟩) := by
  intro i₁ i₂ j₁ j₂ hi hj
  let i₁' : Fin rows.length := ⟨i₁.1, by simpa using i₁.2⟩
  let i₂' : Fin rows.length := ⟨i₂.1, by simpa using i₂.2⟩
  have hi' : i₁' ≤ i₂' := hi
  have h := hentry i₁' i₂' j₁ j₂ hi' hj
  dsimp [i₁', i₂'] at h
  rw [get_get_thresholdMatrix, get_get_thresholdMatrix,
    get_get_thresholdMatrix, get_get_thresholdMatrix]
  exact h

theorem thresholdMatrix_preserves_interlacing_seq0_of_entry
    {q : ℕ} (rows : List (ℕ × ℝ[X]))
    (hα : ∀ p ∈ rows, HasNonnegCoeffs p.2)
    (hentry : ∀ (i₁ i₂ : Fin rows.length) (j₁ j₂ : Fin q),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (thresholdEntry (rows.get i₁).1 (rows.get i₁).2 j₁.1)
        (thresholdEntry (rows.get i₁).1 (rows.get i₁).2 j₂.1)
        (thresholdEntry (rows.get i₂).1 (rows.get i₂).2 j₁.1)
        (thresholdEntry (rows.get i₂).1 (rows.get i₂).2 j₂.1))
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (thresholdMatrix q rows) fs) :=
  matrix_preserves_interlacing_seq0_of_2x2
    (thresholdMatrix q rows)
    (fun row hrow => mem_thresholdMatrix_length row hrow)
    (thresholdMatrix_nonneg hα)
    (thresholdMatrix_has2x2_of_entry hentry)
    fs hfs_len hfs

theorem thresholdMatrix_preserves_interlacing_seq0_of_entry_weak
    {q : ℕ} (rows : List (ℕ × ℝ[X]))
    (hα : ∀ p ∈ rows, HasNonnegCoeffs p.2)
    (hentry : ∀ (i₁ i₂ : Fin rows.length) (j₁ j₂ : Fin q),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (thresholdEntry (rows.get i₁).1 (rows.get i₁).2 j₁.1)
        (thresholdEntry (rows.get i₁).1 (rows.get i₁).2 j₂.1)
        (thresholdEntry (rows.get i₂).1 (rows.get i₂).2 j₁.1)
        (thresholdEntry (rows.get i₂).1 (rows.get i₂).2 j₂.1))
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (thresholdMatrix q rows) fs) ∧
      ∀ f ∈ matPolyAction (thresholdMatrix q rows) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  matrix_preserves_interlacing_seq0_of_2x2_weak
    (thresholdMatrix q rows)
    (fun row hrow => mem_thresholdMatrix_length row hrow)
    (thresholdMatrix_nonneg hα)
    (thresholdMatrix_has2x2_of_entry hentry)
    fs hfs_len hfs hfs_real

lemma weakData_of_isInterlacingSeqNonneg {fs : List ℝ[X]}
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg fs ∧
      ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  ⟨⟨hfs.2.toIsInterlacingSeq0, fun f hf => hfs.nonnegCoeffs f hf⟩,
    fun f hf _ => hfs.realRooted f hf⟩

theorem isRealRooted_sum_of_isInterlacingSeq0Nonneg
    {fs : List ℝ[X]}
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hsum_ne : fs.sum ≠ 0) :
    fs.sum ≠ 0 ∧ fs.sum.Splits := by
  have hstrict : IsInterlacingSeqNonneg (fs.filter (· ≠ 0)) :=
    hfs.filter_ne_zero_of_realRooted hfs_real
  have hfilter_ne : fs.filter (· ≠ 0) ≠ [] := by
    intro hnil
    have hsum_filter : (fs.filter (· ≠ 0)).sum = fs.sum := sum_filter_ne_zero fs
    have hsum_zero : (fs.filter (· ≠ 0)).sum = 0 := by simpa using congrArg List.sum hnil
    apply hsum_ne
    exact hsum_filter.symm.trans hsum_zero
  have hlen_pos : 0 < (fs.filter (· ≠ 0)).length := by
    cases hfilter : fs.filter (· ≠ 0) with
    | nil => exact False.elim (hfilter_ne hfilter)
    | cons _ _ => simp
  have hsum_rr :=
    isRealRooted_staircaseSum_of_isInterlacingSeqNonneg
      (fs := fs.filter (· ≠ 0)) (m := 0) hstrict hlen_pos
  have hsum_rr' :
      (fs.filter (· ≠ 0)).sum ≠ 0 ∧ (fs.filter (· ≠ 0)).sum.Splits := by
    simpa [staircaseSum] using hsum_rr
  rw [← sum_filter_ne_zero fs]
  exact hsum_rr'

/-! ## Finite-entry shape helpers -/

/-- Reflexivity of `Prec0` on a nonzero real-rooted polynomial. -/
theorem prec0_refl_of_realRooted {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) :
    Prec0 p p :=
  (prec_refl hp.1 hp.2).toPrec0

/-- A positive affine form precedes the `X`-multiple of another one under the
cross inequality. -/
theorem prec0_affine_to_X_mul_affine
    {u v U V : ℝ}
    (hu : 0 < u) (hU : 0 < U) (hcross : u * V ≤ U * v)
    (hv : 0 ≤ v) (hV : 0 ≤ V) :
    Prec0 (C U * X + C V) (X * (C u * X + C v)) :=
  (prec_to_prec_mul_X_of_nonneg
    (prec_affine_linear_affine_linear_of_cross hu hU hcross)
    (hasNonnegCoeffs_affine_linear hu.le hv)
    (hasNonnegCoeffs_affine_linear hU.le hV)).toPrec0

def Threshold2x2EntryTuple
    (a b c d A B C D : ℝ[X]) : Prop :=
  a = A ∧ b = B ∧ c = C ∧ d = D

end RealRooted
