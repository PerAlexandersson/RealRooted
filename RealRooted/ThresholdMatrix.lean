import RealRooted.RowThreshold
import RealRooted.StaircaseSum
import RealRooted.VeroneseMatrix

/-!
# Threshold matrices

This module packages the common row-threshold matrix shape behind two backlog
items:

* Gustafsson--Solus Lemma 3.4, where the diagonal marker is `0` or `1`;
* Haglund--Zhang's refined `s`-inversion interlacing recursion, where the
  diagonal marker is `1` or `1 + X`.

The matrix plumbing is proved here.  Both finite entrywise `2 x 2` checks are
proved by finite threshold-shape classifications.  The parameterized backend
theorems are kept as reducer interfaces; direct wrappers apply the checked
finite lemmas.
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

private lemma weakData_of_isInterlacingSeqNonneg {fs : List ℝ[X]}
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

private lemma prec0_refl_of_isRealRooted {p : ℝ[X]} (hp : p ≠ 0 ∧ p.Splits) :
    Prec0 p p :=
  (prec_refl hp.1 hp.2).toPrec0

private lemma prec0_affine_to_X_mul_affine_of_cross
    {u v U V : ℝ}
    (hu : 0 < u) (hU : 0 < U) (hcross : u * V ≤ U * v)
    (hv : 0 ≤ v) (hV : 0 ≤ V) :
    Prec0 (C U * X + C V) (X * (C u * X + C v)) :=
  (prec_to_prec_mul_X_of_nonneg
    (prec_affine_linear_affine_linear_of_cross hu hU hcross)
    (hasNonnegCoeffs_affine_linear hu.le hv)
    (hasNonnegCoeffs_affine_linear hU.le hV)).toPrec0

private def Threshold2x2EntryTuple
    (a b c d A B C D : ℝ[X]) : Prop :=
  a = A ∧ b = B ∧ c = C ∧ d = D

private lemma prec0_add_left_of_common_right_of_nonneg {p q r : ℝ[X]}
    (hp : Prec0 p r) (hq : Prec0 q r)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q) :
    Prec0 (p + q) r := by
  by_cases hp0 : p = 0
  · simpa [hp0] using hq
  by_cases hq0 : q = 0
  · simpa [hq0] using hp
  by_cases hr0 : r = 0
  · simpa [hr0] using prec0_zero_right (p + q)
  rcases hp with hpz | hrz | hpstr
  · contradiction
  · contradiction
  rcases hq with hqz | hrz | hqstr
  · contradiction
  · contradiction
  have hp_pos : HasPosLeadingCoeff p := hpnn.pos_leadingCoeff hp0
  have hq_pos : HasPosLeadingCoeff q := hqnn.pos_leadingCoeff hq0
  exact (prec_add_of_prec_right_of_posLeadingCoeff hpstr hqstr hp_pos hq_pos).toPrec0

/-! ## Haglund--Zhang / A046802 backend -/

namespace OEIS
namespace Backend

/-- Haglund--Zhang notation for threshold entries. -/
abbrev hzEntry (t : ℕ) (α : ℝ[X]) (j : ℕ) : ℝ[X] :=
  thresholdEntry t α j

/-- Haglund--Zhang notation for threshold rows. -/
abbrev hzRow (q t : ℕ) (α : ℝ[X]) : List ℝ[X] :=
  thresholdRow q t α

/-- Haglund--Zhang notation for threshold matrices. -/
abbrev hzMatrix (q : ℕ) (rows : List (ℕ × ℝ[X])) : List (List ℝ[X]) :=
  thresholdMatrix q rows

/-- Threshold list for the binomial Eulerian specialization. -/
abbrev hzBinomialThresholds (n : ℕ) : List ℕ :=
  List.range n

lemma hzBinomialThresholds_mono (n : ℕ) :
    ∀ i j : Fin (hzBinomialThresholds n).length, i ≤ j →
      (hzBinomialThresholds n).get i ≤ (hzBinomialThresholds n).get j := by
  intro i j hij
  simp only [hzBinomialThresholds, List.get_eq_getElem, List.getElem_range]
  exact hij

/-- Row data for the binomial Eulerian specialization: all markers are `1 + X`. -/
abbrev hzBinomialRows (ts : List ℕ) : List (ℕ × ℝ[X]) :=
  ts.map (fun t => (t, (1 + X : ℝ[X])))

/-- Matrix for the binomial Eulerian specialization. -/
abbrev hzBinomialMatrix (q : ℕ) (ts : List ℕ) : List (List ℝ[X]) :=
  hzMatrix q (hzBinomialRows ts)

/-- The one-row terminal data for `(1 + X) f₀ + f₁ + ...`. -/
abbrev hzTerminalRows : List (ℕ × ℝ[X]) :=
  [(0, (1 + X : ℝ[X]))]

/-- The one-row terminal matrix for `(1 + X) f₀ + f₁ + ...`. -/
abbrev hzTerminalMatrix (q : ℕ) : List (List ℝ[X]) :=
  hzMatrix q hzTerminalRows

/-- Haglund--Zhang terminal polynomial `(1 + X) f₀ + f₁ + ...`.

The length parameter is kept explicit so this is literally the action of the
terminal threshold row of width `q`. -/
def hzTerminalPolynomial (q : ℕ) (fs : List ℝ[X]) : ℝ[X] :=
  ((hzRow q 0 (1 + X)).zipWith (· * ·) fs).sum

@[simp] lemma length_hzBinomialRows (ts : List ℕ) :
    (hzBinomialRows ts).length = ts.length := by
  simp [hzBinomialRows]

@[simp] lemma length_hzBinomialMatrix (q : ℕ) (ts : List ℕ) :
    (hzBinomialMatrix q ts).length = ts.length := by
  simp [hzBinomialMatrix]

@[simp] lemma length_hzTerminalRows :
    hzTerminalRows.length = 1 := by
  simp [hzTerminalRows]

@[simp] lemma length_hzTerminalMatrix (q : ℕ) :
    (hzTerminalMatrix q).length = 1 := by
  simp [hzTerminalMatrix]

/-- Validity data for a Haglund--Zhang threshold matrix. -/
structure HZData (rows : List (ℕ × ℝ[X])) : Prop where
  /-- Every diagonal marker is `1` or `1 + X`. -/
  alpha_mem : ∀ p ∈ rows, p.2 = 1 ∨ p.2 = 1 + X
  /-- Thresholds are nondecreasing down the rows. -/
  thresh_mono : ∀ i j : Fin rows.length, i ≤ j → (rows.get i).1 ≤ (rows.get j).1
  /-- Equal-threshold compatibility in the matrix orientation. -/
  compat : ∀ i j : Fin rows.length, i ≤ j → (rows.get i).1 = (rows.get j).1 →
    (rows.get i).2 = 1 + X → (rows.get j).2 = 1 + X

lemma HZData.alpha_nonneg {rows : List (ℕ × ℝ[X])} (h : HZData rows) :
    ∀ p ∈ rows, HasNonnegCoeffs p.2 := by
  intro p hp
  rcases h.alpha_mem p hp with hα | hα <;> rw [hα]
  · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one
  · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one_add_X

lemma hzBinomialRows_data {ts : List ℕ}
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j) :
    HZData (hzBinomialRows ts) := by
  constructor
  · intro p hp
    simp only [hzBinomialRows, List.mem_map] at hp
    obtain ⟨t, _, rfl⟩ := hp
    exact Or.inr rfl
  · intro i j hij
    let i' : Fin ts.length := ⟨i.1, by simpa using i.2⟩
    let j' : Fin ts.length := ⟨j.1, by simpa using j.2⟩
    have hij' : i' ≤ j' := hij
    have hkey := hmono i' j' hij'
    simpa [hzBinomialRows, List.get_eq_getElem, i', j'] using hkey
  · intro i j _ _ _
    simp [hzBinomialRows, List.get_eq_getElem, List.getElem_map]

lemma hzTerminalRows_data :
    HZData hzTerminalRows := by
  constructor
  · intro p hp
    have hp' : p = (0, (1 + X : ℝ[X])) := by simpa [hzTerminalRows] using hp
    subst p
    exact Or.inr rfl
  · intro i j _
    simp [hzTerminalRows]
  · intro i j _ _ _
    simp [hzTerminalRows]

@[simp] lemma matPolyAction_hzTerminalMatrix (q : ℕ) (fs : List ℝ[X]) :
    matPolyAction (hzTerminalMatrix q) fs = [hzTerminalPolynomial q fs] := by
  simp [hzTerminalPolynomial, hzTerminalMatrix, hzTerminalRows, hzMatrix,
    thresholdMatrix, matPolyAction]

@[simp] lemma sum_matPolyAction_hzTerminalMatrix (q : ℕ) (fs : List ℝ[X]) :
    (matPolyAction (hzTerminalMatrix q) fs).sum = hzTerminalPolynomial q fs := by
  simp

lemma hzTerminalPolynomial_mem_matPolyAction (q : ℕ) (fs : List ℝ[X]) :
    hzTerminalPolynomial q fs ∈ matPolyAction (hzTerminalMatrix q) fs := by
  simp

/-! ### Finite-entry shape helpers -/

private lemma hzMiddleQuadratic_eq (s t : ℝ) :
    ((C s * X + C t) * (1 + X) + X : ℝ[X]) =
      C s * X ^ 2 + C (s + t + 1) * X + C t := by
  grind

private lemma eval_hzMiddleQuadratic (s t r : ℝ) :
    (((C s * X + C t) * (1 + X) + X : ℝ[X]).eval r) =
      s * r ^ 2 + (s + t + 1) * r + t := by
  rw [hzMiddleQuadratic_eq]
  simp [eval_add, eval_mul, eval_C, eval_X, pow_two]

private lemma hzMiddleQuadratic_natDegree {s t : ℝ} (hs : 0 < s) :
    (((C s * X + C t) * (1 + X) + X : ℝ[X]).natDegree) = 2 := by
  rw [hzMiddleQuadratic_eq]
  exact natDegree_quadratic hs.ne'

private lemma hzMiddleQuadratic_splits {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ((C s * X + C t) * (1 + X) + X : ℝ[X]).Splits := by
  rw [hzMiddleQuadratic_eq]
  exact quadraticPoly_splits_of_le hs (by
    nlinarith [sq_nonneg (s - t), hs, ht])

private lemma hzMiddleQuadratic_posLeadingCoeff {s t : ℝ} (hs : 0 < s) :
    HasPosLeadingCoeff ((C s * X + C t) * (1 + X) + X : ℝ[X]) := by
  unfold HasPosLeadingCoeff
  rw [hzMiddleQuadratic_eq, leadingCoeff_quadratic hs.ne']
  exact hs

private lemma hzXAffineAddOne_eq (s t : ℝ) :
    (X * (C s * X + C t + 1) : ℝ[X]) =
      C s * X ^ 2 + C (t + 1) * X + C 0 := by
  grind

private lemma eval_hzXAffineAddOne (s t r : ℝ) :
    ((X * (C s * X + C t + 1) : ℝ[X]).eval r) =
      s * r ^ 2 + (t + 1) * r := by
  rw [hzXAffineAddOne_eq]
  simp [eval_add, eval_mul, eval_C, eval_X, pow_two]

private lemma hzXAffineAddOne_natDegree {s t : ℝ} (hs : 0 < s) :
    ((X * (C s * X + C t + 1) : ℝ[X]).natDegree) = 2 := by
  rw [hzXAffineAddOne_eq]
  exact natDegree_quadratic hs.ne'

private lemma hzXAffineAddOne_splits {s t : ℝ} (hs : 0 < s) :
    (X * (C s * X + C t + 1) : ℝ[X]).Splits := by
  rw [hzXAffineAddOne_eq]
  exact quadraticPoly_splits_of_le hs (by
    nlinarith [sq_nonneg (t + 1)])

private lemma hzXAffineAddOne_posLeadingCoeff {s t : ℝ} (hs : 0 < s) :
    HasPosLeadingCoeff (X * (C s * X + C t + 1) : ℝ[X]) := by
  unfold HasPosLeadingCoeff
  rw [hzXAffineAddOne_eq, leadingCoeff_quadratic hs.ne']
  exact hs

private lemma prec0_hz_linear_to_quadratic_of_eval_nonpos
    {f F : ℝ[X]}
    (hfdeg : f.natDegree = 1)
    (hFdeg : F.natDegree = 2)
    (hF_splits : F.Splits)
    (hF_pos : HasPosLeadingCoeff F)
    (hroot_nonpos : ∀ r, f.IsRoot r → F.eval r ≤ 0) :
    Prec0 f F := by
  have hInter : Interlaces (1 : ℝ[X]) f := interlaces_one_linear hfdeg
  have hF_ne : F ≠ 0 := by
    intro hF
    rw [hF, natDegree_zero] at hFdeg
    norm_num at hFdeg
  have hno : ∀ r, f.IsRoot r → ¬ (1 : ℝ[X]).IsRoot r := by
    intro r _ h
    simp at h
  have hroot :
      ∀ r, f.IsRoot r → F.eval r * (1 : ℝ[X]).eval r ≤ 0 := by
    intro r hr
    simpa using hroot_nonpos r hr
  exact
    (prec_of_interlaces_eval_mul_nonpos_of_no_common
      hInter hasPosLeadingCoeff_one hF_ne hF_splits hF_pos
      (by lia) (by lia) hno hroot).toPrec0

private lemma prec0_hz_affine_add_one_self {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + 1) (C s * X + C t + 1) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  exact prec0_refl_of_isRealRooted
    (isRealRooted_affine_factor (s := s) (t := t + 1) hs)

private lemma prec0_hz_affine_add_one_affine_add_one_add_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + 1) (C s * X + C t + (1 + X)) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
    C (s + 1) * X + C (t + 1) by grind]
  exact
    prec0_affine_linear_affine_linear_of_cross
      (u := s) (v := t + 1) (U := s + 1) (V := t + 1)
      hs (by positivity) (by nlinarith [ht])

private lemma prec0_hz_affine_add_one_add_X_self {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + (1 + X)) (C s * X + C t + (1 + X)) := by
  rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
    C (s + 1) * X + C (t + 1) by grind]
  exact prec0_refl_of_isRealRooted
    (isRealRooted_affine_factor (s := s + 1) (t := t + 1) (by positivity))

private lemma prec0_hz_affine_add_one_affine_add_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + 1) (C s * X + C t + X) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact
    prec0_affine_linear_affine_linear_of_cross
      (u := s) (v := t + 1) (U := s + 1) (V := t)
      hs (by positivity) (by nlinarith [hs, ht])

private lemma prec0_hz_affine_add_one_add_X_affine_add_X
    {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + (1 + X)) (C s * X + C t + X) := by
  rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
    C (s + 1) * X + C (t + 1) by grind]
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact
    prec0_affine_linear_affine_linear_of_cross
      (u := s + 1) (v := t + 1) (U := s + 1) (V := t)
      (by positivity) (by positivity) (by nlinarith)

private lemma prec0_hz_affine_add_X_self {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + X) (C s * X + C t + X) := by
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact prec0_refl_of_isRealRooted
    (isRealRooted_affine_factor (s := s + 1) (t := t) (by positivity))

private lemma prec0_hz_affine_add_one_middleQuadratic
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + 1) ((C s * X + C t) * (1 + X) + X) := by
  apply prec0_hz_linear_to_quadratic_of_eval_nonpos
  · rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    grind
  · exact hzMiddleQuadratic_natDegree hs
  · exact hzMiddleQuadratic_splits hs ht
  · exact hzMiddleQuadratic_posLeadingCoeff hs
  · intro r hr
    have hroot0 : t + (1 + s * r) = 0 := by
      simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C, eval_X,
        add_assoc, add_comm, add_left_comm] using hr
    have hroot : s * r + (t + 1) = 0 := by nlinarith
    rw [eval_hzMiddleQuadratic]
    have hscaled : s ^ 2 * (s * r ^ 2 + (s + t + 1) * r + t) = -s ^ 2 := by
      linear_combination (s ^ 2 * r + s ^ 2) * hroot
    have hscale_pos : 0 < s ^ 2 := sq_pos_of_pos hs
    nlinarith [hscaled, sq_nonneg s, hscale_pos]

private lemma prec0_hz_affine_add_one_add_X_middleQuadratic
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + (1 + X)) ((C s * X + C t) * (1 + X) + X) := by
  apply prec0_hz_linear_to_quadratic_of_eval_nonpos
  · rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
        C (s + 1) * X + C (t + 1) by grind]
    grind
  · exact hzMiddleQuadratic_natDegree hs
  · exact hzMiddleQuadratic_splits hs ht
  · exact hzMiddleQuadratic_posLeadingCoeff hs
  · intro r hr
    have hroot0 : t + (1 + (r + s * r)) = 0 := by
      simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C, eval_X,
        add_assoc, add_comm, add_left_comm] using hr
    have hroot : (s + 1) * r + (t + 1) = 0 := by nlinarith
    rw [eval_hzMiddleQuadratic]
    have hscaled : (s + 1) ^ 2 * (s * r ^ 2 + (s + t + 1) * r + t) =
        -s ^ 2 + s * t - s - t ^ 2 - t - 1 := by
      linear_combination ((s ^ 2 + s) * r + s ^ 2 + s + t + 1) * hroot
    have hscale_pos : 0 < (s + 1) ^ 2 := by positivity
    have hnonpos : -s ^ 2 + s * t - s - t ^ 2 - t - 1 ≤ 0 := by
      nlinarith [sq_nonneg (s - t), hs, ht]
    nlinarith

private lemma prec0_hz_affine_add_X_middleQuadratic
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + X) ((C s * X + C t) * (1 + X) + X) := by
  apply prec0_hz_linear_to_quadratic_of_eval_nonpos
  · rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
    grind
  · exact hzMiddleQuadratic_natDegree hs
  · exact hzMiddleQuadratic_splits hs ht
  · exact hzMiddleQuadratic_posLeadingCoeff hs
  · intro r hr
    have hroot0 : t + (r + s * r) = 0 := by
      simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C, eval_X,
        add_assoc, add_comm, add_left_comm] using hr
    have hroot : (s + 1) * r + t = 0 := by nlinarith
    rw [eval_hzMiddleQuadratic]
    have hscaled : (s + 1) ^ 2 * (s * r ^ 2 + (s + t + 1) * r + t) =
        -t ^ 2 := by
      linear_combination ((s ^ 2 + s) * r + s ^ 2 + 2 * s + t + 1) * hroot
    have hscale_pos : 0 < (s + 1) ^ 2 := by positivity
    nlinarith [hscaled, sq_nonneg t, hscale_pos]

private lemma prec0_hz_affine_add_one_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + 1) (X * (C s * X + C t + 1)) := by
  have hf_rr :
      ((C s * X + C t + 1 : ℝ[X]) ≠ 0 ∧
        (C s * X + C t + 1 : ℝ[X]).Splits) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact isRealRooted_affine_factor (s := s) (t := t + 1) hs
  have hf_nn : HasNonnegCoeffs (C s * X + C t + 1 : ℝ[X]) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact hasNonnegCoeffs_affine_linear hs.le (by nlinarith)
  simpa using (prec_self_mul_X_of_nonneg hf_rr.1 hf_rr.2 hf_nn).toPrec0

private lemma prec0_hz_affine_add_one_add_X_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + (1 + X)) (X * (C s * X + C t + 1)) := by
  apply prec0_hz_linear_to_quadratic_of_eval_nonpos
  · rw [show (C s * X + C t + (1 + X) : ℝ[X]) =
        C (s + 1) * X + C (t + 1) by grind]
    grind
  · exact hzXAffineAddOne_natDegree hs
  · exact hzXAffineAddOne_splits hs
  · exact hzXAffineAddOne_posLeadingCoeff hs
  · intro r hr
    have hroot0 : t + (1 + (r + s * r)) = 0 := by
      simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C, eval_X,
        add_assoc, add_comm, add_left_comm] using hr
    have hroot : (s + 1) * r + (t + 1) = 0 := by nlinarith
    rw [eval_hzXAffineAddOne]
    have hscaled : (s + 1) ^ 2 * (s * r ^ 2 + (t + 1) * r) =
        -(t + 1) ^ 2 := by
      linear_combination ((s ^ 2 + s) * r + t + 1) * hroot
    have hscale_pos : 0 < (s + 1) ^ 2 := by positivity
    nlinarith [hscaled, sq_nonneg (t + 1), hscale_pos]

private lemma prec0_hz_affine_add_X_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + X) (X * (C s * X + C t + 1)) := by
  apply prec0_hz_linear_to_quadratic_of_eval_nonpos
  · rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
    grind
  · exact hzXAffineAddOne_natDegree hs
  · exact hzXAffineAddOne_splits hs
  · exact hzXAffineAddOne_posLeadingCoeff hs
  · intro r hr
    have hroot0 : t + (r + s * r) = 0 := by
      simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C, eval_X,
        add_assoc, add_comm, add_left_comm] using hr
    have hroot : (s + 1) * r + t = 0 := by nlinarith
    rw [eval_hzXAffineAddOne]
    have hscaled : (s + 1) ^ 2 * (s * r ^ 2 + (t + 1) * r) =
        -t * (s + t + 1) := by
      linear_combination ((s ^ 2 + s) * r + s + t + 1) * hroot
    have hscale_pos : 0 < (s + 1) ^ 2 := by positivity
    nlinarith [hscaled, ht, hs]

private lemma prec0_hz_affine_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t) (X * (C s * X + C t + 1)) := by
  apply prec0_hz_linear_to_quadratic_of_eval_nonpos
  · grind
  · exact hzXAffineAddOne_natDegree hs
  · exact hzXAffineAddOne_splits hs
  · exact hzXAffineAddOne_posLeadingCoeff hs
  · intro r hr
    have hroot0 : t + s * r = 0 := by
      simpa [Polynomial.IsRoot.def, eval_add, eval_mul, eval_C, eval_X,
        add_assoc, add_comm, add_left_comm] using hr
    have hroot : s * r + t = 0 := by nlinarith
    rw [eval_hzXAffineAddOne]
    have hscaled : s ^ 2 * (s * r ^ 2 + (t + 1) * r) = -s * t := by
      linear_combination (s ^ 2 * r + s) * hroot
    have hscale_pos : 0 < s ^ 2 := sq_pos_of_pos hs
    nlinarith [hscaled, hs, ht]

private lemma prec0_hz_affine_add_one_mul_one_add_X
    {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + 1) ((C s * X + C t + 1) * (1 + X)) := by
  have hd_rr :
      ((C s * X + C t + 1 : ℝ[X]) ≠ 0 ∧
        (C s * X + C t + 1 : ℝ[X]).Splits) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact isRealRooted_affine_factor (s := s) (t := t + 1) hs
  have hbase : Prec (1 : ℝ[X]) (1 + X) := by
    have hdeg : (1 + X : ℝ[X]).natDegree = 1 := by
      simpa [show (1 + X : ℝ[X]) = X + C (1 : ℝ) by grind] using
        (Polynomial.natDegree_X_add_C (x := (1 : ℝ)))
    exact (interlaces_one_linear (p := (1 + X : ℝ[X])) hdeg).toPrec
  have hmul := prec_mul_common_factor hd_rr.1 hd_rr.2 hbase
  simpa using hmul.toPrec0

private lemma prec0_hz_mul_one_add_X_self
    {s t : ℝ} (hs : 0 < s) :
    Prec0 ((C s * X + C t + 1) * (1 + X)) ((C s * X + C t + 1) * (1 + X)) := by
  have hlin_rr :
      ((C s * X + C t + 1 : ℝ[X]) ≠ 0 ∧
        (C s * X + C t + 1 : ℝ[X]).Splits) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact isRealRooted_affine_factor (s := s) (t := t + 1) hs
  have hS_rr : ((1 + X : ℝ[X]) ≠ 0 ∧ (1 + X : ℝ[X]).Splits) := by
    rw [show (1 + X : ℝ[X]) = C (1 : ℝ) * X + C 1 by grind]
    exact isRealRooted_affine_factor (s := 1) (t := 1) zero_lt_one
  exact prec0_refl_of_isRealRooted
    (isRealRooted_mul hlin_rr.1 hlin_rr.2 hS_rr.1 hS_rr.2)

private lemma prec0_hz_middleQuadratic_self
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 ((C s * X + C t) * (1 + X) + X)
      ((C s * X + C t) * (1 + X) + X) := by
  have hdeg := hzMiddleQuadratic_natDegree (s := s) (t := t) hs
  have hne : ((C s * X + C t) * (1 + X) + X : ℝ[X]) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    norm_num at hdeg
  exact prec0_refl_of_isRealRooted ⟨hne, hzMiddleQuadratic_splits hs ht⟩

private lemma prec0_hz_mul_one_add_X_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) :
    Prec0 ((C s * X + C t + 1) * (1 + X)) (X * (C s * X + C t + 1)) := by
  have hd_rr :
      ((C s * X + C t + 1 : ℝ[X]) ≠ 0 ∧
        (C s * X + C t + 1 : ℝ[X]).Splits) := by
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact isRealRooted_affine_factor (s := s) (t := t + 1) hs
  have hbase : Prec (1 + X : ℝ[X]) X := by
    rw [show (1 + X : ℝ[X]) = X + 1 by grind]
    simpa using
      prec_affine_linear_affine_linear_of_cross
        (u := 1) (v := 1) (U := 1) (V := 0)
        zero_lt_one zero_lt_one (by norm_num)
  have hmul := prec_mul_common_factor hd_rr.1 hd_rr.2 hbase
  rw [show (X * (C s * X + C t + 1) : ℝ[X]) =
    (C s * X + C t + 1) * X by ring]
  simpa using hmul.toPrec0

private lemma prec0_hz_XAffineAddOne_self
    {s t : ℝ} (hs : 0 < s) :
    Prec0 (X * (C s * X + C t + 1)) (X * (C s * X + C t + 1)) := by
  have hdeg := hzXAffineAddOne_natDegree (s := s) (t := t) hs
  have hne : (X * (C s * X + C t + 1) : ℝ[X]) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    norm_num at hdeg
  exact prec0_refl_of_isRealRooted ⟨hne, hzXAffineAddOne_splits hs⟩

private lemma prec0_hz_middleQuadratic_XAffineAddOne
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 ((C s * X + C t) * (1 + X) + X) (X * (C s * X + C t + 1)) := by
  have hself : Prec0 (X * (C s * X + C t + 1)) (X * (C s * X + C t + 1)) :=
    prec0_hz_XAffineAddOne_self hs
  have hlin : Prec0 (C s * X + C t) (X * (C s * X + C t + 1)) :=
    prec0_hz_affine_XAffineAddOne hs ht
  have hq_nn : HasNonnegCoeffs (X * (C s * X + C t + 1) : ℝ[X]) := by
    refine hasNonnegCoeffs_X.mul ?_
    rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
    exact hasNonnegCoeffs_affine_linear hs.le (by nlinarith)
  have hlin_nn : HasNonnegCoeffs (C s * X + C t : ℝ[X]) :=
    hasNonnegCoeffs_affine_linear hs.le ht.le
  have hsum :=
    prec0_add_left_of_common_right_of_nonneg hself hlin hq_nn hlin_nn
  rw [show ((C s * X + C t) * (1 + X) + X : ℝ[X]) =
      X * (C s * X + C t + 1) + (C s * X + C t) by grind]
  exact hsum

private def HZ2x2EntryShape (a b c d : ℝ[X]) : Prop :=
  Threshold2x2EntryTuple a b c d 1 1 1 1 ∨
  Threshold2x2EntryTuple a b c d 1 1 (1 + X) 1 ∨
  Threshold2x2EntryTuple a b c d 1 1 (1 + X) (1 + X) ∨
  Threshold2x2EntryTuple a b c d 1 1 X 1 ∨
  Threshold2x2EntryTuple a b c d 1 1 X (1 + X) ∨
  Threshold2x2EntryTuple a b c d 1 1 X X ∨
  Threshold2x2EntryTuple a b c d (1 + X) 1 (1 + X) 1 ∨
  Threshold2x2EntryTuple a b c d (1 + X) 1 X 1 ∨
  Threshold2x2EntryTuple a b c d (1 + X) 1 X (1 + X) ∨
  Threshold2x2EntryTuple a b c d (1 + X) 1 X X ∨
  Threshold2x2EntryTuple a b c d (1 + X) (1 + X) (1 + X) (1 + X) ∨
  Threshold2x2EntryTuple a b c d (1 + X) (1 + X) X X ∨
  Threshold2x2EntryTuple a b c d X 1 X 1 ∨
  Threshold2x2EntryTuple a b c d X 1 X (1 + X) ∨
  Threshold2x2EntryTuple a b c d X 1 X X ∨
  Threshold2x2EntryTuple a b c d X (1 + X) X (1 + X) ∨
  Threshold2x2EntryTuple a b c d X (1 + X) X X ∨
  Threshold2x2EntryTuple a b c d X X X X

private lemma HZ2x2EntryShape.has2x2 {a b c d : ℝ[X]}
    (h : HZ2x2EntryShape a b c d) :
    Has2x2InterlacingProperty0 a b c d := by
  intro s t hs ht
  rcases h with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
  · simpa using prec0_hz_affine_add_one_self hs
  · simpa using prec0_hz_affine_add_one_affine_add_one_add_X hs ht
  · simpa using prec0_hz_affine_add_one_add_X_self hs
  · simpa using prec0_hz_affine_add_one_affine_add_X hs ht
  · simpa using prec0_hz_affine_add_one_add_X_affine_add_X hs
  · simpa using prec0_hz_affine_add_X_self hs
  · simpa [mul_add, add_mul, add_assoc, add_comm, add_left_comm] using
      prec0_hz_affine_add_one_mul_one_add_X hs
  · simpa using prec0_hz_affine_add_one_middleQuadratic hs ht
  · simpa using prec0_hz_affine_add_one_add_X_middleQuadratic hs ht
  · simpa using prec0_hz_affine_add_X_middleQuadratic hs ht
  · simpa [mul_add, add_mul, add_assoc, add_comm, add_left_comm] using
      prec0_hz_mul_one_add_X_self hs
  · simpa using prec0_hz_middleQuadratic_self hs ht
  · rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using prec0_hz_affine_add_one_XAffineAddOne hs ht
  · rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using prec0_hz_affine_add_one_add_X_XAffineAddOne hs ht
  · rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using prec0_hz_affine_add_X_XAffineAddOne hs ht
  · rw [show ((C s * X + C t) * (1 + X) + (1 + X) : ℝ[X]) =
        (C s * X + C t + 1) * (1 + X) by grind]
    rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using prec0_hz_mul_one_add_X_XAffineAddOne hs
  · rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using prec0_hz_middleQuadratic_XAffineAddOne hs ht
  · rw [show ((C s * X + C t) * X + X : ℝ[X]) =
        X * (C s * X + C t + 1) by grind]
    simpa using prec0_hz_XAffineAddOne_self hs

private lemma hzEntry_shape
    {t₁ t₂ j₁ j₂ : ℕ} {α₁ α₂ : ℝ[X]}
    (hα₁ : α₁ = 1 ∨ α₁ = 1 + X)
    (hα₂ : α₂ = 1 ∨ α₂ = 1 + X)
    (ht : t₁ ≤ t₂) (hj : j₁ ≤ j₂)
    (hcompat : t₁ = t₂ → α₁ = 1 + X → α₂ = 1 + X) :
    HZ2x2EntryShape
      (hzEntry t₁ α₁ j₁) (hzEntry t₁ α₁ j₂)
      (hzEntry t₂ α₂ j₁) (hzEntry t₂ α₂ j₂) := by
  rcases hα₁ with rfl | rfl <;> rcases hα₂ with rfl | rfl
  all_goals
    simp at hcompat
    unfold HZ2x2EntryShape Threshold2x2EntryTuple
    simp only [thresholdEntry]
    split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
    all_goals try lia

/-- The finite entrywise Haglund--Zhang `2 x 2` threshold check. -/
def HZEntryHas2x2Statement : Prop :=
  ∀ {t₁ t₂ j₁ j₂ : ℕ} {α₁ α₂ : ℝ[X]},
    (α₁ = 1 ∨ α₁ = 1 + X) →
    (α₂ = 1 ∨ α₂ = 1 + X) →
    t₁ ≤ t₂ → j₁ ≤ j₂ →
    (t₁ = t₂ → α₁ = 1 + X → α₂ = 1 + X) →
    Has2x2InterlacingProperty0
      (hzEntry t₁ α₁ j₁) (hzEntry t₁ α₁ j₂)
      (hzEntry t₂ α₂ j₁) (hzEntry t₂ α₂ j₂)

theorem hzEntry_has2x2 : HZEntryHas2x2Statement := by
  intro t₁ t₂ j₁ j₂ α₁ α₂ hα₁ hα₂ ht hj hcompat
  exact (hzEntry_shape hα₁ hα₂ ht hj hcompat).has2x2

lemma HZData.entry_has2x2 {q : ℕ} {rows : List (ℕ × ℝ[X])}
    (hrows : HZData rows) (hentry : HZEntryHas2x2Statement) :
    ∀ (i₁ i₂ : Fin rows.length) (j₁ j₂ : Fin q),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (hzEntry (rows.get i₁).1 (rows.get i₁).2 j₁.1)
        (hzEntry (rows.get i₁).1 (rows.get i₁).2 j₂.1)
        (hzEntry (rows.get i₂).1 (rows.get i₂).2 j₁.1)
        (hzEntry (rows.get i₂).1 (rows.get i₂).2 j₂.1) := by
  intro i₁ i₂ j₁ j₂ hi hj
  exact hentry
    (hrows.alpha_mem (rows.get i₁) (List.get_mem rows i₁))
    (hrows.alpha_mem (rows.get i₂) (List.get_mem rows i₂))
    (hrows.thresh_mono i₁ i₂ hi)
    hj
    (hrows.compat i₁ i₂ hi)

/-- Haglund--Zhang threshold matrices preserve interlacing once the finite
entrywise `2 x 2` check is available. -/
theorem haglund_zhang_s_inversion_interlacing_backend
    (hentry : HZEntryHas2x2Statement)
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : HZData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (hzMatrix q rows) fs) :=
  thresholdMatrix_preserves_interlacing_seq0_of_entry rows
    hrows.alpha_nonneg (hrows.entry_has2x2 hentry) fs hfs_len hfs

theorem haglund_zhang_s_inversion_interlacing
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : HZData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (hzMatrix q rows) fs) :=
  haglund_zhang_s_inversion_interlacing_backend hzEntry_has2x2
    rows hrows fs hfs_len hfs

theorem haglund_zhang_s_inversion_interlacing_backend_weak
    (hentry : HZEntryHas2x2Statement)
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : HZData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (hzMatrix q rows) fs) ∧
      ∀ f ∈ matPolyAction (hzMatrix q rows) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  thresholdMatrix_preserves_interlacing_seq0_of_entry_weak rows
    hrows.alpha_nonneg (hrows.entry_has2x2 hentry) fs hfs_len hfs hfs_real

theorem haglund_zhang_s_inversion_interlacing_weak
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : HZData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (hzMatrix q rows) fs) ∧
      ∀ f ∈ matPolyAction (hzMatrix q rows) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  haglund_zhang_s_inversion_interlacing_backend_weak hzEntry_has2x2
    rows hrows fs hfs_len hfs hfs_real

theorem haglund_zhang_s_inversion_sum_realRooted_backend
    (hentry : HZEntryHas2x2Statement)
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : HZData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hsum_ne : (matPolyAction (hzMatrix q rows) fs).sum ≠ 0) :
    (matPolyAction (hzMatrix q rows) fs).sum ≠ 0 ∧
      ((matPolyAction (hzMatrix q rows) fs).sum).Splits := by
  have hout :=
    haglund_zhang_s_inversion_interlacing_backend_weak hentry
      rows hrows fs hfs_len hfs hfs_real
  exact isRealRooted_sum_of_isInterlacingSeq0Nonneg hout.1 hout.2 hsum_ne

theorem haglund_zhang_s_inversion_sum_realRooted
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : HZData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hsum_ne : (matPolyAction (hzMatrix q rows) fs).sum ≠ 0) :
    (matPolyAction (hzMatrix q rows) fs).sum ≠ 0 ∧
      ((matPolyAction (hzMatrix q rows) fs).sum).Splits :=
  haglund_zhang_s_inversion_sum_realRooted_backend hzEntry_has2x2
    rows hrows fs hfs_len hfs hfs_real hsum_ne

theorem haglund_zhang_terminal_polynomial_realRooted_backend
    (hentry : HZEntryHas2x2Statement)
    {q : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hterminal_ne : hzTerminalPolynomial q fs ≠ 0) :
    hzTerminalPolynomial q fs ≠ 0 ∧ (hzTerminalPolynomial q fs).Splits := by
  have hout :=
    haglund_zhang_s_inversion_interlacing_backend_weak hentry
      hzTerminalRows hzTerminalRows_data fs hfs_len hfs hfs_real
  exact hout.2 (hzTerminalPolynomial q fs)
    (hzTerminalPolynomial_mem_matPolyAction q fs) hterminal_ne

theorem haglund_zhang_terminal_polynomial_realRooted
    {q : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hterminal_ne : hzTerminalPolynomial q fs ≠ 0) :
    hzTerminalPolynomial q fs ≠ 0 ∧ (hzTerminalPolynomial q fs).Splits :=
  haglund_zhang_terminal_polynomial_realRooted_backend hzEntry_has2x2
    fs hfs_len hfs hfs_real hterminal_ne

theorem haglund_zhang_terminal_polynomial_realRooted_of_interlacing
    {q : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs)
    (hterminal_ne : hzTerminalPolynomial q fs ≠ 0) :
    hzTerminalPolynomial q fs ≠ 0 ∧ (hzTerminalPolynomial q fs).Splits := by
  have hfs_weak := weakData_of_isInterlacingSeqNonneg hfs
  exact haglund_zhang_terminal_polynomial_realRooted
    fs hfs_len hfs_weak.1 hfs_weak.2 hterminal_ne

/-- Binomial Eulerian specialization: all diagonal markers are `1 + X`. -/
theorem haglund_zhang_binomial_eulerian_backend
    (hentry : HZEntryHas2x2Statement)
    {q : ℕ} (ts : List ℕ)
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (hzBinomialMatrix q ts) fs) :=
  haglund_zhang_s_inversion_interlacing_backend hentry _
    (hzBinomialRows_data hmono) fs hfs_len hfs

theorem haglund_zhang_binomial_eulerian
    {q : ℕ} (ts : List ℕ)
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (hzBinomialMatrix q ts) fs) :=
  haglund_zhang_binomial_eulerian_backend hzEntry_has2x2
    ts hmono fs hfs_len hfs

theorem haglund_zhang_binomial_eulerian_range
    {q n : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (hzBinomialMatrix q (hzBinomialThresholds n)) fs) :=
  haglund_zhang_binomial_eulerian
    (hzBinomialThresholds n) (hzBinomialThresholds_mono n) fs hfs_len hfs

theorem haglund_zhang_binomial_eulerian_backend_weak
    (hentry : HZEntryHas2x2Statement)
    {q : ℕ} (ts : List ℕ)
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (hzBinomialMatrix q ts) fs) ∧
      ∀ f ∈ matPolyAction (hzBinomialMatrix q ts) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  haglund_zhang_s_inversion_interlacing_backend_weak hentry
    _ (hzBinomialRows_data hmono) fs hfs_len hfs hfs_real

theorem haglund_zhang_binomial_eulerian_weak
    {q : ℕ} (ts : List ℕ)
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (hzBinomialMatrix q ts) fs) ∧
      ∀ f ∈ matPolyAction (hzBinomialMatrix q ts) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  haglund_zhang_binomial_eulerian_backend_weak hzEntry_has2x2
    ts hmono fs hfs_len hfs hfs_real

theorem haglund_zhang_binomial_eulerian_range_weak
    {q n : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (hzBinomialMatrix q (hzBinomialThresholds n)) fs) ∧
      ∀ f ∈ matPolyAction (hzBinomialMatrix q (hzBinomialThresholds n)) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  haglund_zhang_binomial_eulerian_weak
    (hzBinomialThresholds n) (hzBinomialThresholds_mono n)
    fs hfs_len hfs hfs_real

theorem haglund_zhang_binomial_eulerian_sum_realRooted_backend
    (hentry : HZEntryHas2x2Statement)
    {q : ℕ} (ts : List ℕ)
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hsum_ne :
      (matPolyAction (hzBinomialMatrix q ts) fs).sum ≠ 0) :
    (matPolyAction (hzBinomialMatrix q ts) fs).sum ≠ 0 ∧
      ((matPolyAction (hzBinomialMatrix q ts) fs).sum).Splits := by
  have hout :=
    haglund_zhang_binomial_eulerian_backend_weak hentry
      ts hmono fs hfs_len hfs hfs_real
  exact isRealRooted_sum_of_isInterlacingSeq0Nonneg hout.1 hout.2 hsum_ne

theorem haglund_zhang_binomial_eulerian_sum_realRooted
    {q : ℕ} (ts : List ℕ)
    (hmono : ∀ i j : Fin ts.length, i ≤ j → ts.get i ≤ ts.get j)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hsum_ne :
      (matPolyAction (hzBinomialMatrix q ts) fs).sum ≠ 0) :
    (matPolyAction (hzBinomialMatrix q ts) fs).sum ≠ 0 ∧
      ((matPolyAction (hzBinomialMatrix q ts) fs).sum).Splits :=
  haglund_zhang_binomial_eulerian_sum_realRooted_backend hzEntry_has2x2
    ts hmono fs hfs_len hfs hfs_real hsum_ne

theorem haglund_zhang_binomial_eulerian_range_sum_realRooted
    {q n : ℕ} (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits))
    (hsum_ne :
      (matPolyAction (hzBinomialMatrix q (hzBinomialThresholds n)) fs).sum ≠ 0) :
    (matPolyAction (hzBinomialMatrix q (hzBinomialThresholds n)) fs).sum ≠ 0 ∧
      ((matPolyAction (hzBinomialMatrix q (hzBinomialThresholds n)) fs).sum).Splits :=
  haglund_zhang_binomial_eulerian_sum_realRooted
    (hzBinomialThresholds n) (hzBinomialThresholds_mono n)
    fs hfs_len hfs hfs_real hsum_ne

private def realListAction (G : List (List ℝ)) (cs : List ℝ) : List ℝ :=
  G.map (fun row => (row.zipWith (· * ·) cs).sum)

private def hzConstEntry (t j : ℕ) : ℝ :=
  if j < t then 0 else 1

private def hzConstRow (q t : ℕ) : List ℝ :=
  (List.range q).map (hzConstEntry t)

private def hzConstMatrix (q n : ℕ) : List (List ℝ) :=
  (List.range n).map (hzConstRow q)

private lemma real_zipWith_mul_replicate_zero_sum (row : List ℝ) (n : ℕ) :
    (row.zipWith (· * ·) (List.replicate n (0 : ℝ))).sum = 0 := by
  induction n generalizing row with
  | zero =>
      cases row <;> rfl
  | succ n ih =>
      cases row with
      | nil => rfl
      | cons _ row =>
          rw [show n + 1 = Nat.succ n by rfl, List.replicate_succ]
          simp [ih row]

private lemma real_zipWith_mul_cons_replicate_zero_sum
    (row : List ℝ) (n : ℕ) :
    (row.zipWith (· * ·) (1 :: List.replicate n (0 : ℝ))).sum =
      row.headD 0 := by
  cases row with
  | nil => simp
  | cons _ row => simp [real_zipWith_mul_replicate_zero_sum]

private lemma headD_hzConstRow (n t : ℕ) :
    (hzConstRow (n + 1) t).headD 0 = if t = 0 then 1 else 0 := by
  by_cases ht : t = 0
  · simp [hzConstRow, hzConstEntry, List.head?_map, List.head?_range, ht]
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    simp [hzConstRow, hzConstEntry, List.head?_map, List.head?_range, ht, htpos]

private lemma realListAction_hzConstRow_delta (t n : ℕ) :
    ((hzConstRow (n + 1) t).zipWith (· * ·)
      (1 :: List.replicate n (0 : ℝ))).sum =
      if t = 0 then 1 else 0 := by
  rw [real_zipWith_mul_cons_replicate_zero_sum, headD_hzConstRow]

private lemma replicate_append_singleton_zero (n : ℕ) :
    List.replicate n (0 : ℝ) ++ [0] = List.replicate (n + 1) 0 := by
  simpa using
    (List.replicate_append_replicate (n := n) (m := 1) (a := (0 : ℝ)))

private lemma map_range_indicator_zero (n : ℕ) :
    (List.range (n + 1)).map (fun t => if t = 0 then (1 : ℝ) else 0) =
      1 :: List.replicate n 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1).succ by lia]
      rw [List.range_succ, List.map_append, ih]
      simp [replicate_append_singleton_zero]

private lemma realListAction_hzConstMatrix_delta (n : ℕ) :
    realListAction (hzConstMatrix (n + 1) (n + 2))
      (1 :: List.replicate n (0 : ℝ)) =
      1 :: List.replicate (n + 1) 0 := by
  simp only [realListAction, hzConstMatrix, List.map_map]
  change (List.range (n + 2)).map
      (fun t => ((hzConstRow (n + 1) t).zipWith (· * ·)
        (1 :: List.replicate n (0 : ℝ))).sum) =
      1 :: List.replicate (n + 1) 0
  rw [show n + 2 = n + 1 + 1 by lia]
  simpa [realListAction_hzConstRow_delta] using map_range_indicator_zero (n + 1)

private lemma coeff_zero_zipWith (row fs : List ℝ[X]) :
    ((row.zipWith (· * ·) fs).sum).coeff 0 =
      ((row.map (fun p => p.coeff 0)).zipWith (· * ·)
        (fs.map (fun p => p.coeff 0))).sum := by
  induction row generalizing fs with
  | nil =>
      simp
  | cons _ row ih =>
      cases fs with
      | nil => simp
      | cons _ fs => simp [ih, Polynomial.mul_coeff_zero]

private lemma coeff_zero_matPolyAction
    (G : List (List ℝ[X])) (fs : List ℝ[X]) :
    (matPolyAction G fs).map (fun p => p.coeff 0) =
      realListAction (G.map (fun row => row.map (fun p => p.coeff 0)))
        (fs.map (fun p => p.coeff 0)) := by
  simp [realListAction, matPolyAction, coeff_zero_zipWith]

private lemma coeff_zero_thresholdEntry_one_add_X (t j : ℕ) :
    (thresholdEntry t (1 + X : ℝ[X]) j).coeff 0 = hzConstEntry t j := by
  by_cases hlt : j < t
  · simp [thresholdEntry, hzConstEntry, hlt]
  · by_cases heq : j = t
    · simp [thresholdEntry, hzConstEntry, heq]
    · simp [thresholdEntry, hzConstEntry, hlt, heq]

private lemma coeff_zero_hzBinomialMatrix (q n : ℕ) :
    (hzBinomialMatrix q (hzBinomialThresholds n)).map
      (fun row => row.map (fun p => p.coeff 0)) =
      hzConstMatrix q n := by
  simp [hzBinomialMatrix, hzBinomialThresholds, hzBinomialRows, hzMatrix,
    thresholdMatrix, thresholdRow, coeff_zero_thresholdEntry_one_add_X,
    hzConstMatrix, hzConstRow]

private lemma coeff_zero_hzTerminalRow (q : ℕ) :
    (hzRow q 0 (1 + X)).map (fun p => p.coeff 0) =
      hzConstRow q 0 := by
  simp [hzRow, thresholdRow, hzConstRow, coeff_zero_thresholdEntry_one_add_X]

private lemma coeff_zero_hzTerminalPolynomial (q : ℕ) (fs : List ℝ[X]) :
    (hzTerminalPolynomial q fs).coeff 0 =
      ((hzConstRow q 0).zipWith (· * ·)
        (fs.map (fun p => p.coeff 0))).sum := by
  rw [hzTerminalPolynomial, coeff_zero_zipWith, coeff_zero_hzTerminalRow]

/-- The refined binomial Eulerian vector in the Haglund--Zhang recursion.

The vector has length `n + 1`.  The transition from `n` to `n + 1` has width
`n + 1` and `n + 2` threshold rows. -/
def hzBinomialRefined : ℕ → List ℝ[X]
  | 0 => [1]
  | n + 1 =>
      matPolyAction
        (hzBinomialMatrix (n + 1) (hzBinomialThresholds (n + 2)))
        (hzBinomialRefined n)

@[simp] theorem length_hzBinomialRefined (n : ℕ) :
    (hzBinomialRefined n).length = n + 1 := by
  induction n with
  | zero =>
      simp [hzBinomialRefined]
  | succ n =>
      simp [hzBinomialRefined]

@[simp] lemma mem_hzBinomialRefined_zero {f : ℝ[X]} :
    f ∈ hzBinomialRefined 0 ↔ f = 1 := by
  simp [hzBinomialRefined]

theorem coeff_zero_hzBinomialRefined (n : ℕ) :
    (hzBinomialRefined n).map (fun p => p.coeff 0) =
      1 :: List.replicate n 0 := by
  induction n with
  | zero =>
      simp [hzBinomialRefined]
  | succ n ih =>
      simp [hzBinomialRefined, coeff_zero_matPolyAction,
        coeff_zero_hzBinomialMatrix, ih, realListAction_hzConstMatrix_delta]

lemma hzBinomialRefined_zero_interlacing :
    IsInterlacingSeq0Nonneg (hzBinomialRefined 0) := by
  constructor
  · simp [hzBinomialRefined, IsInterlacingSeq0]
  · intro f hf
    have hf' : f = 1 := mem_hzBinomialRefined_zero.mp hf
    subst f
    exact hasNonnegCoeffs_one

lemma hzBinomialRefined_zero_splits :
    ∀ f ∈ hzBinomialRefined 0, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  intro f hf _
  have hf' : f = 1 := mem_hzBinomialRefined_zero.mp hf
  subst f
  exact ⟨one_ne_zero, Polynomial.Splits.one⟩

theorem hzBinomialRefined_interlacing_weak (n : ℕ) :
    IsInterlacingSeq0Nonneg (hzBinomialRefined n) ∧
      ∀ f ∈ hzBinomialRefined n, f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  induction n with
  | zero =>
      exact ⟨hzBinomialRefined_zero_interlacing, hzBinomialRefined_zero_splits⟩
  | succ n ih =>
      simpa [hzBinomialRefined] using
        haglund_zhang_binomial_eulerian_range_weak
          (q := n + 1) (n := n + 2) (fs := hzBinomialRefined n)
          (by simp)
          ih.1 ih.2

/-- Interlacing projection from the Haglund--Zhang refined-vector induction. -/
theorem hzBinomialRefined_interlaces (n : ℕ) :
    IsInterlacingSeq0Nonneg (hzBinomialRefined n) :=
  (hzBinomialRefined_interlacing_weak n).1

/-- Real-rootedness projection from the Haglund--Zhang refined-vector induction. -/
theorem hzBinomialRefined_realRooted (n : ℕ) :
    ∀ f ∈ hzBinomialRefined n, f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  (hzBinomialRefined_interlacing_weak n).2

/-- The terminal binomial Eulerian polynomial obtained from the refined vector. -/
def hzBinomialEulerianPolynomial (n : ℕ) : ℝ[X] :=
  hzTerminalPolynomial (n + 1) (hzBinomialRefined n)

@[simp] theorem coeff_zero_hzBinomialEulerianPolynomial (n : ℕ) :
    (hzBinomialEulerianPolynomial n).coeff 0 = 1 := by
  rw [hzBinomialEulerianPolynomial, coeff_zero_hzTerminalPolynomial,
    coeff_zero_hzBinomialRefined]
  simp [realListAction_hzConstRow_delta]

theorem hzBinomialEulerianPolynomial_ne_zero (n : ℕ) :
    hzBinomialEulerianPolynomial n ≠ 0 := by
  intro h
  have hcoeff := coeff_zero_hzBinomialEulerianPolynomial n
  rw [h] at hcoeff
  norm_num at hcoeff

theorem hzBinomialEulerianPolynomial_realRooted_of_ne
    (n : ℕ) (hne : hzBinomialEulerianPolynomial n ≠ 0) :
    hzBinomialEulerianPolynomial n ≠ 0 ∧
      (hzBinomialEulerianPolynomial n).Splits := by
  simpa [hzBinomialEulerianPolynomial] using
    haglund_zhang_terminal_polynomial_realRooted
      (q := n + 1) (fs := hzBinomialRefined n)
      (by simp)
      (hzBinomialRefined_interlaces n) (hzBinomialRefined_realRooted n)
      (by simpa [hzBinomialEulerianPolynomial] using hne)

theorem hzBinomialEulerianPolynomial_splits_of_ne
    (n : ℕ) (hne : hzBinomialEulerianPolynomial n ≠ 0) :
    (hzBinomialEulerianPolynomial n).Splits :=
  (hzBinomialEulerianPolynomial_realRooted_of_ne n hne).2

theorem hzBinomialEulerianPolynomial_realRooted (n : ℕ) :
    hzBinomialEulerianPolynomial n ≠ 0 ∧
      (hzBinomialEulerianPolynomial n).Splits :=
  hzBinomialEulerianPolynomial_realRooted_of_ne
    n (hzBinomialEulerianPolynomial_ne_zero n)

theorem hzBinomialEulerianPolynomial_splits (n : ℕ) :
    (hzBinomialEulerianPolynomial n).Splits :=
  (hzBinomialEulerianPolynomial_realRooted n).2

end Backend

/-! ### OEIS A046802 surface -/

/-- The recurrence-defined A046802 row family, represented by the
Haglund--Zhang binomial Eulerian polynomial.  Agreement with the external OEIS
table is intentionally a separate theorem for the generated sequence file. -/
abbrev A046802 (n : ℕ) : ℝ[X] :=
  Backend.hzBinomialEulerianPolynomial n

/-- The refined Haglund--Zhang vector used as the interlacing certificate for
`A046802`. -/
abbrev A046802Refined (n : ℕ) : List ℝ[X] :=
  Backend.hzBinomialRefined n

@[simp] theorem A046802_eq_hzBinomialEulerianPolynomial (n : ℕ) :
    A046802 n = Backend.hzBinomialEulerianPolynomial n := rfl

@[simp] theorem A046802Refined_eq_hzBinomialRefined (n : ℕ) :
    A046802Refined n = Backend.hzBinomialRefined n := rfl

@[simp] theorem coeff_zero_A046802 (n : ℕ) :
    (A046802 n).coeff 0 = 1 :=
  Backend.coeff_zero_hzBinomialEulerianPolynomial n

/-- Interlacing certificate for the Haglund--Zhang refinement behind A046802. -/
theorem A046802_interlaces (n : ℕ) :
    IsInterlacingSeq0Nonneg (A046802Refined n) :=
  Backend.hzBinomialRefined_interlaces n

/-- Real-rootedness certificate for each nonzero refined polynomial behind A046802. -/
theorem A046802_refined_realRooted (n : ℕ) :
    ∀ f ∈ A046802Refined n, f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  Backend.hzBinomialRefined_realRooted n

theorem A046802_ne_zero (n : ℕ) :
    A046802 n ≠ 0 := by
  intro h
  have hcoeff := coeff_zero_A046802 n
  rw [h] at hcoeff
  norm_num at hcoeff

theorem A046802_realRooted (n : ℕ) :
    A046802 n ≠ 0 ∧ (A046802 n).Splits :=
  Backend.hzBinomialEulerianPolynomial_realRooted n

theorem A046802_splits (n : ℕ) :
    (A046802 n).Splits :=
  (A046802_realRooted n).2

/-- Real-rootedness for the recurrence-defined A046802 family represented by
the Haglund--Zhang binomial Eulerian polynomial. -/
theorem oeisA046802_realRooted (n : ℕ) :
    A046802 n ≠ 0 ∧ (A046802 n).Splits :=
  A046802_realRooted n

/-- Tactic-facing theorem for the `rr_s_inversion_binomial_eulerian_sequence`
route. -/
theorem rr_s_inversion_binomial_eulerian_sequence (n : ℕ) :
    A046802 n ≠ 0 ∧ (A046802 n).Splits :=
  A046802_realRooted n

end OEIS

/-! ## Gustafsson--Solus Lemma 3.4 backend -/

namespace GustafssonSolus

/-! ### Finite-entry shape helpers -/

private lemma prec0_gs_quadratic_self {s t : ℝ} (hs : 0 < s) :
    Prec0 ((C s * X + C t) * X + X) ((C s * X + C t) * X + X) :=
  prec0_refl_of_isRealRooted (isRealRooted_affine_mul_X_add_X hs)

private lemma prec0_gs_X_quadratic {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 X ((C s * X + C t) * X + X) := by
  rw [affine_mul_X_add_X_eq]
  simpa using
    prec0_affine_to_X_mul_affine_of_cross
      (u := s) (v := t + 1) (U := 1) (V := 0)
      hs zero_lt_one (by nlinarith) (by positivity) le_rfl

private lemma prec0_gs_affine_add_X_quadratic
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + X) ((C s * X + C t) * X + X) := by
  rw [affine_mul_X_add_X_eq]
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact
    prec0_affine_to_X_mul_affine_of_cross
      (u := s) (v := t + 1) (U := s + 1) (V := t)
      hs (by positivity) (by nlinarith [hs, ht]) (by positivity) ht.le

private lemma prec0_gs_affine_quadratic {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t) ((C s * X + C t) * X + X) := by
  rw [affine_mul_X_add_X_eq]
  exact
    prec0_affine_to_X_mul_affine_of_cross
      (u := s) (v := t + 1) (U := s) (V := t)
      hs hs (by nlinarith [hs]) (by positivity) ht.le

private lemma prec0_gs_affine_add_one_quadratic
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + 1) ((C s * X + C t) * X + X) := by
  rw [affine_mul_X_add_X_eq]
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  exact
    prec0_affine_to_X_mul_affine_of_cross
      (u := s) (v := t + 1) (U := s) (V := t + 1)
      hs hs le_rfl (by nlinarith) (by nlinarith)

private lemma prec0_gs_affine_add_X_X {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + X) X := by
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  simpa using
    prec0_affine_linear_affine_linear_of_cross
      (u := s + 1) (v := t) (U := 1) (V := 0)
      (by positivity) zero_lt_one (by nlinarith [ht])

private lemma prec0_gs_affine_X {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t) X := by
  simpa using
    prec0_affine_linear_affine_linear_of_cross
      (u := s) (v := t) (U := 1) (V := 0)
      hs zero_lt_one (by nlinarith [ht])

private lemma prec0_gs_affine_add_one_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + 1) X := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  simpa using
    prec0_affine_linear_affine_linear_of_cross
      (u := s) (v := t + 1) (U := 1) (V := 0)
      hs zero_lt_one (by nlinarith [ht])

private lemma prec0_gs_affine_add_X_self {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + X) (C s * X + C t + X) := by
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact
    prec0_refl_of_isRealRooted
      (isRealRooted_affine_factor (s := s + 1) (t := t) (by positivity))

private lemma prec0_gs_affine_self {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t) (C s * X + C t) :=
  prec0_refl_of_isRealRooted (isRealRooted_affine_factor (s := s) (t := t) hs)

private lemma prec0_gs_affine_add_one_self {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + 1) (C s * X + C t + 1) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  exact
    prec0_refl_of_isRealRooted
      (isRealRooted_affine_factor (s := s) (t := t + 1) hs)

private lemma prec0_gs_X_X : Prec0 (X : ℝ[X]) X :=
  prec0_refl_of_isRealRooted isRealRooted_X

private lemma prec0_gs_one_one : Prec0 (1 : ℝ[X]) 1 := by simpa using prec0_C_C (1 : ℝ) (1 : ℝ)

private lemma prec0_gs_affine_affine_add_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t) (C s * X + C t + X) := by
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact
    prec0_affine_linear_affine_linear_of_cross
      (u := s) (v := t) (U := s + 1) (V := t)
      hs (by positivity) (by nlinarith [ht])

private lemma prec0_gs_affine_add_one_affine_add_X
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Prec0 (C s * X + C t + 1) (C s * X + C t + X) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  rw [show (C s * X + C t + X : ℝ[X]) = C (s + 1) * X + C t by grind]
  exact
    prec0_affine_linear_affine_linear_of_cross
      (u := s) (v := t + 1) (U := s + 1) (V := t)
      hs (by positivity) (by nlinarith [hs, ht])

private lemma prec0_gs_affine_add_one_affine {s t : ℝ} (hs : 0 < s) :
    Prec0 (C s * X + C t + 1) (C s * X + C t) := by
  rw [show (C s * X + C t + 1 : ℝ[X]) = C s * X + C (t + 1) by grind]
  exact
    prec0_affine_linear_affine_linear_of_cross
      (u := s) (v := t + 1) (U := s) (V := t)
      hs hs (by nlinarith [hs])

private def GS2x2EntryShape (a b c d : ℝ[X]) : Prop :=
  Threshold2x2EntryTuple a b c d 0 0 0 0 ∨
  Threshold2x2EntryTuple a b c d 0 0 X X ∨
  Threshold2x2EntryTuple a b c d 0 1 0 1 ∨
  Threshold2x2EntryTuple a b c d 0 1 X 0 ∨
  Threshold2x2EntryTuple a b c d 0 1 X 1 ∨
  Threshold2x2EntryTuple a b c d 0 1 X X ∨
  Threshold2x2EntryTuple a b c d 1 1 0 0 ∨
  Threshold2x2EntryTuple a b c d 1 1 0 1 ∨
  Threshold2x2EntryTuple a b c d 1 1 1 1 ∨
  Threshold2x2EntryTuple a b c d 1 1 X 0 ∨
  Threshold2x2EntryTuple a b c d 1 1 X 1 ∨
  Threshold2x2EntryTuple a b c d 1 1 X X ∨
  Threshold2x2EntryTuple a b c d X 0 X 0 ∨
  Threshold2x2EntryTuple a b c d X 0 X X ∨
  Threshold2x2EntryTuple a b c d X 1 X 0 ∨
  Threshold2x2EntryTuple a b c d X 1 X 1 ∨
  Threshold2x2EntryTuple a b c d X 1 X X ∨
  Threshold2x2EntryTuple a b c d X X X X

private lemma GS2x2EntryShape.has2x2 {a b c d : ℝ[X]}
    (h : GS2x2EntryShape a b c d) :
    Has2x2InterlacingProperty0 a b c d := by
  intro s t hs ht
  rcases h with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
  · simpa using prec0_zero_zero
  · simpa using prec0_gs_X_X
  · simpa using (prec0_zero_right (C s * X + C t + 1 : ℝ[X]))
  · simpa using prec0_gs_affine_X hs ht
  · simpa using prec0_gs_affine_add_one_X hs ht
  · simpa using prec0_gs_affine_add_X_X hs ht
  · simpa using prec0_gs_affine_self hs
  · simpa using prec0_gs_affine_add_one_affine hs
  · simpa using prec0_gs_affine_add_one_self hs
  · simpa using prec0_gs_affine_affine_add_X hs ht
  · simpa using prec0_gs_affine_add_one_affine_add_X hs ht
  · simpa using prec0_gs_affine_add_X_self hs
  · simpa using (prec0_zero_left (((C s * X + C t) * X + X : ℝ[X])))
  · simpa using prec0_gs_X_quadratic hs ht
  · simpa using prec0_gs_affine_quadratic hs ht
  · simpa using prec0_gs_affine_add_one_quadratic hs ht
  · simpa using prec0_gs_affine_add_X_quadratic hs ht
  · simpa using prec0_gs_quadratic_self hs

private lemma gsEntry_shape
    {t₁ t₂ j₁ j₂ : ℕ} {α₁ α₂ : ℝ[X]}
    (hα₁ : α₁ = 0 ∨ α₁ = 1)
    (hα₂ : α₂ = 0 ∨ α₂ = 1)
    (ht : t₁ ≤ t₂) (hj : j₁ ≤ j₂)
    (hcompat : t₁ = t₂ → α₁ = 0 → α₂ = 0) :
    GS2x2EntryShape
      (thresholdEntry t₁ α₁ j₁) (thresholdEntry t₁ α₁ j₂)
      (thresholdEntry t₂ α₂ j₁) (thresholdEntry t₂ α₂ j₂) := by
  rcases hα₁ with rfl | rfl <;> rcases hα₂ with rfl | rfl
  all_goals
    simp at hcompat
    unfold GS2x2EntryShape Threshold2x2EntryTuple
    simp only [thresholdEntry]
    split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
    all_goals try lia

/-- Validity data for the Gustafsson--Solus recursion rows.

The marker `1` encodes the row `g_i`, while marker `0` encodes
`g_i - f_{phi i}`.  The compatibility condition is the global form of the
paper's no-immediate-switch condition within an equal-threshold block. -/
structure GSData (rows : List (ℕ × ℝ[X])) : Prop where
  /-- Every diagonal marker is `0` or `1`. -/
  alpha_mem : ∀ p ∈ rows, p.2 = 0 ∨ p.2 = 1
  /-- Thresholds are nondecreasing down the rows. -/
  thresh_mono : ∀ i j : Fin rows.length, i ≤ j → (rows.get i).1 ≤ (rows.get j).1
  /-- Once a row with a fixed threshold deletes the diagonal term, later rows
  with the same threshold also delete it. -/
  compat : ∀ i j : Fin rows.length, i ≤ j → (rows.get i).1 = (rows.get j).1 →
    (rows.get i).2 = 0 → (rows.get j).2 = 0

lemma GSData.alpha_nonneg {rows : List (ℕ × ℝ[X])} (h : GSData rows) :
    ∀ p ∈ rows, HasNonnegCoeffs p.2 := by
  intro p hp
  rcases h.alpha_mem p hp with hα | hα <;> rw [hα]
  · exact hasNonnegCoeffs_zero
  · exact isNonnegLinearForm_hasNonnegCoeffs isNonnegLinearForm_one

/-! ### Paper-shaped row-choice wrapper -/

/-- Boolean encoding of the two Gustafsson--Solus row choices.

`false` means the row is `g_i`; `true` means the diagonal term is deleted, so
the row is `g_i - f_{phi i}`. -/
def gsChoiceMarker (delete : Bool) : ℝ[X] :=
  if delete then 0 else 1

@[simp] lemma gsChoiceMarker_false :
    gsChoiceMarker false = (1 : ℝ[X]) := rfl

@[simp] lemma gsChoiceMarker_true :
    gsChoiceMarker true = (0 : ℝ[X]) := rfl

@[simp] lemma gsChoiceMarker_eq_zero {delete : Bool} :
    gsChoiceMarker delete = (0 : ℝ[X]) ↔ delete = true := by
  cases delete <;> simp

/-- Gustafsson--Solus row data using a threshold and a Boolean deletion flag. -/
def gsChoiceRows (choices : List (ℕ × Bool)) : List (ℕ × ℝ[X]) :=
  choices.map (fun p => (p.1, gsChoiceMarker p.2))

/-- Matrix associated to Gustafsson--Solus threshold choices. -/
abbrev gsChoiceMatrix (q : ℕ) (choices : List (ℕ × Bool)) : List (List ℝ[X]) :=
  thresholdMatrix q (gsChoiceRows choices)

@[simp] lemma length_gsChoiceRows (choices : List (ℕ × Bool)) :
    (gsChoiceRows choices).length = choices.length := by
  simp [gsChoiceRows]

@[simp] lemma length_gsChoiceMatrix (q : ℕ) (choices : List (ℕ × Bool)) :
    (gsChoiceMatrix q choices).length = choices.length := by
  simp [gsChoiceMatrix]

lemma gsChoiceRows_data {choices : List (ℕ × Bool)}
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hdelete : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 = (choices.get j).1 →
      (choices.get i).2 = true → (choices.get j).2 = true) :
    GSData (gsChoiceRows choices) := by
  constructor
  · intro p hp
    simp only [gsChoiceRows, List.mem_map] at hp
    obtain ⟨p, _, rfl⟩ := hp
    cases p.2 <;> simp [gsChoiceMarker]
  · intro i j hij
    let i' : Fin choices.length := ⟨i.1, by simpa using i.2⟩
    let j' : Fin choices.length := ⟨j.1, by simpa using j.2⟩
    have hij' : i' ≤ j' := hij
    have hkey := hmono i' j' hij'
    simpa [gsChoiceRows, List.get_eq_getElem, i', j'] using hkey
  · intro i j hij heq hdel
    let i' : Fin choices.length := ⟨i.1, by simpa using i.2⟩
    let j' : Fin choices.length := ⟨j.1, by simpa using j.2⟩
    have hij' : i' ≤ j' := hij
    have heq' : (choices.get i').1 = (choices.get j').1 := by
      simpa [gsChoiceRows, List.get_eq_getElem, i', j'] using heq
    have hdel_marker : gsChoiceMarker (choices.get i').2 = 0 := by
      simpa [gsChoiceRows, List.get_eq_getElem, i'] using hdel
    have hdel' : (choices.get i').2 = true := by simpa using hdel_marker
    have hdelj := hdelete i' j' hij' heq' hdel'
    simpa [gsChoiceRows, List.get_eq_getElem, j', hdelj]

lemma gsChoice_delete_global_of_local {choices : List (ℕ × Bool)}
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hlocal : ∀ n (hn : n + 1 < choices.length),
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).1 =
        (choices.get ⟨n + 1, hn⟩).1 →
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).2 = true →
      (choices.get ⟨n + 1, hn⟩).2 = true) :
    ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 = (choices.get j).1 →
      (choices.get i).2 = true → (choices.get j).2 = true := by
  intro i j hij heq hdel
  have hconst : ∀ k (hik : i.1 ≤ k) (hkj : k ≤ j.1),
      (choices.get ⟨k, Nat.lt_of_le_of_lt hkj j.2⟩).1 =
        (choices.get i).1 := by
    intro k hik hkj
    let k' : Fin choices.length := ⟨k, Nat.lt_of_le_of_lt hkj j.2⟩
    have hik' : i ≤ k' := hik
    have hkj' : k' ≤ j := hkj
    have hle1 : (choices.get i).1 ≤ (choices.get k').1 := hmono i k' hik'
    have hle2 : (choices.get k').1 ≤ (choices.get i).1 := by
      have hkj_le : (choices.get k').1 ≤ (choices.get j).1 := hmono k' j hkj'
      rw [← heq] at hkj_le
      exact hkj_le
    exact le_antisymm hle2 hle1
  have hmain := Nat.le_induction (m := i.1)
    (P := fun n _ => ∀ hnj : n ≤ j.1,
      (choices.get ⟨n, Nat.lt_of_le_of_lt hnj j.2⟩).2 = true)
    (by
      intro _
      simpa using hdel)
    (by
      intro n hin ih hsuccj
      have hnle : n ≤ j.1 := Nat.le_of_succ_le hsuccj
      have hsucc_len : n + 1 < choices.length := Nat.lt_of_le_of_lt hsuccj j.2
      have hdeln : (choices.get ⟨n, Nat.lt_of_le_of_lt hnle j.2⟩).2 = true :=
        ih hnle
      have heq_step :
          (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hsucc_len⟩).1 =
            (choices.get ⟨n + 1, hsucc_len⟩).1 := by
        have hn_eq := hconst n hin hnle
        have hisucc : i.1 ≤ n + 1 := Nat.le_trans hin (Nat.le_succ n)
        have hsucc_eq := hconst (n + 1) hisucc hsuccj
        simpa using hn_eq.trans hsucc_eq.symm
      have hdeln' :
          (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hsucc_len⟩).2 =
            true := by
        simpa using hdeln
      exact hlocal n hsucc_len heq_step hdeln')
    j.1 hij
  simpa using hmain le_rfl

/-- The finite entrywise Gustafsson--Solus `2 x 2` threshold check. -/
def GSEntryHas2x2Statement : Prop :=
  ∀ {t₁ t₂ j₁ j₂ : ℕ} {α₁ α₂ : ℝ[X]},
    (α₁ = 0 ∨ α₁ = 1) →
    (α₂ = 0 ∨ α₂ = 1) →
    t₁ ≤ t₂ → j₁ ≤ j₂ →
    (t₁ = t₂ → α₁ = 0 → α₂ = 0) →
    Has2x2InterlacingProperty0
      (thresholdEntry t₁ α₁ j₁) (thresholdEntry t₁ α₁ j₂)
      (thresholdEntry t₂ α₂ j₁) (thresholdEntry t₂ α₂ j₂)

theorem gsEntry_has2x2 : GSEntryHas2x2Statement := by
  intro t₁ t₂ j₁ j₂ α₁ α₂ hα₁ hα₂ ht hj hcompat
  exact (gsEntry_shape hα₁ hα₂ ht hj hcompat).has2x2

lemma GSData.entry_has2x2 {q : ℕ} {rows : List (ℕ × ℝ[X])}
    (hrows : GSData rows) (hentry : GSEntryHas2x2Statement) :
    ∀ (i₁ i₂ : Fin rows.length) (j₁ j₂ : Fin q),
      i₁ ≤ i₂ → j₁ ≤ j₂ →
      Has2x2InterlacingProperty0
        (thresholdEntry (rows.get i₁).1 (rows.get i₁).2 j₁.1)
        (thresholdEntry (rows.get i₁).1 (rows.get i₁).2 j₂.1)
        (thresholdEntry (rows.get i₂).1 (rows.get i₂).2 j₁.1)
        (thresholdEntry (rows.get i₂).1 (rows.get i₂).2 j₂.1) := by
  intro i₁ i₂ j₁ j₂ hi hj
  exact hentry
    (hrows.alpha_mem (rows.get i₁) (List.get_mem rows i₁))
    (hrows.alpha_mem (rows.get i₂) (List.get_mem rows i₂))
    (hrows.thresh_mono i₁ i₂ hi)
    hj
    (hrows.compat i₁ i₂ hi)

/-- Gustafsson--Solus threshold-recursion backend, reduced to the finite
entrywise `2 x 2` threshold check. -/
theorem gustafsson_solus_interlacing_recursion_backend
    (hentry : GSEntryHas2x2Statement)
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : GSData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (thresholdMatrix q rows) fs) :=
  thresholdMatrix_preserves_interlacing_seq0_of_entry rows
    hrows.alpha_nonneg (hrows.entry_has2x2 hentry) fs hfs_len hfs

theorem gustafsson_solus_interlacing_recursion
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : GSData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (thresholdMatrix q rows) fs) :=
  gustafsson_solus_interlacing_recursion_backend gsEntry_has2x2
    rows hrows fs hfs_len hfs

theorem gustafsson_solus_interlacing_recursion_backend_weak
    (hentry : GSEntryHas2x2Statement)
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : GSData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (thresholdMatrix q rows) fs) ∧
      ∀ f ∈ matPolyAction (thresholdMatrix q rows) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  thresholdMatrix_preserves_interlacing_seq0_of_entry_weak rows
    hrows.alpha_nonneg (hrows.entry_has2x2 hentry) fs hfs_len hfs hfs_real

theorem gustafsson_solus_interlacing_recursion_weak
    {q : ℕ} (rows : List (ℕ × ℝ[X])) (hrows : GSData rows)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (thresholdMatrix q rows) fs) ∧
      ∀ f ∈ matPolyAction (thresholdMatrix q rows) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  gustafsson_solus_interlacing_recursion_backend_weak gsEntry_has2x2
    rows hrows fs hfs_len hfs hfs_real

theorem gustafsson_solus_interlacing_recursion_choices
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hdelete : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 = (choices.get j).1 →
      (choices.get i).2 = true → (choices.get j).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (gsChoiceMatrix q choices) fs) :=
  gustafsson_solus_interlacing_recursion (gsChoiceRows choices)
    (gsChoiceRows_data hmono hdelete) fs hfs_len hfs

theorem gustafsson_solus_interlacing_recursion_choices_weak
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hdelete : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 = (choices.get j).1 →
      (choices.get i).2 = true → (choices.get j).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (gsChoiceMatrix q choices) fs) ∧
      ∀ f ∈ matPolyAction (gsChoiceMatrix q choices) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  gustafsson_solus_interlacing_recursion_weak (gsChoiceRows choices)
    (gsChoiceRows_data hmono hdelete) fs hfs_len hfs hfs_real

theorem gustafsson_solus_interlacing_recursion_choices_weak_of_interlacing
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hdelete : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 = (choices.get j).1 →
      (choices.get i).2 = true → (choices.get j).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (gsChoiceMatrix q choices) fs) ∧
      ∀ f ∈ matPolyAction (gsChoiceMatrix q choices) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  have hfs_weak := weakData_of_isInterlacingSeqNonneg hfs
  exact gustafsson_solus_interlacing_recursion_choices_weak
    choices hmono hdelete fs hfs_len hfs_weak.1 hfs_weak.2

theorem gustafsson_solus_interlacing_recursion_local_choices
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hlocal : ∀ n (hn : n + 1 < choices.length),
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).1 =
        (choices.get ⟨n + 1, hn⟩).1 →
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).2 = true →
      (choices.get ⟨n + 1, hn⟩).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (gsChoiceMatrix q choices) fs) :=
  gustafsson_solus_interlacing_recursion_choices choices hmono
    (gsChoice_delete_global_of_local hmono hlocal) fs hfs_len hfs

theorem gustafsson_solus_interlacing_recursion_local_choices_weak
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hlocal : ∀ n (hn : n + 1 < choices.length),
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).1 =
        (choices.get ⟨n + 1, hn⟩).1 →
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).2 = true →
      (choices.get ⟨n + 1, hn⟩).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (matPolyAction (gsChoiceMatrix q choices) fs) ∧
      ∀ f ∈ matPolyAction (gsChoiceMatrix q choices) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  gustafsson_solus_interlacing_recursion_choices_weak choices hmono
    (gsChoice_delete_global_of_local hmono hlocal) fs hfs_len hfs hfs_real

theorem gustafsson_solus_interlacing_recursion_local_choices_weak_of_interlacing
    {q : ℕ} (choices : List (ℕ × Bool))
    (hmono : ∀ i j : Fin choices.length, i ≤ j → (choices.get i).1 ≤ (choices.get j).1)
    (hlocal : ∀ n (hn : n + 1 < choices.length),
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).1 =
        (choices.get ⟨n + 1, hn⟩).1 →
      (choices.get ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).2 = true →
      (choices.get ⟨n + 1, hn⟩).2 = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (matPolyAction (gsChoiceMatrix q choices) fs) ∧
      ∀ f ∈ matPolyAction (gsChoiceMatrix q choices) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  gustafsson_solus_interlacing_recursion_choices_weak_of_interlacing choices hmono
    (gsChoice_delete_global_of_local hmono hlocal) fs hfs_len hfs

/-- Paper-shaped finite-indexed Gustafsson--Solus row choices.

For `i : Fin (m + 1)`, `phi i` is the row threshold and `delete i` chooses
between `g_i` and `g_i - f_{phi i}`. -/
def gsPaperChoices (m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool) : List (ℕ × Bool) :=
  List.ofFn fun i => (phi i, delete i)

/-- The Gustafsson--Solus row polynomial attached to a single threshold and
row choice.  The Boolean convention is that `false` gives the row `g_i`, while
`true` gives the row `g_i - f_{phi i}`. -/
def gsRowPolynomial (q t : ℕ) (delete : Bool) (fs : List ℝ[X]) : ℝ[X] :=
  ((thresholdRow q t (gsChoiceMarker delete)).zipWith (· * ·) fs).sum

/-- The paper-shaped list of Gustafsson--Solus row polynomials. -/
def gsPaperPolynomials (q m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool) (fs : List ℝ[X]) : List ℝ[X] :=
  List.ofFn fun i => gsRowPolynomial q (phi i) (delete i) fs

@[simp] lemma length_gsPaperChoices (m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool) :
    (gsPaperChoices m phi delete).length = m + 1 := by
  simp [gsPaperChoices]

@[simp] lemma length_gsPaperPolynomials (q m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool) (fs : List ℝ[X]) :
    (gsPaperPolynomials q m phi delete fs).length = m + 1 := by
  simp [gsPaperPolynomials]

lemma get_gsPaperChoices (m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool)
    (i : Fin (gsPaperChoices m phi delete).length) :
    (gsPaperChoices m phi delete).get i =
      (phi (Fin.cast (length_gsPaperChoices m phi delete) i),
        delete (Fin.cast (length_gsPaperChoices m phi delete) i)) := by
  simpa [gsPaperChoices] using
    (List.get_ofFn (fun i : Fin (m + 1) => (phi i, delete i)) i)

@[simp] lemma matPolyAction_gsChoiceMatrix_gsPaperChoices
    (q m : ℕ) (phi : Fin (m + 1) → ℕ)
    (delete : Fin (m + 1) → Bool) (fs : List ℝ[X]) :
  matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs =
      gsPaperPolynomials q m phi delete fs := by
  simp [gsChoiceMatrix, gsChoiceRows, gsPaperChoices, gsPaperPolynomials,
    gsRowPolynomial, thresholdMatrix, matPolyAction, Function.comp_def]

private lemma fin_mono_of_adjacent {m : ℕ} {phi : Fin (m + 1) → ℕ}
    (hstep : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ) :
    ∀ i j : Fin (m + 1), i ≤ j → phi i ≤ phi j := by
  intro i j hij
  have hmain := Nat.le_induction (m := i.1)
    (P := fun n _ => ∀ hn : n < m + 1, phi i ≤ phi ⟨n, hn⟩)
    (by
      intro hn
      have hidx : (⟨i.1, hn⟩ : Fin (m + 1)) = i := by ext; rfl
      simp [hidx])
    (by
      intro n hin ih hsucc
      have hn : n < m + 1 := Nat.lt_of_succ_lt hsucc
      have hn_m : n < m := by lia
      have hle := ih hn
      have hstepn := hstep ⟨n, hn_m⟩
      have hleft : (⟨n, hn_m⟩ : Fin m).castSucc =
          (⟨n, hn⟩ : Fin (m + 1)) := by
        ext
        rfl
      have hright : (⟨n, hn_m⟩ : Fin m).succ =
          (⟨n + 1, hsucc⟩ : Fin (m + 1)) := by
        ext
        rfl
      rw [hleft, hright] at hstepn
      exact le_trans hle hstepn)
    j.1 hij
  exact hmain j.2

private lemma gsPaperChoices_mono_of_adjacent {m : ℕ}
    {phi : Fin (m + 1) → ℕ} {delete : Fin (m + 1) → Bool}
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ) :
    ∀ i j : Fin (gsPaperChoices m phi delete).length, i ≤ j →
      ((gsPaperChoices m phi delete).get i).1 ≤
        ((gsPaperChoices m phi delete).get j).1 := by
  intro i j hij
  have hi := get_gsPaperChoices m phi delete i
  have hj := get_gsPaperChoices m phi delete j
  let i' : Fin (m + 1) := Fin.cast (length_gsPaperChoices m phi delete) i
  let j' : Fin (m + 1) := Fin.cast (length_gsPaperChoices m phi delete) j
  have hij' : i' ≤ j' := hij
  have hmonoFin : phi i' ≤ phi j' :=
    fin_mono_of_adjacent hphi i' j' hij'
  calc
    ((gsPaperChoices m phi delete).get i).1 = phi i' := by rw [hi]
    _ ≤ phi j' := hmonoFin
    _ = ((gsPaperChoices m phi delete).get j).1 := by rw [hj]

private lemma gsPaperChoices_local_of_fin {m : ℕ}
    {phi : Fin (m + 1) → ℕ} {delete : Fin (m + 1) → Bool}
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true) :
    ∀ n (hn : n + 1 < (gsPaperChoices m phi delete).length),
      ((gsPaperChoices m phi delete).get
        ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).1 =
        ((gsPaperChoices m phi delete).get ⟨n + 1, hn⟩).1 →
      ((gsPaperChoices m phi delete).get
        ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩).2 = true →
      ((gsPaperChoices m phi delete).get ⟨n + 1, hn⟩).2 = true := by
  intro n hn heq hdel
  have hn_m : n < m := by simpa [length_gsPaperChoices] using hn
  let i : Fin m := ⟨n, hn_m⟩
  have hleft : (i.castSucc : Fin (m + 1)) =
      Fin.cast (length_gsPaperChoices m phi delete)
        ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩ := by
    ext
    rfl
  have hright : (i.succ : Fin (m + 1)) =
      Fin.cast (length_gsPaperChoices m phi delete) ⟨n + 1, hn⟩ := by
    ext
    rfl
  have hget_left := get_gsPaperChoices m phi delete
    ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩
  have hget_right := get_gsPaperChoices m phi delete ⟨n + 1, hn⟩
  have heq' : phi i.castSucc = phi i.succ := by
    rw [hget_left, hget_right] at heq
    rwa [hleft, hright]
  have hdel' : delete i.castSucc = true := by
    rw [hget_left] at hdel
    rwa [hleft]
  have hnext := hlocal i heq' hdel'
  rw [hget_right]
  rwa [hright] at hnext

/-- Gustafsson--Solus Lemma 3.4 in finite-indexed row-choice form.

The function `delete` uses the same convention as `gsChoiceMarker`: `false`
selects the row `g_i`, and `true` selects `g_i - f_{phi i}`. -/
theorem gustafsson_solus_interlacing_recursion_fin_choices
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs) :=
  gustafsson_solus_interlacing_recursion_local_choices (gsPaperChoices m phi delete)
    (gsPaperChoices_mono_of_adjacent hphi)
    (gsPaperChoices_local_of_fin hlocal) fs hfs_len hfs

theorem gustafsson_solus_interlacing_recursion_fin_choices_weak
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs) ∧
      ∀ f ∈ matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  gustafsson_solus_interlacing_recursion_local_choices_weak
    (gsPaperChoices m phi delete)
    (gsPaperChoices_mono_of_adjacent hphi)
    (gsPaperChoices_local_of_fin hlocal) fs hfs_len hfs hfs_real

theorem gustafsson_solus_interlacing_recursion_fin_choices_weak_of_interlacing
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs) ∧
      ∀ f ∈ matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  gustafsson_solus_interlacing_recursion_local_choices_weak_of_interlacing
    (gsPaperChoices m phi delete)
    (gsPaperChoices_mono_of_adjacent hphi)
    (gsPaperChoices_local_of_fin hlocal) fs hfs_len hfs

/-- Interlacing projection of the finite-indexed Gustafsson--Solus row-choice
form. -/
theorem gustafsson_solus_interlacing_recursion_fin_choices_interlaces
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg
      (matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs) :=
  (gustafsson_solus_interlacing_recursion_fin_choices_weak_of_interlacing
    phi delete hphi hlocal fs hfs_len hfs).1

/-- Real-rootedness projection of the finite-indexed Gustafsson--Solus
row-choice form. -/
theorem gustafsson_solus_interlacing_recursion_fin_choices_realRooted
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    ∀ f ∈ matPolyAction (gsChoiceMatrix q (gsPaperChoices m phi delete)) fs,
      f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  (gustafsson_solus_interlacing_recursion_fin_choices_weak_of_interlacing
    phi delete hphi hlocal fs hfs_len hfs).2

theorem gustafsson_solus_interlacing_recursion_fin_polynomials_weak
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeq0Nonneg fs)
    (hfs_real : ∀ f ∈ fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits)) :
    IsInterlacingSeq0Nonneg (gsPaperPolynomials q m phi delete fs) ∧
      ∀ f ∈ gsPaperPolynomials q m phi delete fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  simpa using
    gustafsson_solus_interlacing_recursion_fin_choices_weak
      phi delete hphi hlocal fs hfs_len hfs hfs_real

theorem gustafsson_solus_interlacing_recursion_fin_polynomials_weak_of_interlacing
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (gsPaperPolynomials q m phi delete fs) ∧
      ∀ f ∈ gsPaperPolynomials q m phi delete fs,
        f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
  simpa using
    gustafsson_solus_interlacing_recursion_fin_choices_weak_of_interlacing
      phi delete hphi hlocal fs hfs_len hfs

/-- Interlacing projection of the paper-shaped Gustafsson--Solus polynomial-list
recursion. -/
theorem gustafsson_solus_interlacing_recursion_fin_polynomials_interlaces
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (gsPaperPolynomials q m phi delete fs) :=
  by
    simpa using
      gustafsson_solus_interlacing_recursion_fin_choices_interlaces
        phi delete hphi hlocal fs hfs_len hfs

/-- Gustafsson--Solus Lemma 3.4 in paper-shaped finite-indexed polynomial-list
form.  The output list has entries `g_i` or `g_i - f_{phi i}` according to
`delete`. -/
theorem gustafsson_solus_interlacing_recursion_fin_polynomials
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    IsInterlacingSeq0Nonneg (gsPaperPolynomials q m phi delete fs) :=
  gustafsson_solus_interlacing_recursion_fin_polynomials_interlaces
    phi delete hphi hlocal fs hfs_len hfs

/-- Real-rootedness projection of the paper-shaped Gustafsson--Solus
polynomial-list recursion. -/
theorem gustafsson_solus_interlacing_recursion_fin_polynomials_realRooted
    {q m : ℕ} (phi : Fin (m + 1) → ℕ) (delete : Fin (m + 1) → Bool)
    (hphi : ∀ i : Fin m, phi i.castSucc ≤ phi i.succ)
    (hlocal : ∀ i : Fin m, phi i.castSucc = phi i.succ →
      delete i.castSucc = true → delete i.succ = true)
    (fs : List ℝ[X]) (hfs_len : fs.length = q)
    (hfs : IsInterlacingSeqNonneg fs) :
    ∀ f ∈ gsPaperPolynomials q m phi delete fs, f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  by
    simpa using
      gustafsson_solus_interlacing_recursion_fin_choices_realRooted
        phi delete hphi hlocal fs hfs_len hfs

end GustafssonSolus

end RealRooted
