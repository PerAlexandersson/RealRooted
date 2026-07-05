import RealRooted.VeroneseSection

open Polynomial Matrix

noncomputable section

namespace RealRooted

/-!
# Hurwitz matrix criterion interface

This file records checked interface lemmas for the Hurwitz-matrix worker.  The
classical analytic theorem is not proved here; the point is to expose the exact
finite-minor statement needed by the existing `VeroneseSection` route.
-/

@[simp] theorem hurwitz_coeff_even_row (p : ℝ[X]) (i j : ℕ) :
    hurwitz (fun k => p.coeff k) (2 * i) j = toeplitz (fun k => p.coeff (2 * k + 1)) i j := by
  simp [hurwitz]

@[simp] theorem hurwitz_coeff_odd_row (p : ℝ[X]) (i j : ℕ) :
    hurwitz (fun k => p.coeff k) (2 * i + 1) j = toeplitz (fun k => p.coeff (2 * k)) i j := by
  simp [hurwitz, show (2 * i + 1) / 2 = i by lia]

/-! ### Row-parity entry formulas for arbitrary coefficient sequences

The polynomial-specific apply lemmas below are the `c = p.coeff` special cases
of these general facts, which describe every entry of `hurwitz c` by row
parity. -/

/-- Even-row entry of the Hurwitz matrix of an arbitrary coefficient sequence. -/
theorem hurwitz_even_row_apply (c : ℕ → ℝ) (i j : ℕ) :
    hurwitz c (2 * i) j = if j ≤ i then c (2 * (i - j) + 1) else 0 := by
  rw [hurwitz]
  simp only [Matrix.of_apply]
  rw [if_pos (by lia : (2 * i) % 2 = 0),
    show (2 * i) / 2 = i by lia, toeplitz_apply]

/-- Odd-row entry of the Hurwitz matrix of an arbitrary coefficient sequence. -/
theorem hurwitz_odd_row_apply (c : ℕ → ℝ) (i j : ℕ) :
    hurwitz c (2 * i + 1) j = if j ≤ i then c (2 * (i - j)) else 0 := by
  rw [hurwitz]
  simp only [Matrix.of_apply]
  rw [if_neg (by lia : ¬ (2 * i + 1) % 2 = 0),
    show (2 * i + 1) / 2 = i by lia, toeplitz_apply]

/-- Every Hurwitz-matrix entry above the staircase vanishes. -/
theorem hurwitz_apply_eq_zero_of_lt (c : ℕ → ℝ) {i j : ℕ} (h : i < 2 * j) :
    hurwitz c i j = 0 := by
  rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m = 2 * m by ring, hurwitz_even_row_apply, if_neg (by lia)]
  · subst hm
    rw [hurwitz_odd_row_apply, if_neg (by lia)]

theorem hurwitz_coeff_even_row_apply (p : ℝ[X]) (i j : ℕ) :
    hurwitz (fun k => p.coeff k) (2 * i) j =
      if j ≤ i then p.coeff (2 * (i - j) + 1) else 0 :=
  hurwitz_even_row_apply (fun k => p.coeff k) i j

theorem hurwitz_coeff_odd_row_apply (p : ℝ[X]) (i j : ℕ) :
    hurwitz (fun k => p.coeff k) (2 * i + 1) j =
      if j ≤ i then p.coeff (2 * (i - j)) else 0 :=
  hurwitz_odd_row_apply (fun k => p.coeff k) i j

/-! ### Odd/even Toeplitz submatrices of a Hurwitz matrix -/

/-- The even rows of a Hurwitz matrix form the Toeplitz matrix for the odd
subsequence of coefficients. -/
theorem hurwitz_submatrix_even_eq_toeplitz (c : ℕ → ℝ) :
    (hurwitz c).submatrix (fun i => 2 * i) id = toeplitz (fun n => c (2 * n + 1)) := by
  ext i j
  simp only [Matrix.submatrix_apply, id_eq]
  rw [hurwitz_even_row_apply, toeplitz_apply]

/-- The odd rows of a Hurwitz matrix form the Toeplitz matrix for the even
subsequence of coefficients. -/
theorem hurwitz_submatrix_odd_eq_toeplitz (c : ℕ → ℝ) :
    (hurwitz c).submatrix (fun i => 2 * i + 1) id = toeplitz (fun n => c (2 * n)) := by
  ext i j
  simp only [Matrix.submatrix_apply, id_eq]
  rw [hurwitz_odd_row_apply, toeplitz_apply]

/-- Total nonnegativity of a Hurwitz matrix implies that the odd coefficient
subsequence is Pólya-frequency. -/
theorem hurwitz_isPolyaFreqSeq_odd {c : ℕ → ℝ}
    (hc : (hurwitz c).IsTotallyNonneg) :
    IsPolyaFreqSeq (fun n => c (2 * n + 1)) := by
  rw [IsPolyaFreqSeq, ← hurwitz_submatrix_even_eq_toeplitz]
  exact hc.submatrix (by intro i j hij; lia) strictMono_id

/-- Total nonnegativity of a Hurwitz matrix implies that the even coefficient
subsequence is Pólya-frequency. -/
theorem hurwitz_isPolyaFreqSeq_even {c : ℕ → ℝ}
    (hc : (hurwitz c).IsTotallyNonneg) :
    IsPolyaFreqSeq (fun n => c (2 * n)) := by
  rw [IsPolyaFreqSeq, ← hurwitz_submatrix_odd_eq_toeplitz]
  exact hc.submatrix (strictMono_nat_of_lt_succ fun _ => by lia) strictMono_id

/-- Unfolded finite-minor form of
`HurwitzStableToMatrixTotallyNonnegativeStatement`.

This is the statement to target if one proves the classical theorem directly
from determinant formulas: every finite minor of the row-oriented Hurwitz
matrix attached to a Hurwitz-stable polynomial is nonnegative. -/
def HurwitzStableToHurwitzMatrixMinorsStatement : Prop :=
  ∀ {p : ℝ[X]}, IsHurwitzStable p → (hurwitz p.coeff).IsTotallyNonneg

theorem hurwitzStableToMatrixTotallyNonnegativeStatement_iff_minors :
    HurwitzStableToMatrixTotallyNonnegativeStatement ↔
      HurwitzStableToHurwitzMatrixMinorsStatement :=
  Iff.rfl

/-- Reverse direction of the classical total-nonnegativity criterion, kept as a
separate interface because the current Veronese route only needs the forward
direction. -/
def HurwitzMatrixTotallyNonnegativeToStableStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄, (hurwitz p.coeff).IsTotallyNonneg → IsHurwitzStable p

/-- The converse Hurwitz-matrix criterion gives the converse odd/even Lace
bridge by the explicit Hurwitz/Lace matrix identity. -/
theorem fullyInterlacingPairToHurwitzOddEvenStable_of_matrixTNN
    (hMatrix : HurwitzMatrixTotallyNonnegativeToStableStatement) :
    FullyInterlacingPairToHurwitzOddEvenStableStatement :=
  fun {p q} hfull =>
    hMatrix
      ((hurwitzMatrixTotallyNonnegative_oddEvenPolynomial_iff_fullyInterlacingPair p q).2
        hfull)

/-- Full weak Hurwitz-matrix criterion in the coefficient-nonnegative
convention used in this project. -/
def HurwitzMatrixCriterionStatement : Prop :=
  HurwitzStableToMatrixTotallyNonnegativeStatement ∧
    HurwitzMatrixTotallyNonnegativeToStableStatement

theorem hurwitzStableToMatrixTotallyNonnegative_of_criterion
    (h : HurwitzMatrixCriterionStatement) :
    HurwitzStableToMatrixTotallyNonnegativeStatement :=
  h.1

theorem hurwitzStableToHurwitzMatrixMinors_of_criterion
    (h : HurwitzMatrixCriterionStatement) :
    HurwitzStableToHurwitzMatrixMinorsStatement :=
  hurwitzStableToMatrixTotallyNonnegativeStatement_iff_minors.1 h.1

theorem hurwitzMatrixTotallyNonnegativeToStable_of_criterion
    (h : HurwitzMatrixCriterionStatement) :
    HurwitzMatrixTotallyNonnegativeToStableStatement :=
  h.2

theorem fullyInterlacingPairToHurwitzOddEvenStable_of_criterion
    (h : HurwitzMatrixCriterionStatement) :
    FullyInterlacingPairToHurwitzOddEvenStableStatement :=
  fullyInterlacingPairToHurwitzOddEvenStable_of_matrixTNN
    (hurwitzMatrixTotallyNonnegativeToStable_of_criterion h)

theorem hurwitzOddEvenToFullyInterlacingPair_of_matrixMinors
    (h : HurwitzStableToHurwitzMatrixMinorsStatement) :
    HurwitzOddEvenToFullyInterlacingPairStatement :=
  hurwitzOddEvenToFullyInterlacingPair_of_matrixTNN
    (hurwitzStableToMatrixTotallyNonnegativeStatement_iff_minors.2 h)

theorem hurwitzOddEvenToFullyInterlacingPair_of_criterion
    (h : HurwitzMatrixCriterionStatement) :
    HurwitzOddEvenToFullyInterlacingPairStatement :=
  hurwitzOddEvenToFullyInterlacingPair_of_matrixMinors
    (hurwitzStableToHurwitzMatrixMinors_of_criterion h)

/-! ### Entrywise Hadamard structure of Hurwitz matrices

The coefficientwise Hadamard product of two polynomials corresponds, at the
level of Hurwitz matrices, to the entrywise product of the two Hurwitz
matrices.  Every entry of `hurwitz c` is either `0` or a single coefficient
`c k`, so replacing `c` by the pointwise product `fun n => a n * b n`
multiplies each entry by the corresponding entry of the other matrix. -/

/-- Entrywise product identity for Hurwitz matrices.  The Hurwitz matrix of a
coefficientwise product of sequences agrees, entrywise, with the product of
the two Hurwitz matrices. -/
theorem hurwitz_mul_entrywise (a b : ℕ → ℝ) (i j : ℕ) :
    hurwitz (fun n => a n * b n) i j = hurwitz a i j * hurwitz b i j := by
  unfold hurwitz toeplitz
  by_cases hi : i % 2 = 0 <;>
    simp only [hi, Matrix.of_apply, if_true, if_false] <;>
      split <;> simp

/-- Matrix form of `hurwitz_mul_entrywise`: the Hurwitz matrix of a
coefficientwise product is the entrywise product of the two Hurwitz matrices. -/
theorem hurwitz_mul_entrywise_matrix (a b : ℕ → ℝ) :
    hurwitz (fun n => a n * b n) =
      Matrix.of (fun i j => hurwitz a i j * hurwitz b i j) := by
  ext i j
  simp only [Matrix.of_apply]
  exact hurwitz_mul_entrywise a b i j

/-- Pure-matrix combinatorial core of Garloff--Wagner Theorem 1.

This is the deep leaf of the reduction, stripped of analytic and polynomial
content: the entrywise product of two totally nonnegative Hurwitz matrices is
again totally nonnegative.  This is special to the Hurwitz block-Toeplitz
structure; the entrywise product of arbitrary totally nonnegative matrices is
not totally nonnegative in general. -/
def HurwitzMatrixSchurProductTNStatement : Prop :=
  ∀ {a b : ℕ → ℝ},
    (hurwitz a).IsTotallyNonneg →
    (hurwitz b).IsTotallyNonneg →
    (Matrix.of fun i j => hurwitz a i j * hurwitz b i j).IsTotallyNonneg

/-! ### Low-order cases of the Schur-product core -/

/-- Every entry of the entrywise product of two totally nonnegative Hurwitz
matrices is nonnegative.  This is the `1 × 1` minor case of
`HurwitzMatrixSchurProductTNStatement`. -/
theorem hurwitz_schurProduct_entry_nonneg {a b : ℕ → ℝ}
    (ha : (hurwitz a).IsTotallyNonneg) (hb : (hurwitz b).IsTotallyNonneg)
    (i j : ℕ) :
    0 ≤ (Matrix.of fun i j => hurwitz a i j * hurwitz b i j) i j := by
  simp only [Matrix.of_apply]
  exact mul_nonneg (ha.nonneg i j) (hb.nonneg i j)

/-- Every `2 × 2` minor of the entrywise product of two totally nonnegative
Hurwitz matrices is nonnegative.  This is the general two-by-two Hadamard minor
lemma specialized to Hurwitz matrices. -/
theorem hurwitz_schurProduct_det_fin_two {a b : ℕ → ℝ}
    (ha : (hurwitz a).IsTotallyNonneg) (hb : (hurwitz b).IsTotallyNonneg)
    {rows cols : Fin 2 → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols) :
    0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det :=
  ha.hadamard_det_fin_two hb hrows hcols

/-! ### The `3 × 3` minor case: structural zero patterns -/

/-- Entry of the entrywise Hurwitz product vanishes above the staircase. -/
theorem hurwitz_schurProduct_apply_eq_zero_of_lt (a b : ℕ → ℝ) {i j : ℕ}
    (h : i < 2 * j) :
    (Matrix.of fun i j => hurwitz a i j * hurwitz b i j) i j = 0 := by
  simp only [Matrix.of_apply, hurwitz_apply_eq_zero_of_lt a h, zero_mul]

/-- Structural vanishing of a `3 × 3` Hadamard minor of two Hurwitz matrices.

If the staircase condition `2 * cols l ≤ rows l` fails for some index `l`, then
monotonicity of the selected rows and columns forces a top-right zero block
large enough to make the determinant vanish. -/
theorem hurwitz_schurProduct_det_fin_three_of_band_fail {a b : ℕ → ℝ}
    {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (l : Fin 3) (hl : rows l < 2 * cols l) :
    ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det = 0 := by
  have hr01 : rows 0 ≤ rows 1 := hrows.monotone (by decide)
  have hr12 : rows 1 ≤ rows 2 := hrows.monotone (by decide)
  have hr02 : rows 0 ≤ rows 2 := hrows.monotone (by decide)
  have hc01 : cols 0 ≤ cols 1 := hcols.monotone (by decide)
  have hc12 : cols 1 ≤ cols 2 := hcols.monotone (by decide)
  have hc02 : cols 0 ≤ cols 2 := hcols.monotone (by decide)
  rw [Matrix.det_fin_three]
  simp only [Matrix.submatrix_apply, Matrix.of_apply]
  fin_cases l <;> simp only [Fin.isValue] at hl ⊢
  · rw [hurwitz_apply_eq_zero_of_lt a (by lia : rows 0 < 2 * cols 0),
      hurwitz_apply_eq_zero_of_lt a (by lia : rows 0 < 2 * cols 1),
      hurwitz_apply_eq_zero_of_lt a (by lia : rows 0 < 2 * cols 2)]
    ring
  · rw [hurwitz_apply_eq_zero_of_lt a (by lia : rows 0 < 2 * cols 1),
      hurwitz_apply_eq_zero_of_lt a (by lia : rows 0 < 2 * cols 2),
      hurwitz_apply_eq_zero_of_lt a (by lia : rows 1 < 2 * cols 1),
      hurwitz_apply_eq_zero_of_lt a (by lia : rows 1 < 2 * cols 2)]
    ring
  · rw [hurwitz_apply_eq_zero_of_lt a (by lia : rows 0 < 2 * cols 2),
      hurwitz_apply_eq_zero_of_lt a (by lia : rows 1 < 2 * cols 2),
      hurwitz_apply_eq_zero_of_lt a (by lia : rows 2 < 2 * cols 2)]
    ring

/-- Nonnegativity form of the structural band-fail `3 × 3` case. -/
theorem hurwitz_schurProduct_det_fin_three_nonneg_of_band_fail {a b : ℕ → ℝ}
    {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (l : Fin 3) (hl : rows l < 2 * cols l) :
    0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det := by
  rw [hurwitz_schurProduct_det_fin_three_of_band_fail hrows hcols l hl]

/-- In-band `3 × 3` core of the Hurwitz Schur-product theorem.

Together with `hurwitz_schurProduct_det_fin_three_nonneg_of_band_fail`, this
is equivalent to the full `3 × 3` case.  The condition
`2 * cols l ≤ rows l` says that every selected row/column pair lies in the
nonzero staircase of a Hurwitz matrix. -/
def HurwitzMatrixSchurProductDetFinThreeInBandStatement : Prop :=
  ∀ {a b : ℕ → ℝ},
    (hurwitz a).IsTotallyNonneg →
    (hurwitz b).IsTotallyNonneg →
    ∀ {rows cols : Fin 3 → ℕ},
      StrictMono rows →
      StrictMono cols →
      (∀ l : Fin 3, 2 * cols l ≤ rows l) →
      0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det

/-- Full `3 × 3` Hurwitz Schur-product minor from the in-band core.

The out-of-band case is already structural: if some `rows l < 2 * cols l`,
then the determinant is zero by `hurwitz_schurProduct_det_fin_three_of_band_fail`.
-/
theorem hurwitz_schurProduct_det_fin_three
    (hInBand : HurwitzMatrixSchurProductDetFinThreeInBandStatement)
    {a b : ℕ → ℝ}
    (ha : (hurwitz a).IsTotallyNonneg) (hb : (hurwitz b).IsTotallyNonneg)
    {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols) :
    0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det := by
  by_cases hfail : ∃ l : Fin 3, rows l < 2 * cols l
  · rcases hfail with ⟨l, hl⟩
    exact hurwitz_schurProduct_det_fin_three_nonneg_of_band_fail hrows hcols l hl
  · have hband : ∀ l : Fin 3, 2 * cols l ≤ rows l := by
      intro l
      exact not_lt.mp (by
        intro hl
        exact hfail ⟨l, hl⟩)
    exact hInBand ha hb hrows hcols hband

/-- Every minor of size at most two of the entrywise product of two totally
nonnegative Hurwitz matrices is nonnegative.  This packages the complete
low-order part of `HurwitzMatrixSchurProductTNStatement`; the first remaining
case is the genuinely Hurwitz-specific `3 × 3` minor. -/
theorem hurwitz_schurProduct_det_of_card_le_two {a b : ℕ → ℝ}
    (ha : (hurwitz a).IsTotallyNonneg) (hb : (hurwitz b).IsTotallyNonneg)
    {n : ℕ} {rows cols : Fin n → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hn : n ≤ 2) :
    0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det :=
  ha.hadamard_det_of_card_le_two hb hrows hcols hn

/-- Every minor of size at most three of the entrywise product of two totally
nonnegative Hurwitz matrices is nonnegative, assuming the in-band `3 × 3`
Hurwitz core. -/
theorem hurwitz_schurProduct_det_of_card_le_three
    (hInBand : HurwitzMatrixSchurProductDetFinThreeInBandStatement)
    {a b : ℕ → ℝ}
    (ha : (hurwitz a).IsTotallyNonneg) (hb : (hurwitz b).IsTotallyNonneg)
    {n : ℕ} {rows cols : Fin n → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hn : n ≤ 3) :
    0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det := by
  by_cases hn2 : n ≤ 2
  · exact hurwitz_schurProduct_det_of_card_le_two ha hb hrows hcols hn2
  · have hn3 : n = 3 := by
      lia
    subst n
    exact hurwitz_schurProduct_det_fin_three hInBand ha hb hrows hcols

/-- In-band entry formula: on the nonzero staircase `2 * j ≤ i`, every Hurwitz
matrix entry is a single coefficient. -/
theorem hurwitz_apply_of_band (c : ℕ → ℝ) {i j : ℕ} (h : 2 * j ≤ i) :
    hurwitz c i j = c ((if i % 2 = 0 then i + 1 else i - 1) - 2 * j) := by
  rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m = 2 * m by ring, hurwitz_even_row_apply,
      if_pos (by lia : j ≤ m), if_pos (by lia : (2 * m) % 2 = 0)]
    congr 1
    lia
  · subst hm
    rw [hurwitz_odd_row_apply, if_pos (by lia : j ≤ m),
      if_neg (by lia : ¬ (2 * m + 1) % 2 = 0)]
    congr 1
    lia

/-- `StrictMono` for a two-element index vector. -/
private theorem strictMono_pair {x y : ℕ} (hxy : x < y) :
    StrictMono ![x, y] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- Triangular reduction along the top row.  If the top selected row lies below
the staircase of the middle column, then the two entries to the right of the
top-left corner vanish and the determinant reduces to a `2 × 2` Hadamard minor. -/
theorem hurwitz_schurProduct_det_fin_three_of_row0_below {a b : ℕ → ℝ}
    (ha : (hurwitz a).IsTotallyNonneg) (hb : (hurwitz b).IsTotallyNonneg)
    {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (h : rows 0 < 2 * cols 1) :
    0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det := by
  have hc12 : cols 1 < cols 2 := hcols (by decide)
  have hr12 : rows 1 < rows 2 := hrows (by decide)
  have h2 : 0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix
      ![rows 1, rows 2] ![cols 1, cols 2]).det :=
    ha.hadamard_det_fin_two hb (strictMono_pair hr12) (strictMono_pair hc12)
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h2
  have hM00 : 0 ≤ hurwitz a (rows 0) (cols 0) * hurwitz b (rows 0) (cols 0) :=
    mul_nonneg (ha.nonneg _ _) (hb.nonneg _ _)
  rw [Matrix.det_fin_three]
  simp only [Matrix.submatrix_apply, Matrix.of_apply]
  rw [hurwitz_apply_eq_zero_of_lt a h,
    hurwitz_apply_eq_zero_of_lt a (by lia : rows 0 < 2 * cols 2)]
  nlinarith [mul_nonneg hM00 h2]

/-- Triangular reduction along the right column.  If the middle selected row lies
below the staircase of the last column, then the two entries above the
bottom-right corner vanish and the determinant reduces to a `2 × 2` Hadamard
minor. -/
theorem hurwitz_schurProduct_det_fin_three_of_row1_below {a b : ℕ → ℝ}
    (ha : (hurwitz a).IsTotallyNonneg) (hb : (hurwitz b).IsTotallyNonneg)
    {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (h : rows 1 < 2 * cols 2) :
    0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det := by
  have hc01 : cols 0 < cols 1 := hcols (by decide)
  have hr01 : rows 0 < rows 1 := hrows (by decide)
  have h2 : 0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix
      ![rows 0, rows 1] ![cols 0, cols 1]).det :=
    ha.hadamard_det_fin_two hb (strictMono_pair hr01) (strictMono_pair hc01)
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h2
  have hM22 : 0 ≤ hurwitz a (rows 2) (cols 2) * hurwitz b (rows 2) (cols 2) :=
    mul_nonneg (ha.nonneg _ _) (hb.nonneg _ _)
  rw [Matrix.det_fin_three]
  simp only [Matrix.submatrix_apply, Matrix.of_apply]
  rw [hurwitz_apply_eq_zero_of_lt a h,
    hurwitz_apply_eq_zero_of_lt a (by lia : rows 0 < 2 * cols 2)]
  nlinarith [mul_nonneg hM22 h2]

/-- Refined in-band `3 × 3` Hurwitz Schur-product core after the two triangular
reductions have been removed.  The remaining case has
`2 * cols 1 ≤ rows 0` and `2 * cols 2 ≤ rows 1`, so the top `2 × 3` block lies
on the nonzero staircase. -/
def HurwitzMatrixSchurProductDetFinThreeCoreStatement : Prop :=
  ∀ {a b : ℕ → ℝ},
    (hurwitz a).IsTotallyNonneg →
    (hurwitz b).IsTotallyNonneg →
    ∀ {rows cols : Fin 3 → ℕ},
      StrictMono rows →
      StrictMono cols →
      (∀ l : Fin 3, 2 * cols l ≤ rows l) →
      2 * cols 1 ≤ rows 0 →
      2 * cols 2 ≤ rows 1 →
      0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det

/-- The original in-band `3 × 3` core implies the refined triangular-free core. -/
theorem hurwitzMatrixSchurProductDetFinThreeCore_of_inBand
    (hInBand : HurwitzMatrixSchurProductDetFinThreeInBandStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreStatement := by
  intro a b ha hb rows cols hrows hcols hband _h01 _h12
  exact hInBand ha hb hrows hcols hband

/-- The refined triangular-free core implies the original in-band `3 × 3` core. -/
theorem hurwitzMatrixSchurProductDetFinThreeInBand_of_core
    (hcore : HurwitzMatrixSchurProductDetFinThreeCoreStatement) :
    HurwitzMatrixSchurProductDetFinThreeInBandStatement := by
  intro a b ha hb rows cols hrows hcols hband
  by_cases h0 : rows 0 < 2 * cols 1
  · exact hurwitz_schurProduct_det_fin_three_of_row0_below ha hb hrows hcols h0
  · by_cases h1 : rows 1 < 2 * cols 2
    · exact hurwitz_schurProduct_det_fin_three_of_row1_below ha hb hrows hcols h1
    · exact hcore ha hb hrows hcols hband (by lia) (by lia)

/-- The in-band `3 × 3` Hurwitz Schur-product core is equivalent to its
triangular-free refinement. -/
theorem hurwitzMatrixSchurProductDetFinThreeInBand_iff_core :
    HurwitzMatrixSchurProductDetFinThreeInBandStatement ↔
      HurwitzMatrixSchurProductDetFinThreeCoreStatement :=
  ⟨hurwitzMatrixSchurProductDetFinThreeCore_of_inBand,
    hurwitzMatrixSchurProductDetFinThreeInBand_of_core⟩

/-- Low-order, size-`≤ 3`, form of the Hurwitz matrix Schur-product core. -/
def HurwitzMatrixSchurProductDetLeThreeStatement : Prop :=
  ∀ {a b : ℕ → ℝ},
    (hurwitz a).IsTotallyNonneg →
    (hurwitz b).IsTotallyNonneg →
    ∀ {n : ℕ} {rows cols : Fin n → ℕ},
      StrictMono rows →
      StrictMono cols →
      n ≤ 3 →
      0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det

/-- The isolated in-band `3 × 3` core implies the low-order, size-`≤ 3`,
Hurwitz matrix Schur-product statement. -/
theorem hurwitzMatrixSchurProductDetLeThree_of_inBand
    (hInBand : HurwitzMatrixSchurProductDetFinThreeInBandStatement) :
    HurwitzMatrixSchurProductDetLeThreeStatement := by
  intro a b ha hb n rows cols hrows hcols hn
  exact hurwitz_schurProduct_det_of_card_le_three hInBand ha hb hrows hcols hn

/-- The refined triangular-free `3 × 3` core implies the low-order, size-`≤ 3`,
Hurwitz matrix Schur-product statement. -/
theorem hurwitzMatrixSchurProductDetLeThree_of_core
    (hcore : HurwitzMatrixSchurProductDetFinThreeCoreStatement) :
    HurwitzMatrixSchurProductDetLeThreeStatement :=
  hurwitzMatrixSchurProductDetLeThree_of_inBand
    (hurwitzMatrixSchurProductDetFinThreeInBand_of_core hcore)

/-- The full Hurwitz matrix Schur-product statement implies its named
low-order, size-`≤ 3`, consequence. -/
theorem hurwitzMatrixSchurProductDetLeThree_of_schurProductTN
    (h : HurwitzMatrixSchurProductTNStatement) :
    HurwitzMatrixSchurProductDetLeThreeStatement := by
  intro a b ha hb n rows cols hrows hcols _hn
  exact h ha hb hrows hcols

/-- The full Hurwitz matrix Schur-product statement implies the isolated
in-band `3 × 3` core. -/
theorem hurwitzMatrixSchurProductDetFinThreeInBand_of_schurProductTN
    (h : HurwitzMatrixSchurProductTNStatement) :
    HurwitzMatrixSchurProductDetFinThreeInBandStatement := by
  intro a b ha hb rows cols hrows hcols _hband
  exact h ha hb hrows hcols

/-- The low-order, size-`≤ 3`, Hurwitz matrix Schur-product statement implies
the isolated in-band `3 × 3` core. -/
theorem hurwitzMatrixSchurProductDetFinThreeInBand_of_leThree
    (hLeThree : HurwitzMatrixSchurProductDetLeThreeStatement) :
    HurwitzMatrixSchurProductDetFinThreeInBandStatement := by
  intro a b ha hb rows cols hrows hcols _hband
  exact hLeThree ha hb hrows hcols (by norm_num)

/-- The low-order, size-`≤ 3`, Hurwitz Schur-product statement is equivalent
to the isolated in-band `3 × 3` core. -/
theorem hurwitzMatrixSchurProductDetLeThree_iff_inBand :
    HurwitzMatrixSchurProductDetLeThreeStatement ↔
      HurwitzMatrixSchurProductDetFinThreeInBandStatement :=
  ⟨hurwitzMatrixSchurProductDetFinThreeInBand_of_leThree,
    hurwitzMatrixSchurProductDetLeThree_of_inBand⟩

/-! ### Reusable reductions for the triangular-free `3 × 3` core -/

/-- Arithmetic band bookkeeping for the triangular-free `3 × 3` core. Under
the two triangular-free hypotheses `2 * cols 1 ≤ rows 0` and
`2 * cols 2 ≤ rows 1`, monotonicity of the selected rows and columns forces
every selected entry except possibly the top-right corner `(0, 2)` onto the
nonzero staircase. -/
theorem hurwitz_schurProduct_core_inband_entries
    {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (h01 : 2 * cols 1 ≤ rows 0) (h12 : 2 * cols 2 ≤ rows 1) :
    2 * cols 0 ≤ rows 0 ∧ 2 * cols 0 ≤ rows 1 ∧ 2 * cols 1 ≤ rows 1 ∧
      2 * cols 0 ≤ rows 2 ∧ 2 * cols 1 ≤ rows 2 ∧ 2 * cols 2 ≤ rows 2 := by
  have hc01 : cols 0 ≤ cols 1 := hcols.monotone (by decide)
  have hc12 : cols 1 ≤ cols 2 := hcols.monotone (by decide)
  have hr01 : rows 0 ≤ rows 1 := hrows.monotone (by decide)
  have hr12 : rows 1 ≤ rows 2 := hrows.monotone (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> lia

/-- The Hadamard-product matrix of two Hurwitz matrices is itself the Hurwitz
matrix of the coefficientwise product, so every one of its minors is the same
minor of `hurwitz (fun k => a k * b k)`. -/
theorem hurwitz_schurProduct_submatrix_eq (a b : ℕ → ℝ) {n : ℕ}
    (rows cols : Fin n → ℕ) :
    (Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols =
      (hurwitz (fun k => a k * b k)).submatrix rows cols := by
  rw [hurwitz_mul_entrywise_matrix]

/-- Fundamental column-shift structure of a Hurwitz matrix: in the nonzero
staircase, moving one column to the right is the same as moving two rows up. -/
theorem hurwitz_col_shift (c : ℕ → ℝ) {i j : ℕ} (h : 2 * (j + 1) ≤ i) :
    hurwitz c i (j + 1) = hurwitz c (i - 2) j := by
  rw [hurwitz_apply_of_band c (by lia), hurwitz_apply_of_band c (by lia)]
  congr 1
  by_cases hp : i % 2 = 0
  · rw [if_pos hp, if_pos (by lia : (i - 2) % 2 = 0)]
    lia
  · rw [if_neg hp, if_neg (by lia : ¬ (i - 2) % 2 = 0)]
    lia

/-- Iterated column-shift structure of a Hurwitz matrix: in the nonzero
staircase, moving `d` columns to the right is the same as moving `2 * d` rows
up.  This is the `hurwitz_col_shift` identity applied `d` times. -/
theorem hurwitz_col_shift_add (c : ℕ → ℝ) (j : ℕ) :
    ∀ (d i : ℕ), 2 * (j + d) ≤ i →
      hurwitz c i (j + d) = hurwitz c (i - 2 * d) j := by
  intro d
  induction d with
  | zero =>
      intro i _
      simp
  | succ d ih =>
      intro i h
      have h1 : hurwitz c i (j + (d + 1)) = hurwitz c (i - 2) (j + d) := by
        have hji : j + (d + 1) = (j + d) + 1 := by lia
        rw [hji, hurwitz_col_shift c (by lia)]
      rw [h1, ih (i - 2) (by lia)]
      congr 1
      lia

/-- Fully in-band subcase of the triangular-free `3 × 3` core: the top-right
corner `(0, 2)` also lies on the nonzero staircase. -/
def HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement : Prop :=
  ∀ {a b : ℕ → ℝ},
    (hurwitz a).IsTotallyNonneg →
    (hurwitz b).IsTotallyNonneg →
    ∀ {rows cols : Fin 3 → ℕ},
      StrictMono rows →
      StrictMono cols →
      (∀ l : Fin 3, 2 * cols l ≤ rows l) →
      2 * cols 1 ≤ rows 0 →
      2 * cols 2 ≤ rows 1 →
      2 * cols 2 ≤ rows 0 →
      0 ≤
        ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det

/-- The full-band `3 × 3` Hadamard determinant with the top-right corner
contribution deleted.  This is the remaining determinant after expanding along
the top row and setting the `(0, 2)` entry to zero. -/
def hurwitzSchurProductFullBandCornerZeroedDet
    (a b : ℕ → ℝ) (rows cols : Fin 3 → ℕ) : ℝ :=
  (hurwitz a (rows 0) (cols 0) * hurwitz b (rows 0) (cols 0)) *
      ((hurwitz a (rows 1) (cols 1) * hurwitz b (rows 1) (cols 1)) *
          (hurwitz a (rows 2) (cols 2) * hurwitz b (rows 2) (cols 2)) -
        (hurwitz a (rows 1) (cols 2) * hurwitz b (rows 1) (cols 2)) *
          (hurwitz a (rows 2) (cols 1) * hurwitz b (rows 2) (cols 1))) -
    (hurwitz a (rows 0) (cols 1) * hurwitz b (rows 0) (cols 1)) *
      ((hurwitz a (rows 1) (cols 0) * hurwitz b (rows 1) (cols 0)) *
          (hurwitz a (rows 2) (cols 2) * hurwitz b (rows 2) (cols 2)) -
        (hurwitz a (rows 1) (cols 2) * hurwitz b (rows 1) (cols 2)) *
          (hurwitz a (rows 2) (cols 0) * hurwitz b (rows 2) (cols 0)))

/-- Corner-zeroed subtarget for the full-band `3 × 3` Hurwitz Schur-product
core.  The full determinant follows from this subtarget by adding the
top-right corner contribution, which is a nonnegative `2 × 2` Hadamard minor. -/
def HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedStatement : Prop :=
  ∀ {a b : ℕ → ℝ},
    (hurwitz a).IsTotallyNonneg →
    (hurwitz b).IsTotallyNonneg →
    ∀ {rows cols : Fin 3 → ℕ},
      StrictMono rows →
      StrictMono cols →
      (∀ l : Fin 3, 2 * cols l ≤ rows l) →
      2 * cols 1 ≤ rows 0 →
      2 * cols 2 ≤ rows 1 →
      2 * cols 2 ≤ rows 0 →
      0 ≤ hurwitzSchurProductFullBandCornerZeroedDet a b rows cols

/-- Single-matrix full-band corner-zeroed determinant subtarget.

This is the sharper one-matrix inequality isolated by the Aristotle
corner-zeroed run.  It says that, for one totally nonnegative Hurwitz matrix in
the fully in-band configuration, deleting the top-right contribution from the
`3 × 3` determinant still leaves a nonnegative expression. -/
def HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleStatement : Prop :=
  ∀ {a : ℕ → ℝ},
    (hurwitz a).IsTotallyNonneg →
    ∀ {rows cols : Fin 3 → ℕ},
      StrictMono rows →
      StrictMono cols →
      (∀ l : Fin 3, 2 * cols l ≤ rows l) →
      2 * cols 1 ≤ rows 0 →
      2 * cols 2 ≤ rows 1 →
      2 * cols 2 ≤ rows 0 →
      0 ≤ hurwitz a (rows 0) (cols 0) *
          (hurwitz a (rows 1) (cols 1) * hurwitz a (rows 2) (cols 2) -
            hurwitz a (rows 1) (cols 2) * hurwitz a (rows 2) (cols 1)) -
        hurwitz a (rows 0) (cols 1) *
          (hurwitz a (rows 1) (cols 0) * hurwitz a (rows 2) (cols 2) -
            hurwitz a (rows 1) (cols 2) * hurwitz a (rows 2) (cols 0))

/-- The full-band `3 × 3` core follows from the corner-zeroed full-band
subtarget.  The missing top-right term factors as the `(0, 2)` entry times a
`2 × 2` Hadamard minor on rows `{1, 2}` and columns `{0, 1}`. -/
theorem hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_cornerZeroed
    (hCZ : HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement := by
  intro a b ha hb rows cols hrows hcols hband h01 h12 h02
  have hcz := hCZ ha hb hrows hcols hband h01 h12 h02
  have hr12 : rows 1 < rows 2 := hrows (by decide)
  have hc01 : cols 0 < cols 1 := hcols (by decide)
  have hcorner := ha.hadamard_det_fin_two hb
    (strictMono_pair hr12) (strictMono_pair hc01)
  rw [Matrix.det_fin_two] at hcorner
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hcorner
  have hentry :
      0 ≤ hurwitz a (rows 0) (cols 2) * hurwitz b (rows 0) (cols 2) :=
    mul_nonneg (ha.nonneg _ _) (hb.nonneg _ _)
  have hcornerTerm :
      0 ≤
        (hurwitz a (rows 0) (cols 2) * hurwitz b (rows 0) (cols 2)) *
          ((hurwitz a (rows 1) (cols 0) * hurwitz b (rows 1) (cols 0)) *
              (hurwitz a (rows 2) (cols 1) * hurwitz b (rows 2) (cols 1)) -
            (hurwitz a (rows 1) (cols 1) * hurwitz b (rows 1) (cols 1)) *
              (hurwitz a (rows 2) (cols 0) * hurwitz b (rows 2) (cols 0))) :=
    mul_nonneg hentry hcorner
  rw [Matrix.det_fin_three]
  simp only [Matrix.submatrix_apply, Matrix.of_apply,
    hurwitzSchurProductFullBandCornerZeroedDet] at hcz ⊢
  nlinarith [hcz, hcornerTerm]

/-- Corner-zero subcase of the triangular-free `3 × 3` core: the top-right
corner `(0, 2)` lies above the staircase, so that entry vanishes. -/
def HurwitzMatrixSchurProductDetFinThreeCoreCornerZeroStatement : Prop :=
  ∀ {a b : ℕ → ℝ},
    (hurwitz a).IsTotallyNonneg →
    (hurwitz b).IsTotallyNonneg →
    ∀ {rows cols : Fin 3 → ℕ},
      StrictMono rows →
      StrictMono cols →
      (∀ l : Fin 3, 2 * cols l ≤ rows l) →
      2 * cols 1 ≤ rows 0 →
      2 * cols 2 ≤ rows 1 →
      rows 0 < 2 * cols 2 →
      0 ≤
        ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det

/-- Reduction of the triangular-free `3 × 3` core (GitHub issue #34) to its
two top-right-corner subcases. Splitting on whether the corner `(0, 2)` is on
the staircase reduces the sharper core to the fully in-band case and the
corner-zero case. -/
theorem hurwitzMatrixSchurProductDetFinThreeCore_of_fullBand_cornerZero
    (hF : HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement)
    (hZ : HurwitzMatrixSchurProductDetFinThreeCoreCornerZeroStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreStatement := by
  intro a b ha hb rows cols hrows hcols hband h01 h12
  by_cases hc : 2 * cols 2 ≤ rows 0
  · exact hF ha hb hrows hcols hband h01 h12 hc
  · exact hZ ha hb hrows hcols hband h01 h12 (by lia)

/-! ### The corner-zero subcase -/

/-- Pure `3 × 3` algebraic core of the corner-zero case.  For two totally
nonnegative `3 × 3` matrices whose top-right entry vanishes, the Hadamard
product has nonnegative determinant.

The proof uses the explicit positive-combination certificate
`det(A∘B) = detA * b00 * b11 * b22
  + a01 * (a10 * a22 - a12 * a20) * (b00 * b11 - b01 * b10) * b22
  + a12 * (a00 * a21 - a01 * a20) * b00 * (b11 * b22 - b12 * b21)
  + a01 * a12 * a20 * detB`. -/
theorem hadamard_det_fin_three_cornerZero_nonneg
    (a00 a01 a10 a11 a12 a20 a21 a22 : ℝ)
    (b00 b01 b10 b11 b12 b20 b21 b22 : ℝ)
    (ha01 : 0 ≤ a01) (ha12 : 0 ≤ a12) (ha20 : 0 ≤ a20)
    (hb00 : 0 ≤ b00) (hb11 : 0 ≤ b11) (hb22 : 0 ≤ b22)
    (mA02 : 0 ≤ a00 * a21 - a01 * a20)
    (mA_r12c02 : 0 ≤ a10 * a22 - a12 * a20)
    (mB01 : 0 ≤ b00 * b11 - b01 * b10)
    (mB_r12c12 : 0 ≤ b11 * b22 - b12 * b21)
    (detA :
      0 ≤ a00 * (a11 * a22 - a12 * a21) -
        a01 * (a10 * a22 - a12 * a20))
    (detB :
      0 ≤ b00 * (b11 * b22 - b12 * b21) -
        b01 * (b10 * b22 - b12 * b20)) :
    0 ≤
      a00 * b00 * (a11 * b11) * (a22 * b22) -
        a00 * b00 * (a12 * b12) * (a21 * b21) -
          a01 * b01 * (a10 * b10) * (a22 * b22) +
            a01 * b01 * (a12 * b12) * (a20 * b20) := by
  nlinarith [mul_nonneg detA (by positivity : (0 : ℝ) ≤ b00 * b11 * b22),
    mul_nonneg (mul_nonneg ha01 mA_r12c02) (mul_nonneg mB01 hb22),
    mul_nonneg (mul_nonneg ha12 mA02) (mul_nonneg hb00 mB_r12c12),
    mul_nonneg (mul_nonneg (mul_nonneg ha01 ha12) ha20) detB]

/-- The two-matrix corner-zeroed full-band subtarget follows from the
single-matrix corner-zeroed determinant subtarget for each factor.

This is the checked part of the Aristotle corner-zeroed reduction: the
one-matrix inequalities supply the `detA` and `detB` inputs to the existing
positive-combination certificate
`hadamard_det_fin_three_cornerZero_nonneg`; the remaining inputs are ordinary
`2 × 2` minors of the two totally nonnegative Hurwitz matrices. -/
theorem hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroed_of_single
    (hSingle :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedStatement := by
  intro a b ha hb rows cols hrows hcols hband h01 h12 h02
  have hr01 : StrictMono ![rows 0, rows 1] := strictMono_pair (hrows (by decide))
  have hr02 : StrictMono ![rows 0, rows 2] := strictMono_pair (hrows (by decide))
  have hr12 : StrictMono ![rows 1, rows 2] := strictMono_pair (hrows (by decide))
  have hc01 : StrictMono ![cols 0, cols 1] := strictMono_pair (hcols (by decide))
  have hc02 : StrictMono ![cols 0, cols 2] := strictMono_pair (hcols (by decide))
  have hc12 : StrictMono ![cols 1, cols 2] := strictMono_pair (hcols (by decide))
  have mA02 := ha hr02 hc01
  rw [Matrix.det_fin_two] at mA02
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at mA02
  have mAc02 := ha hr12 hc02
  rw [Matrix.det_fin_two] at mAc02
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at mAc02
  have mB01 := hb hr01 hc01
  rw [Matrix.det_fin_two] at mB01
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at mB01
  have mBc12 := hb hr12 hc12
  rw [Matrix.det_fin_two] at mBc12
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at mBc12
  have detA := hSingle ha hrows hcols hband h01 h12 h02
  have detB := hSingle hb hrows hcols hband h01 h12 h02
  have hres := hadamard_det_fin_three_cornerZero_nonneg
    (hurwitz a (rows 0) (cols 0)) (hurwitz a (rows 0) (cols 1))
    (hurwitz a (rows 1) (cols 0)) (hurwitz a (rows 1) (cols 1))
    (hurwitz a (rows 1) (cols 2)) (hurwitz a (rows 2) (cols 0))
    (hurwitz a (rows 2) (cols 1)) (hurwitz a (rows 2) (cols 2))
    (hurwitz b (rows 0) (cols 0)) (hurwitz b (rows 0) (cols 1))
    (hurwitz b (rows 1) (cols 0)) (hurwitz b (rows 1) (cols 1))
    (hurwitz b (rows 1) (cols 2)) (hurwitz b (rows 2) (cols 0))
    (hurwitz b (rows 2) (cols 1)) (hurwitz b (rows 2) (cols 2))
    (ha.nonneg (rows 0) (cols 1)) (ha.nonneg (rows 1) (cols 2))
    (ha.nonneg (rows 2) (cols 0)) (hb.nonneg (rows 0) (cols 0))
    (hb.nonneg (rows 1) (cols 1)) (hb.nonneg (rows 2) (cols 2))
    mA02 mAc02 mB01 mBc12 detA detB
  simp only [hurwitzSchurProductFullBandCornerZeroedDet]
  nlinarith [hres]

/-- The single-matrix corner-zeroed determinant subtarget implies the
full-band `3 × 3` Hurwitz Schur-product subcase. -/
theorem hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_cornerZeroedSingle
    (hSingle :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_cornerZeroed
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroed_of_single hSingle)

/-- The corner-zero subcase of the triangular-free `3 × 3` Hurwitz
Schur-product core.  When the top-right corner `(0, 2)` lies strictly above the
staircase, the corresponding Hadamard-product entry vanishes and the determinant
is nonnegative by `hadamard_det_fin_three_cornerZero_nonneg`. -/
theorem hurwitzMatrixSchurProductDetFinThreeCoreCornerZero :
    HurwitzMatrixSchurProductDetFinThreeCoreCornerZeroStatement := by
  intro a b ha hb rows cols hrows hcols _hband _h01 _h12 hcz
  have cza : hurwitz a (rows 0) (cols 2) = 0 :=
    hurwitz_apply_eq_zero_of_lt a hcz
  have czb : hurwitz b (rows 0) (cols 2) = 0 :=
    hurwitz_apply_eq_zero_of_lt b hcz
  have hr01 : StrictMono ![rows 0, rows 1] := strictMono_pair (hrows (by decide))
  have hr02 : StrictMono ![rows 0, rows 2] := strictMono_pair (hrows (by decide))
  have hr12 : StrictMono ![rows 1, rows 2] := strictMono_pair (hrows (by decide))
  have hc01 : StrictMono ![cols 0, cols 1] := strictMono_pair (hcols (by decide))
  have hc02 : StrictMono ![cols 0, cols 2] := strictMono_pair (hcols (by decide))
  have hc12 : StrictMono ![cols 1, cols 2] := strictMono_pair (hcols (by decide))
  have mA02 := ha hr02 hc01
  rw [Matrix.det_fin_two] at mA02
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at mA02
  have mAc02 := ha hr12 hc02
  rw [Matrix.det_fin_two] at mAc02
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at mAc02
  have mB01 := hb hr01 hc01
  rw [Matrix.det_fin_two] at mB01
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at mB01
  have mBc12 := hb hr12 hc12
  rw [Matrix.det_fin_two] at mBc12
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at mBc12
  have detAraw := ha hrows hcols
  rw [Matrix.det_fin_three] at detAraw
  simp only [Matrix.submatrix_apply] at detAraw
  rw [cza] at detAraw
  have detBraw := hb hrows hcols
  rw [Matrix.det_fin_three] at detBraw
  simp only [Matrix.submatrix_apply] at detBraw
  rw [czb] at detBraw
  have detA :
      0 ≤ hurwitz a (rows 0) (cols 0) *
          (hurwitz a (rows 1) (cols 1) * hurwitz a (rows 2) (cols 2) -
            hurwitz a (rows 1) (cols 2) * hurwitz a (rows 2) (cols 1)) -
        hurwitz a (rows 0) (cols 1) *
          (hurwitz a (rows 1) (cols 0) * hurwitz a (rows 2) (cols 2) -
            hurwitz a (rows 1) (cols 2) * hurwitz a (rows 2) (cols 0)) := by
    nlinarith [detAraw]
  have detB :
      0 ≤ hurwitz b (rows 0) (cols 0) *
          (hurwitz b (rows 1) (cols 1) * hurwitz b (rows 2) (cols 2) -
            hurwitz b (rows 1) (cols 2) * hurwitz b (rows 2) (cols 1)) -
        hurwitz b (rows 0) (cols 1) *
          (hurwitz b (rows 1) (cols 0) * hurwitz b (rows 2) (cols 2) -
            hurwitz b (rows 1) (cols 2) * hurwitz b (rows 2) (cols 0)) := by
    nlinarith [detBraw]
  have hres := hadamard_det_fin_three_cornerZero_nonneg
    (hurwitz a (rows 0) (cols 0)) (hurwitz a (rows 0) (cols 1))
    (hurwitz a (rows 1) (cols 0)) (hurwitz a (rows 1) (cols 1))
    (hurwitz a (rows 1) (cols 2)) (hurwitz a (rows 2) (cols 0))
    (hurwitz a (rows 2) (cols 1)) (hurwitz a (rows 2) (cols 2))
    (hurwitz b (rows 0) (cols 0)) (hurwitz b (rows 0) (cols 1))
    (hurwitz b (rows 1) (cols 0)) (hurwitz b (rows 1) (cols 1))
    (hurwitz b (rows 1) (cols 2)) (hurwitz b (rows 2) (cols 0))
    (hurwitz b (rows 2) (cols 1)) (hurwitz b (rows 2) (cols 2))
    (ha.nonneg (rows 0) (cols 1)) (ha.nonneg (rows 1) (cols 2))
    (ha.nonneg (rows 2) (cols 0)) (hb.nonneg (rows 0) (cols 0))
    (hb.nonneg (rows 1) (cols 1)) (hb.nonneg (rows 2) (cols 2))
    mA02 mAc02 mB01 mBc12 detA detB
  rw [Matrix.det_fin_three]
  simp only [Matrix.submatrix_apply, Matrix.of_apply]
  rw [cza, czb]
  nlinarith [hres]

/-- Since the corner-zero subcase is proved, the triangular-free `3 × 3` core
now reduces to the fully in-band top-right subcase alone. -/
theorem hurwitzMatrixSchurProductDetFinThreeCore_of_fullBand
    (hF : HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreStatement :=
  hurwitzMatrixSchurProductDetFinThreeCore_of_fullBand_cornerZero hF
    hurwitzMatrixSchurProductDetFinThreeCoreCornerZero

/-- The fully in-band top-right subcase implies the original in-band `3 × 3`
core. -/
theorem hurwitzMatrixSchurProductDetFinThreeInBand_of_fullBand
    (hF : HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement) :
    HurwitzMatrixSchurProductDetFinThreeInBandStatement :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_core
    (hurwitzMatrixSchurProductDetFinThreeCore_of_fullBand hF)

/-- The fully in-band top-right subcase implies the low-order, size-`≤ 3`,
Hurwitz matrix Schur-product statement. -/
theorem hurwitzMatrixSchurProductDetLeThree_of_fullBand
    (hF : HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement) :
    HurwitzMatrixSchurProductDetLeThreeStatement :=
  hurwitzMatrixSchurProductDetLeThree_of_core
    (hurwitzMatrixSchurProductDetFinThreeCore_of_fullBand hF)

/-- The single-matrix corner-zeroed determinant subtarget implies the
triangular-free `3 × 3` Hurwitz Schur-product core. -/
theorem hurwitzMatrixSchurProductDetFinThreeCore_of_cornerZeroedSingle
    (hSingle :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreStatement :=
  hurwitzMatrixSchurProductDetFinThreeCore_of_fullBand
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_cornerZeroedSingle hSingle)

/-- The single-matrix corner-zeroed determinant subtarget implies the original
in-band `3 × 3` Hurwitz Schur-product core. -/
theorem hurwitzMatrixSchurProductDetFinThreeInBand_of_cornerZeroedSingle
    (hSingle :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleStatement) :
    HurwitzMatrixSchurProductDetFinThreeInBandStatement :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_core
    (hurwitzMatrixSchurProductDetFinThreeCore_of_cornerZeroedSingle hSingle)

/-- The single-matrix corner-zeroed determinant subtarget implies the
low-order, size-`≤ 3`, Hurwitz matrix Schur-product statement. -/
theorem hurwitzMatrixSchurProductDetLeThree_of_cornerZeroedSingle
    (hSingle :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleStatement) :
    HurwitzMatrixSchurProductDetLeThreeStatement :=
  hurwitzMatrixSchurProductDetLeThree_of_core
    (hurwitzMatrixSchurProductDetFinThreeCore_of_cornerZeroedSingle hSingle)

/-- The triangular-free core immediately gives the fully in-band top-right
subcase. -/
theorem hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_core
    (hcore : HurwitzMatrixSchurProductDetFinThreeCoreStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement := by
  intro a b ha hb rows cols hrows hcols hband h01 h12 _h02
  exact hcore ha hb hrows hcols hband h01 h12

/-- After the corner-zero subcase is proved, the triangular-free `3 × 3` core is
equivalent to the fully in-band top-right subcase. -/
theorem hurwitzMatrixSchurProductDetFinThreeCore_iff_fullBand :
    HurwitzMatrixSchurProductDetFinThreeCoreStatement ↔
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement :=
  ⟨hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_core,
    hurwitzMatrixSchurProductDetFinThreeCore_of_fullBand⟩

/-- The triangular-free core immediately gives the corner-zero top-right
subcase. -/
theorem hurwitzMatrixSchurProductDetFinThreeCoreCornerZero_of_core
    (hcore : HurwitzMatrixSchurProductDetFinThreeCoreStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreCornerZeroStatement := by
  intro a b ha hb rows cols hrows hcols hband h01 h12 _h02
  exact hcore ha hb hrows hcols hband h01 h12

/-- The triangular-free `3 × 3` core is equivalent to the conjunction of the
fully in-band top-right subcase and the corner-zero top-right subcase. -/
theorem hurwitzMatrixSchurProductDetFinThreeCore_iff_fullBand_cornerZero :
    HurwitzMatrixSchurProductDetFinThreeCoreStatement ↔
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement ∧
        HurwitzMatrixSchurProductDetFinThreeCoreCornerZeroStatement :=
  ⟨fun hcore =>
    ⟨hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_core hcore,
      hurwitzMatrixSchurProductDetFinThreeCoreCornerZero_of_core hcore⟩,
    fun h => hurwitzMatrixSchurProductDetFinThreeCore_of_fullBand_cornerZero h.1 h.2⟩

end RealRooted
