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

end RealRooted
