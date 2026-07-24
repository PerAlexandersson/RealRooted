import RealRooted.PolyaFrequencyConvolution
import RealRooted.VeroneseSection

open Polynomial Matrix

noncomputable section

namespace RealRooted

/-!
# Hurwitz matrix criterion interface

This file records checked interface lemmas for the row-oriented Hurwitz matrix
used by the Lace and Veronese developments. The classical Hurwitz criterion
does not hold for this orientation; both proposed directions are refuted below.
-/

@[simp] theorem hurwitz_coeff_even_row (p : ℝ[X]) (i j : ℕ) :
    hurwitz p.coeff (2 * i) j = toeplitz (fun k => p.coeff (2 * k + 1)) i j := by
  simp [hurwitz]

@[simp] theorem hurwitz_coeff_odd_row (p : ℝ[X]) (i j : ℕ) :
    hurwitz p.coeff (2 * i + 1) j = toeplitz (fun k => p.coeff (2 * k)) i j := by
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
    hurwitz p.coeff (2 * i) j =
      if j ≤ i then p.coeff (2 * (i - j) + 1) else 0 :=
  hurwitz_even_row_apply p.coeff i j

theorem hurwitz_coeff_odd_row_apply (p : ℝ[X]) (i j : ℕ) :
    hurwitz p.coeff (2 * i + 1) j =
      if j ≤ i then p.coeff (2 * (i - j)) else 0 :=
  hurwitz_odd_row_apply p.coeff i j

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
  simpa [IsPolyaFreqSeq, ← hurwitz_submatrix_even_eq_toeplitz] using
    hc.submatrix (by intro i j hij; lia) strictMono_id

/-- Total nonnegativity of a Hurwitz matrix implies that the even coefficient
subsequence is Pólya-frequency. -/
theorem hurwitz_isPolyaFreqSeq_even {c : ℕ → ℝ}
    (hc : (hurwitz c).IsTotallyNonneg) :
    IsPolyaFreqSeq (fun n => c (2 * n)) := by
  simpa [IsPolyaFreqSeq, ← hurwitz_submatrix_odd_eq_toeplitz] using
    hc.submatrix (strictMono_nat_of_lt_succ fun _ => by lia) strictMono_id

/-- Unfolded finite-minor form of
`HurwitzStableToMatrixTotallyNonnegativeStatement`.

This candidate statement is false for the current row orientation; see
`not_hurwitzStableToMatrixTotallyNonnegativeStatement`. -/
def HurwitzStableToHurwitzMatrixMinorsStatement : Prop :=
  ∀ {p : ℝ[X]}, IsHurwitzStable p → (hurwitz p.coeff).IsTotallyNonneg

theorem hurwitzStableToMatrixTotallyNonnegativeStatement_iff_minors :
    HurwitzStableToMatrixTotallyNonnegativeStatement ↔
      HurwitzStableToHurwitzMatrixMinorsStatement :=
  Iff.rfl

abbrev HurwitzMatrixTotallyNonnegativeToStableStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄, p ≠ 0 → (hurwitz p.coeff).IsTotallyNonneg → IsHurwitzStable p

/-- The converse Hurwitz-matrix criterion gives the converse odd/even Lace
bridge by the explicit Hurwitz/Lace matrix identity. -/
theorem fullyInterlacingPairToHurwitzOddEvenStable_of_matrixTNN
    (hMatrixToStable : HurwitzMatrixTotallyNonnegativeToStableStatement) :
    FullyInterlacingPairToHurwitzOddEvenStableStatement :=
  fun {p q} hpq0 hfull =>
    hMatrixToStable
      (oddEvenPolynomial_ne_zero_iff.mpr hpq0)
      ((hurwitzMatrixTotallyNonnegative_oddEvenPolynomial_iff_fullyInterlacingPair p q).2
        hfull)

/-- Full weak Hurwitz-matrix criterion in the coefficient-nonnegative
convention used in this project. -/
abbrev HurwitzMatrixCriterionStatement : Prop :=
  HurwitzStableToMatrixTotallyNonnegativeStatement ∧
    HurwitzMatrixTotallyNonnegativeToStableStatement

theorem hurwitzStableToMatrixTotallyNonnegative_of_criterion
    (h : HurwitzMatrixCriterionStatement) :
    HurwitzStableToMatrixTotallyNonnegativeStatement :=
  h.1

theorem hurwitzStableToHurwitzMatrixMinors_of_criterion
    (h : HurwitzMatrixCriterionStatement) :
    HurwitzStableToHurwitzMatrixMinorsStatement :=
  fun hstab => h.1 hstab

theorem hurwitzMatrixTotallyNonnegativeToStable_of_criterion
    (h : HurwitzMatrixCriterionStatement) :
    HurwitzMatrixTotallyNonnegativeToStableStatement :=
  h.2

theorem fullyInterlacingPairToHurwitzOddEvenStable_of_criterion
    (h : HurwitzMatrixCriterionStatement) :
    FullyInterlacingPairToHurwitzOddEvenStableStatement :=
  fullyInterlacingPairToHurwitzOddEvenStable_of_matrixTNN h.2

theorem hurwitzOddEvenToFullyInterlacingPair_of_matrixMinors
    (hStableToMatrix : HurwitzStableToMatrixTotallyNonnegativeStatement) :
    HurwitzOddEvenToFullyInterlacingPairStatement :=
  fun {p q} hstab =>
    (hurwitzMatrixTotallyNonnegative_oddEvenPolynomial_iff_fullyInterlacingPair p q).mp
      (hStableToMatrix hstab)

theorem hurwitzOddEvenToFullyInterlacingPair_of_criterion
    (h : HurwitzMatrixCriterionStatement) :
    HurwitzOddEvenToFullyInterlacingPairStatement :=
  hurwitzOddEvenToFullyInterlacingPair_of_matrixMinors h.1

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
  simpa using hurwitz_mul_entrywise a b i j

/-- Proposed infinite-matrix extension of the finite nonsingular Hurwitz-matrix
form of Garloff--Wagner Theorem 1.

The cited theorem proves closure for finite nonsingular Hurwitz matrices. The
statement below is kept as an explicit interface because neither that theorem
nor the current development justifies the unrestricted infinite, possibly
singular version. -/
abbrev HurwitzMatrixSchurProductTNStatement : Prop :=
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
  simpa using mul_nonneg (ha.nonneg i j) (hb.nonneg i j)

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
  · have hband : ∀ l : Fin 3, 2 * cols l ≤ rows l :=
      fun l => not_lt.mp (fun hl => hfail ⟨l, hl⟩)
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
    HurwitzMatrixSchurProductDetFinThreeCoreStatement :=
  fun {_a _b} ha hb {_rows} {_cols} hrows hcols hband _h01 _h12 =>
    hInBand ha hb hrows hcols hband

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
    HurwitzMatrixSchurProductDetLeThreeStatement :=
  @hurwitz_schurProduct_det_of_card_le_three hInBand

/-- The refined triangular-free `3 × 3` core implies the low-order, size-`≤ 3`,
Hurwitz matrix Schur-product statement. -/
theorem hurwitzMatrixSchurProductDetLeThree_of_core
    (hcore : HurwitzMatrixSchurProductDetFinThreeCoreStatement) :
    HurwitzMatrixSchurProductDetLeThreeStatement :=
  hurwitzMatrixSchurProductDetLeThree_of_inBand
    (hurwitzMatrixSchurProductDetFinThreeInBand_of_core hcore)

theorem hurwitzMatrixSchurProductDetLeThree_of_schurProductTN
    (hSchur : HurwitzMatrixSchurProductTNStatement) :
    HurwitzMatrixSchurProductDetLeThreeStatement :=
  fun {_a _b} ha hb {_n} {_rows} {_cols} hrows hcols _hn =>
    hSchur ha hb hrows hcols

/-- The full Hurwitz matrix Schur-product statement implies the isolated
in-band `3 × 3` core. -/
theorem hurwitzMatrixSchurProductDetFinThreeInBand_of_schurProductTN
    (hSchur : HurwitzMatrixSchurProductTNStatement) :
    HurwitzMatrixSchurProductDetFinThreeInBandStatement :=
  fun {_a _b} ha hb {_rows} {_cols} hrows hcols _hband =>
    hSchur ha hb hrows hcols

/-- The low-order, size-`≤ 3`, Hurwitz matrix Schur-product statement implies
the isolated in-band `3 × 3` core. -/
theorem hurwitzMatrixSchurProductDetFinThreeInBand_of_leThree
    (hLeThree : HurwitzMatrixSchurProductDetLeThreeStatement) :
    HurwitzMatrixSchurProductDetFinThreeInBandStatement :=
  fun {_a _b} ha hb {_rows} {_cols} hrows hcols _hband =>
    hLeThree ha hb hrows hcols (by norm_num)

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

This is the sharper one-matrix inequality isolated by an earlier Aristotle
corner-zeroed run.  It is retained as a named historical branch for existing
reductions, but it is too strong as a proof route: see
`RealRooted.Challenges.Issue34SingleMatrixCounterexample` for checked
arithmetic showing a candidate window where the full determinant is positive
while the corner-zeroed expression is negative.  The two-matrix issue #34
target is not refuted by that arithmetic witness. -/
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

/-- Column-normalized version of the single-matrix full-band corner-zeroed
determinant subtarget.

The first selected column is assumed to be `0`.  The general single-matrix
subtarget reduces to this normalized form by shifting all selected columns by
`cols 0` and all selected rows by `2 * cols 0`. -/
def HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement :
    Prop :=
  ∀ {a : ℕ → ℝ},
    (hurwitz a).IsTotallyNonneg →
    ∀ {rows cols : Fin 3 → ℕ},
      StrictMono rows →
      StrictMono cols →
      (∀ l : Fin 3, 2 * cols l ≤ rows l) →
      2 * cols 1 ≤ rows 0 →
      2 * cols 2 ≤ rows 1 →
      2 * cols 2 ≤ rows 0 →
      cols 0 = 0 →
      0 ≤ hurwitz a (rows 0) (cols 0) *
          (hurwitz a (rows 1) (cols 1) * hurwitz a (rows 2) (cols 2) -
            hurwitz a (rows 1) (cols 2) * hurwitz a (rows 2) (cols 1)) -
        hurwitz a (rows 0) (cols 1) *
          (hurwitz a (rows 1) (cols 0) * hurwitz a (rows 2) (cols 2) -
            hurwitz a (rows 1) (cols 2) * hurwitz a (rows 2) (cols 0))

/-- First-column form of the corner-zeroed single-matrix determinant. -/
def hurwitzFullBandCornerZeroedSingleFirstColDet
    (a : ℕ → ℝ) (row0 row1 row2 col1 col2 : ℕ) : ℝ :=
  hurwitz a row0 0 *
      (hurwitz a (row1 - 2 * col1) 0 *
          hurwitz a (row2 - 2 * col2) 0 -
        hurwitz a (row1 - 2 * col2) 0 *
          hurwitz a (row2 - 2 * col1) 0) -
    hurwitz a (row0 - 2 * col1) 0 *
      (hurwitz a row1 0 * hurwitz a (row2 - 2 * col2) 0 -
        hurwitz a (row1 - 2 * col2) 0 * hurwitz a row2 0)

/-- The lower-left `2 × 2` minor appearing in the first-column determinant
decomposition. -/
def hurwitzFullBandCornerZeroedSingleFirstColLowerMinor
    (a : ℕ → ℝ) (row1 row2 col1 : ℕ) : ℝ :=
  hurwitz a row1 0 * hurwitz a (row2 - 2 * col1) 0 -
    hurwitz a (row1 - 2 * col1) 0 * hurwitz a row2 0

/-- First-column normal form of the single-matrix full-band corner-zeroed
determinant subtarget.

After the first selected column is normalized to `0`, every remaining selected
column can be shifted back to column `0` by moving rows up by twice that column
index.  This is the remaining #34 leaf in pure first-column Hurwitz form. -/
def HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement :
    Prop :=
  ∀ {a : ℕ → ℝ},
    (hurwitz a).IsTotallyNonneg →
    ∀ {row0 row1 row2 col1 col2 : ℕ},
      row0 < row1 →
      row1 < row2 →
      0 < col1 →
      col1 < col2 →
      2 * col2 ≤ row0 →
      0 ≤ hurwitzFullBandCornerZeroedSingleFirstColDet a row0 row1 row2 col1 col2

/-- Strict-remainder branch of the first-column target.

The full `3 × 3` determinant supplies the first-column corner-zeroed
determinant plus a product of the shifted top-right entry and the lower-left
`2 × 2` minor.  The zero cases of that product are automatic, so the remaining
work is the branch where both factors are strictly positive. -/
def HurwitzMatrixSchurProductDetFirstColPositiveRemainderStatement : Prop :=
  ∀ {a : ℕ → ℝ},
    (hurwitz a).IsTotallyNonneg →
    ∀ {row0 row1 row2 col1 col2 : ℕ},
      row0 < row1 →
      row1 < row2 →
      0 < col1 →
      col1 < col2 →
      2 * col2 ≤ row0 →
      0 < hurwitz a (row0 - 2 * col2) 0 →
      0 < hurwitzFullBandCornerZeroedSingleFirstColLowerMinor a row1 row2 col1 →
      0 ≤ hurwitzFullBandCornerZeroedSingleFirstColDet a row0 row1 row2 col1 col2

/-- The strict-remainder branch implies the first-column normal form. -/
theorem
    hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol_of_positiveRemainder
    (hPos :
      HurwitzMatrixSchurProductDetFirstColPositiveRemainderStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement := by
  intro a ha row0 row1 row2 col1 col2 hr01 hr12 hc0 hc12 h02
  let rows : Fin 3 → ℕ := ![row0, row1, row2]
  let cols : Fin 3 → ℕ := ![0, col1, col2]
  have hrows : StrictMono rows := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [rows] at hij ⊢ <;> lia
  have hcols : StrictMono cols := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [cols] at hij ⊢ <;> lia
  have hrow0_le : ∀ i : Fin 3, row0 ≤ rows i := by
    intro i
    fin_cases i
    · rfl
    · exact le_of_lt hr01
    · exact (le_of_lt hr01).trans (le_of_lt hr12)
  have hcol_le : ∀ j : Fin 3, cols j ≤ col2 := by
    intro j
    fin_cases j
    · exact Nat.zero_le col2
    · exact le_of_lt hc12
    · rfl
  have hall : ∀ i j : Fin 3, 2 * cols j ≤ rows i := by
    intro i j
    have hi := hrow0_le i
    have hj := hcol_le j
    lia
  have hshift (i j : Fin 3) :
      hurwitz a (rows i) (cols j) = hurwitz a (rows i - 2 * cols j) 0 := by
    simpa using
      hurwitz_col_shift_add a 0 (cols j) (rows i) (by simpa using hall i j)
  have hcorner_nonneg : 0 ≤ hurwitz a (row0 - 2 * col2) 0 := by
    have h := ha.nonneg row0 col2
    change 0 ≤ hurwitz a (rows 0) (cols 2) at h
    rwa [hshift 0 2] at h
  have hminor_nonneg :
      0 ≤ hurwitzFullBandCornerZeroedSingleFirstColLowerMinor a row1 row2 col1 := by
    have h := ha (strictMono_pair hr12) (strictMono_pair hc0)
    rw [Matrix.det_fin_two] at h
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have h10 : hurwitz a row1 col1 = hurwitz a (row1 - 2 * col1) 0 := by
      simpa [rows, cols] using hshift 1 1
    have h21 : hurwitz a row2 col1 = hurwitz a (row2 - 2 * col1) 0 := by
      simpa [rows, cols] using hshift 2 1
    simpa [hurwitzFullBandCornerZeroedSingleFirstColLowerMinor, h10, h21] using h
  have hs01 : hurwitz a row0 col1 = hurwitz a (row0 - 2 * col1) 0 := by
    simpa [rows, cols] using hshift 0 1
  have hs02 : hurwitz a row0 col2 = hurwitz a (row0 - 2 * col2) 0 := by
    simpa [rows, cols] using hshift 0 2
  have hs11 : hurwitz a row1 col1 = hurwitz a (row1 - 2 * col1) 0 := by
    simpa [rows, cols] using hshift 1 1
  have hs12 : hurwitz a row1 col2 = hurwitz a (row1 - 2 * col2) 0 := by
    simpa [rows, cols] using hshift 1 2
  have hs21 : hurwitz a row2 col1 = hurwitz a (row2 - 2 * col1) 0 := by
    simpa [rows, cols] using hshift 2 1
  have hs22 : hurwitz a row2 col2 = hurwitz a (row2 - 2 * col2) 0 := by
    simpa [rows, cols] using hshift 2 2
  have hdet_full :
      0 ≤ hurwitzFullBandCornerZeroedSingleFirstColDet a row0 row1 row2 col1 col2 +
        hurwitz a (row0 - 2 * col2) 0 *
          hurwitzFullBandCornerZeroedSingleFirstColLowerMinor a row1 row2 col1 := by
    have hdet := ha hrows hcols
    rw [Matrix.det_fin_three] at hdet
    simp only [Matrix.submatrix_apply] at hdet
    change
      0 ≤
        hurwitz a row0 0 * hurwitz a row1 col1 * hurwitz a row2 col2 -
          hurwitz a row0 0 * hurwitz a row1 col2 * hurwitz a row2 col1 -
            hurwitz a row0 col1 * hurwitz a row1 0 * hurwitz a row2 col2 +
          hurwitz a row0 col1 * hurwitz a row1 col2 * hurwitz a row2 0 +
            hurwitz a row0 col2 * hurwitz a row1 0 * hurwitz a row2 col1 -
          hurwitz a row0 col2 * hurwitz a row1 col1 * hurwitz a row2 0 at hdet
    rw [hs01, hs02, hs11, hs12, hs21, hs22] at hdet
    dsimp [hurwitzFullBandCornerZeroedSingleFirstColDet,
      hurwitzFullBandCornerZeroedSingleFirstColLowerMinor]
    nlinarith [hdet]
  by_cases hcorner :
      hurwitz a (row0 - 2 * col2) 0 = 0
  · dsimp [hurwitzFullBandCornerZeroedSingleFirstColDet] at hdet_full ⊢
    nlinarith
  · by_cases hminor :
        hurwitzFullBandCornerZeroedSingleFirstColLowerMinor a row1 row2 col1 = 0
    · dsimp [hurwitzFullBandCornerZeroedSingleFirstColDet,
        hurwitzFullBandCornerZeroedSingleFirstColLowerMinor] at hdet_full hminor ⊢
      nlinarith
    · exact hPos ha hr01 hr12 hc0 hc12 h02
        (lt_of_le_of_ne hcorner_nonneg (Ne.symm hcorner))
        (lt_of_le_of_ne hminor_nonneg (Ne.symm hminor))

/-- The general single-matrix corner-zeroed target specializes to the
column-normalized target. -/
theorem
    hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero_of_single
    (hSingle :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement :=
  fun {_a} ha {_rows} {_cols} hrows hcols hband h01 h12 h02 _hcol0 =>
    hSingle ha hrows hcols hband h01 h12 h02

/-- The first-column normal form implies the column-normalized single-matrix
corner-zeroed determinant target. -/
theorem
    hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero_of_firstCol
    (hFirst :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement := by
  intro a ha rows cols hrows hcols _hband _h01 _h12 h02 hcol0
  have hr01 : rows 0 < rows 1 := hrows (by decide)
  have hr12 : rows 1 < rows 2 := hrows (by decide)
  have hr02le : rows 0 ≤ rows 2 := (le_of_lt hr01).trans (le_of_lt hr12)
  have hc01 : cols 0 < cols 1 := hcols (by decide)
  have hc12 : cols 1 < cols 2 := hcols (by decide)
  have hc01pos : 0 < cols 1 := by
    simpa [hcol0] using hc01
  have hcol_le_two : ∀ j : Fin 3, cols j ≤ cols 2 := by
    intro j
    fin_cases j
    · simp [hcol0]
    · exact le_of_lt hc12
    · rfl
  have hrow_ge_zero : ∀ i : Fin 3, rows 0 ≤ rows i := by
    intro i
    fin_cases i
    · rfl
    · exact le_of_lt hr01
    · exact hr02le
  have hall : ∀ i j : Fin 3, 2 * cols j ≤ rows i := by
    intro i j
    have hc := hcol_le_two j
    have hr := hrow_ge_zero i
    lia
  have hentry (i j : Fin 3) :
      hurwitz a (rows i) (cols j) = hurwitz a (rows i - 2 * cols j) 0 := by
    simpa using
      hurwitz_col_shift_add a 0 (cols j) (rows i) (by simpa using hall i j)
  have hfirst := hFirst ha hr01 hr12 hc01pos hc12 h02
  rw [hentry 0 0, hentry 1 1, hentry 2 2, hentry 1 2, hentry 2 1,
    hentry 0 1, hentry 1 0, hentry 2 0]
  simpa [hurwitzFullBandCornerZeroedSingleFirstColDet, hcol0] using hfirst

/-- The column-normalized single-matrix target specializes to the first-column
normal form. -/
theorem
    hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol_of_colZero
    (hZero :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement := by
  intro a ha row0 row1 row2 col1 col2 hr01 hr12 hc0 hc12 h02
  let rows : Fin 3 → ℕ := ![row0, row1, row2]
  let cols : Fin 3 → ℕ := ![0, col1, col2]
  have hrows : StrictMono rows := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [rows] at hij ⊢ <;> lia
  have hcols : StrictMono cols := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [cols] at hij ⊢ <;> lia
  have hband : ∀ l : Fin 3, 2 * cols l ≤ rows l := by
    intro l
    fin_cases l <;> simp [rows, cols] <;> lia
  have h01 : 2 * cols 1 ≤ rows 0 := by
    simpa [rows, cols] using le_trans (Nat.mul_le_mul_left 2 (le_of_lt hc12)) h02
  have h12 : 2 * cols 2 ≤ rows 1 := by
    simpa [rows, cols] using le_trans h02 (le_of_lt hr01)
  have h02' : 2 * cols 2 ≤ rows 0 := by
    simpa [rows, cols] using h02
  have hcol0 : cols 0 = 0 := by simp [cols]
  have hres := hZero ha hrows hcols hband h01 h12 h02' hcol0
  have hall : ∀ i j : Fin 3, 2 * cols j ≤ rows i := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [rows, cols] <;> lia
  have hshift (i j : Fin 3) :
      hurwitz a (rows i) (cols j) = hurwitz a (rows i - 2 * cols j) 0 := by
    simpa only [Nat.zero_add] using
      hurwitz_col_shift_add a 0 (cols j) (rows i) (by simpa using hall i j)
  have hs01 : hurwitz a row0 col1 = hurwitz a (row0 - 2 * col1) 0 := by
    simpa [rows, cols] using hshift 0 1
  have hs11 : hurwitz a row1 col1 = hurwitz a (row1 - 2 * col1) 0 := by
    simpa [rows, cols] using hshift 1 1
  have hs21 : hurwitz a row2 col1 = hurwitz a (row2 - 2 * col1) 0 := by
    simpa [rows, cols] using hshift 2 1
  have hs12 : hurwitz a row1 col2 = hurwitz a (row1 - 2 * col2) 0 := by
    simpa [rows, cols] using hshift 1 2
  have hs22 : hurwitz a row2 col2 = hurwitz a (row2 - 2 * col2) 0 := by
    simpa [rows, cols] using hshift 2 2
  simpa [hurwitzFullBandCornerZeroedSingleFirstColDet, rows, cols,
    hs01, hs11, hs21, hs12, hs22] using hres

/-- The general single-matrix target specializes to the first-column normal
form. -/
theorem
    hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol_of_single
    (hSingle :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol_of_colZero
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero_of_single
      hSingle)

/-- The column-normalized single-matrix corner-zeroed target implies the
general single-matrix corner-zeroed target. -/
theorem hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingle_of_colZero
    (hZero :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleStatement := by
  intro a ha rows cols hrows hcols hband h01 h12 h02
  let d := cols 0
  let rows' : Fin 3 → ℕ := fun i => rows i - 2 * d
  let cols' : Fin 3 → ℕ := fun i => cols i - d
  have hr01 : rows 0 ≤ rows 1 := hrows.monotone (by decide)
  have hr12 : rows 1 ≤ rows 2 := hrows.monotone (by decide)
  have hr02 : rows 0 ≤ rows 2 := hrows.monotone (by decide)
  have hc0 : ∀ i : Fin 3, d ≤ cols i := by
    intro i
    have h0i : (0 : Fin 3) ≤ i := by
      fin_cases i <;> decide
    exact hcols.monotone h0i
  have hdrow : ∀ i : Fin 3, 2 * d ≤ rows i := by
    intro i
    have h0 : 2 * d ≤ rows 0 := by
      simpa [d] using hband 0
    fin_cases i
    · exact h0
    · exact le_trans h0 hr01
    · exact le_trans h0 hr02
  have hrows' : StrictMono rows' := by
    intro i j hij
    dsimp [rows']
    have hij' := hrows hij
    have hi := hdrow i
    have hj := hdrow j
    lia
  have hcols' : StrictMono cols' := by
    intro i j hij
    dsimp [cols']
    have hij' := hcols hij
    have hi := hc0 i
    have hj := hc0 j
    lia
  have hband' : ∀ l : Fin 3, 2 * cols' l ≤ rows' l := by
    intro l
    dsimp [rows', cols']
    have hc := hc0 l
    have hr := hdrow l
    have hb := hband l
    lia
  have h01' : 2 * cols' 1 ≤ rows' 0 := by
    dsimp [rows', cols']
    have hc := hc0 1
    have hr := hdrow 0
    lia
  have h12' : 2 * cols' 2 ≤ rows' 1 := by
    dsimp [rows', cols']
    have hc := hc0 2
    have hr := hdrow 1
    lia
  have h02' : 2 * cols' 2 ≤ rows' 0 := by
    dsimp [rows', cols']
    have hc := hc0 2
    have hr := hdrow 0
    lia
  have hcol0' : cols' 0 = 0 := by
    dsimp [cols', d]
    exact Nat.sub_self _
  have hall : ∀ i j : Fin 3, 2 * cols j ≤ rows i := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using hband 0
    · simpa using h01
    · simpa using h02
    · exact le_trans (by simpa using hband 0) hr01
    · simpa using hband 1
    · simpa using h12
    · exact le_trans (by simpa using hband 0) hr02
    · exact le_trans (by simpa using hband 1) hr12
    · simpa using hband 2
  have hentry (i j : Fin 3) :
      hurwitz a (rows i) (cols j) = hurwitz a (rows' i) (cols' j) := by
    have hcadd : cols' j + d = cols j := by
      dsimp [cols', d]
      exact Nat.sub_add_cancel (hc0 j)
    have hrow : rows i - 2 * d = rows' i := by
      rfl
    have hs := hurwitz_col_shift_add a (cols' j) d (rows i) <|
      by simpa [hcadd] using hall i j
    simpa [hcadd, hrow] using hs
  have hnorm := hZero ha hrows' hcols' hband' h01' h12' h02' hcol0'
  rw [← hentry 0 0, ← hentry 1 1, ← hentry 2 2, ← hentry 1 2,
    ← hentry 2 1, ← hentry 0 1, ← hentry 1 0, ← hentry 2 0] at hnorm
  exact hnorm

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

/-- The column-normalized single-matrix corner-zeroed determinant subtarget
implies the two-matrix corner-zeroed full-band subtarget. -/
theorem hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroed_of_singleColZero
    (hZero :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedStatement :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroed_of_single
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingle_of_colZero hZero)

/-- The first-column normal form implies the two-matrix corner-zeroed
full-band subtarget. -/
theorem hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroed_of_singleFirstCol
    (hFirst :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedStatement :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroed_of_singleColZero
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero_of_firstCol
      hFirst)

/-- The column-normalized single-matrix corner-zeroed determinant subtarget
implies the full-band `3 × 3` Hurwitz Schur-product subcase. -/
theorem hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_cornerZeroedSingleColZero
    (hZero :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_cornerZeroedSingle
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingle_of_colZero hZero)

/-- The first-column normal form implies the full-band `3 × 3` Hurwitz
Schur-product subcase. -/
theorem hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_cornerZeroedSingleFirstCol
    (hFirst :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement :=
  hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_cornerZeroedSingleColZero
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero_of_firstCol
      hFirst)

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

/-- The column-normalized single-matrix corner-zeroed determinant subtarget
implies the triangular-free `3 × 3` Hurwitz Schur-product core. -/
theorem hurwitzMatrixSchurProductDetFinThreeCore_of_cornerZeroedSingleColZero
    (hZero :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreStatement :=
  hurwitzMatrixSchurProductDetFinThreeCore_of_cornerZeroedSingle
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingle_of_colZero hZero)

/-- The column-normalized single-matrix corner-zeroed determinant subtarget
implies the original in-band `3 × 3` Hurwitz Schur-product core. -/
theorem hurwitzMatrixSchurProductDetFinThreeInBand_of_cornerZeroedSingleColZero
    (hZero :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement) :
    HurwitzMatrixSchurProductDetFinThreeInBandStatement :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_cornerZeroedSingle
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingle_of_colZero hZero)

/-- The column-normalized single-matrix corner-zeroed determinant subtarget
implies the low-order, size-`≤ 3`, Hurwitz matrix Schur-product statement. -/
theorem hurwitzMatrixSchurProductDetLeThree_of_cornerZeroedSingleColZero
    (hZero :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement) :
    HurwitzMatrixSchurProductDetLeThreeStatement :=
  hurwitzMatrixSchurProductDetLeThree_of_cornerZeroedSingle
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingle_of_colZero hZero)

/-- The first-column normal form implies the triangular-free `3 × 3` Hurwitz
Schur-product core. -/
theorem hurwitzMatrixSchurProductDetFinThreeCore_of_cornerZeroedSingleFirstCol
    (hFirst :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreStatement :=
  hurwitzMatrixSchurProductDetFinThreeCore_of_cornerZeroedSingleColZero
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero_of_firstCol
      hFirst)

/-- The first-column normal form implies the original in-band `3 × 3` Hurwitz
Schur-product core. -/
theorem hurwitzMatrixSchurProductDetFinThreeInBand_of_cornerZeroedSingleFirstCol
    (hFirst :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement) :
    HurwitzMatrixSchurProductDetFinThreeInBandStatement :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_cornerZeroedSingleColZero
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero_of_firstCol
      hFirst)

/-- The first-column normal form implies the low-order, size-`≤ 3`, Hurwitz
matrix Schur-product statement. -/
theorem hurwitzMatrixSchurProductDetLeThree_of_cornerZeroedSingleFirstCol
    (hFirst :
      HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement) :
    HurwitzMatrixSchurProductDetLeThreeStatement :=
  hurwitzMatrixSchurProductDetLeThree_of_cornerZeroedSingleColZero
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero_of_firstCol
      hFirst)

/-- The triangular-free core immediately gives the fully in-band top-right
subcase. -/
theorem hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_core
    (hcore : HurwitzMatrixSchurProductDetFinThreeCoreStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement :=
  fun {_a _b} ha hb {_rows} {_cols} hrows hcols hband h01 h12 _h02 =>
    hcore ha hb hrows hcols hband h01 h12

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
    HurwitzMatrixSchurProductDetFinThreeCoreCornerZeroStatement :=
  fun {_a _b} ha hb {_rows} {_cols} hrows hcols hband h01 h12 _h02 =>
    hcore ha hb hrows hcols hband h01 h12

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

/-! ### The first-column normal-form leaf is false

The leaf
`HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement`
is strictly stronger than the genuine `3 × 3` minor nonnegativity supplied by
total nonnegativity: the corner-zeroed determinant equals the honest minor
minus the top-right corner contribution, and that subtraction can make it
negative.

The explicit counterexample below uses the totally nonnegative Hurwitz matrix
whose first column is the binomial sequence `k ↦ C(16, k)`, with
`rows = (9, 10, 11)` and `cols = (0, 1, 2)`.  There the corner-zeroed
determinant equals `-11569226240 < 0`.
-/

/-- The Hurwitz matrix of any coefficient sequence is the even-column submatrix
of the Toeplitz matrix built from its own first column. -/
theorem hurwitz_eq_toeplitz_firstColumn_submatrix (c : ℕ → ℝ) :
    hurwitz c = (toeplitz fun k => hurwitz c k 0).submatrix id fun j => 2 * j := by
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, toeplitz_apply]
  by_cases h : 2 * j ≤ i
  · rw [if_pos h]
    simpa using hurwitz_col_shift_add c 0 j i (by simpa using h)
  · rw [if_neg h]
    exact hurwitz_apply_eq_zero_of_lt c (by lia)

/-- If the first column of a Hurwitz matrix is a Pólya-frequency sequence, then
the whole Hurwitz matrix is totally nonnegative. -/
theorem hurwitz_isTotallyNonneg_of_firstColumn_isPolyaFreqSeq (c : ℕ → ℝ)
    (h : IsPolyaFreqSeq fun k => hurwitz c k 0) :
    (hurwitz c).IsTotallyNonneg := by
  exact hurwitz_eq_toeplitz_firstColumn_submatrix c ▸
    Matrix.IsTotallyNonneg.submatrix h strictMono_id (fun _ _ hab => by lia)

/-! ### The row-oriented Hurwitz criterion is false -/

/-- The polynomial `X ^ 3 + 1` refutes the converse criterion for the current
row-oriented Hurwitz matrix. -/
def hurwitzMatrixCriterionCounterexample : ℝ[X] := X ^ 3 + 1

theorem hurwitzMatrixCriterionCounterexample_matrix_isTotallyNonneg :
    (hurwitz hurwitzMatrixCriterionCounterexample.coeff).IsTotallyNonneg := by
  apply hurwitz_isTotallyNonneg_of_firstColumn_isPolyaFreqSeq
  have hpf1 : IsPolyaFreqSeq (X + 1 : ℝ[X]).coeff := by
    convert IsPolyaFreqSeq.linear (r := (-1 : ℝ)) (by norm_num) using 1
    funext n
    simp
  have hpf : IsPolyaFreqSeq (X * (X + 1) : ℝ[X]).coeff := by
    simpa only [map_zero, sub_zero] using
      IsPolyaFreqSeq.linear_mul (r := (0 : ℝ)) (by norm_num) hpf1
  convert hpf using 1
  funext k
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m = 2 * m by ring, hurwitz_even_row_apply, if_pos (Nat.zero_le m)]
    rw [show (X * (X + 1) : ℝ[X]) = X ^ 2 + X by ring]
    simp [hurwitzMatrixCriterionCounterexample, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
    lia
  · subst hm
    rw [hurwitz_odd_row_apply, if_pos (Nat.zero_le m)]
    rw [show (X * (X + 1) : ℝ[X]) = X ^ 2 + X by ring]
    simp [hurwitzMatrixCriterionCounterexample, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
    lia

private def hurwitzMatrixCriterionCounterexampleRoot : ℂ :=
  ⟨(1 : ℝ) / 2, Real.sqrt 3 / 2⟩

private theorem hurwitzMatrixCriterionCounterexampleRoot_re_pos :
    0 < hurwitzMatrixCriterionCounterexampleRoot.re := by
  norm_num [hurwitzMatrixCriterionCounterexampleRoot]

private theorem hurwitzMatrixCriterionCounterexampleRoot_cube :
    hurwitzMatrixCriterionCounterexampleRoot ^ 3 = -1 := by
  have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    calc
      Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hs]
  apply Complex.ext
  · simp [hurwitzMatrixCriterionCounterexampleRoot, pow_succ,
      Complex.mul_re, Complex.mul_im]
    ring_nf
    nlinarith
  · simp [hurwitzMatrixCriterionCounterexampleRoot, pow_succ,
      Complex.mul_re, Complex.mul_im]
    ring_nf
    nlinarith

theorem not_isHurwitzStable_hurwitzMatrixCriterionCounterexample :
    ¬ IsHurwitzStable hurwitzMatrixCriterionCounterexample := by
  intro h
  apply h.2 hurwitzMatrixCriterionCounterexampleRoot
    hurwitzMatrixCriterionCounterexampleRoot_re_pos
  rw [show complexify hurwitzMatrixCriterionCounterexample = (X ^ 3 + 1 : ℂ[X]) by
    simp [hurwitzMatrixCriterionCounterexample, complexify]]
  simp [hurwitzMatrixCriterionCounterexampleRoot_cube]

/-- Total nonnegativity of the current row-oriented Hurwitz matrix does not
imply Hurwitz stability, even for a nonzero polynomial. -/
theorem not_hurwitzMatrixTotallyNonnegativeToStableStatement :
    ¬ HurwitzMatrixTotallyNonnegativeToStableStatement := by
  intro h
  exact not_isHurwitzStable_hurwitzMatrixCriterionCounterexample
    (h (by
      intro hp
      have hc := congrArg (fun p : ℝ[X] => p.coeff 3) hp
      norm_num [hurwitzMatrixCriterionCounterexample, Polynomial.coeff_add,
        Polynomial.coeff_X_pow, Polynomial.coeff_one] at hc)
      hurwitzMatrixCriterionCounterexample_matrix_isTotallyNonneg)

/-- The two-sided row-oriented Hurwitz criterion is false. -/
theorem not_hurwitzMatrixCriterionStatement : ¬ HurwitzMatrixCriterionStatement :=
  fun h => not_hurwitzStableToMatrixTotallyNonnegativeStatement h.1

/-- Counterexample first column: the binomial sequence `k ↦ C(16, k)`. -/
noncomputable def cexFirstColumn : ℕ → ℝ := fun k => (Nat.choose 16 k : ℝ)

/-- The binomial sequence `k ↦ C(16, k)` is a Pólya-frequency sequence. -/
theorem cexFirstColumn_isPolyaFreqSeq : IsPolyaFreqSeq cexFirstColumn := by
  have hpf := IsPolyaFreqSeq.prod_X_sub_C (Multiset.replicate 16 (-1 : ℝ))
    (by
      intro r hr
      rw [Multiset.eq_of_mem_replicate hr]
      norm_num)
  have heq : ((Multiset.replicate 16 (-1 : ℝ)).map fun r => X - C r).prod =
      (X + 1) ^ 16 := by
    rw [Multiset.map_replicate, Multiset.prod_replicate]
    congr 1
    rw [map_neg, map_one]
    ring
  have hfun :
      (fun n => (((Multiset.replicate 16 (-1 : ℝ)).map fun r => X - C r).prod).coeff n)
        = cexFirstColumn := by
    funext n
    rw [heq, Polynomial.coeff_X_add_one_pow]
    rfl
  rwa [hfun] at hpf

/-- The counterexample coefficient sequence: the parity swap of
`cexFirstColumn`, chosen so that the first column of `hurwitz cexA` is exactly
`cexFirstColumn`. -/
noncomputable def cexA : ℕ → ℝ :=
  fun n => if n % 2 = 0 then cexFirstColumn (n + 1) else cexFirstColumn (n - 1)

/-- The first column of `hurwitz cexA` is the binomial sequence. -/
theorem hurwitz_cexA_firstColumn (k : ℕ) : hurwitz cexA k 0 = cexFirstColumn k := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m = 2 * m by ring, hurwitz_even_row_apply, if_pos (Nat.zero_le m),
      Nat.sub_zero]
    simp only [cexA, if_neg (show ¬ (2 * m + 1) % 2 = 0 by lia), Nat.add_sub_cancel]
  · subst hm
    rw [hurwitz_odd_row_apply, if_pos (Nat.zero_le m), Nat.sub_zero]
    simp only [cexA, if_pos (show (2 * m) % 2 = 0 by lia)]

/-- The Hurwitz matrix of the counterexample is totally nonnegative. -/
theorem cexA_hurwitz_isTotallyNonneg : (hurwitz cexA).IsTotallyNonneg := by
  refine hurwitz_isTotallyNonneg_of_firstColumn_isPolyaFreqSeq cexA ?_
  simpa [hurwitz_cexA_firstColumn] using cexFirstColumn_isPolyaFreqSeq

/-- The first-column normal-form leaf of GitHub issue #34 is false.  Even for
the concrete totally nonnegative Hurwitz matrix `hurwitz cexA`, the
corner-zeroed determinant at `rows = (9, 10, 11)`, `cols = (0, 1, 2)` is
negative. -/
theorem not_hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol :
    ¬ HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstColStatement := by
  intro H
  have key := H cexA_hurwitz_isTotallyNonneg (row0 := 9) (row1 := 10) (row2 := 11)
    (col1 := 1) (col2 := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  simp only [hurwitz_cexA_firstColumn, cexFirstColumn,
    hurwitzFullBandCornerZeroedSingleFirstColDet] at key
  norm_num [Nat.choose] at key

/-- The column-normalized single-matrix leaf of GitHub issue #34 is false. -/
theorem not_hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZero :
    ¬ HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleColZeroStatement :=
  fun h => not_hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol_of_colZero
      h)

/-- The general single-matrix corner-zeroed leaf of GitHub issue #34 is false. -/
theorem not_hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingle :
    ¬ HurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleStatement :=
  fun h => not_hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBandCornerZeroedSingleFirstCol_of_single
      h)

/-! ### Hurwitz staircase/Toeplitz normal form for the full-band Schur product

The genuine two-matrix issue #34 target is special to Hurwitz matrices, and
(as recorded in `RealRooted.Challenges.Issue34WindowObstruction`) cannot be
reached from total nonnegativity of the selected `3 × 3` windows alone.  The
lemmas below expose the Hurwitz-specific input: the column-shift/staircase
relation `hurwitz_col_shift_add` identifies, on the nonzero staircase, a
Hurwitz matrix entry with a single Toeplitz entry of its column-`0` sequence.
This turns any fully in-band minor of the entrywise product of two Hurwitz
matrices into an honest Toeplitz minor of the pointwise product of the two
column-`0` sequences, and thereby reduces the full-band `3 × 3` core to a
single Pólya-frequency statement about that product sequence. -/

/-- Hurwitz staircase/Toeplitz relation.  On the nonzero staircase
`2 * j ≤ i`, the `(i, j)` entry of a Hurwitz matrix equals the `(i, 2 * j)`
entry of the Toeplitz matrix built from its column-`0` sequence
`n ↦ hurwitz c n 0`. -/
theorem hurwitz_eq_toeplitz_colZero (c : ℕ → ℝ) {i j : ℕ} (h : 2 * j ≤ i) :
    hurwitz c i j = toeplitz (fun n => hurwitz c n 0) i (2 * j) := by
  have hshift := hurwitz_col_shift_add c 0 j i (by simpa using h)
  simp only [Nat.zero_add] at hshift
  rw [hshift, toeplitz_apply, if_pos h]

/-- Toeplitz normal form for a fully in-band minor of the entrywise Hurwitz
product.  When every selected `(rows i, cols j)` cell lies on the nonzero
staircase, the selected submatrix of the Hadamard product equals the Toeplitz
submatrix of the pointwise product sequence
`k ↦ hurwitz a k 0 * hurwitz b k 0`, with the columns doubled. -/
theorem hurwitz_schurProduct_submatrix_eq_toeplitz_of_band
    (a b : ℕ → ℝ) {n : ℕ} {rows cols : Fin n → ℕ}
    (hband : ∀ i j, 2 * cols j ≤ rows i) :
    (Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols =
      (toeplitz (fun k => hurwitz a k 0 * hurwitz b k 0)).submatrix rows
        (fun j => 2 * cols j) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply]
  rw [hurwitz_eq_toeplitz_colZero a (hband i j),
    hurwitz_eq_toeplitz_colZero b (hband i j), toeplitz_apply, toeplitz_apply,
    toeplitz_apply, if_pos (hband i j), if_pos (hband i j), if_pos (hband i j)]

/-- Determinant form of the Toeplitz normal form: a fully in-band minor of the
entrywise Hurwitz product has the same determinant as the corresponding
doubled-column Toeplitz minor of the pointwise product sequence. -/
theorem hurwitz_schurProduct_det_submatrix_eq_toeplitz_of_band
    (a b : ℕ → ℝ) {n : ℕ} {rows cols : Fin n → ℕ}
    (hband : ∀ i j, 2 * cols j ≤ rows i) :
    ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det =
      ((toeplitz (fun k => hurwitz a k 0 * hurwitz b k 0)).submatrix rows
        (fun j => 2 * cols j)).det := by
  rw [hurwitz_schurProduct_submatrix_eq_toeplitz_of_band a b hband]

/-- Reusable reduction of the full-band `3 × 3` Hurwitz Schur-product core
(GitHub issue #34) to a single Pólya-frequency statement.

If for every pair of totally nonnegative Hurwitz matrices the pointwise product
of their column-`0` sequences is a Pólya-frequency sequence, then the full-band
`3 × 3` core holds.  This is faithful to the classical Garloff--Wagner content:
after the staircase change of variables the minor is literally a Toeplitz minor
of that product sequence, so its nonnegativity is exactly the Pólya-frequency
condition.  Unlike the refuted single-matrix corner-zeroed route, this genuinely
uses the Hurwitz Toeplitz/staircase structure of both factors. -/
theorem hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_polyaFreq
    (hPF : ∀ {a b : ℕ → ℝ},
      (hurwitz a).IsTotallyNonneg →
      (hurwitz b).IsTotallyNonneg →
      IsPolyaFreqSeq (fun k => hurwitz a k 0 * hurwitz b k 0)) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement := by
  intro a b ha hb rows cols hrows hcols _hband _h01 _h12 h02
  have hbandall : ∀ i j : Fin 3, 2 * cols j ≤ rows i := by
    intro i j
    have hcj : cols j ≤ cols 2 := hcols.monotone (Fin.le_last j)
    have hri : rows 0 ≤ rows i := hrows.monotone (Fin.zero_le i)
    calc
      2 * cols j ≤ 2 * cols 2 := by lia
      _ ≤ rows 0 := h02
      _ ≤ rows i := hri
  have hdbl : StrictMono (fun j : Fin 3 => 2 * cols j) := by
    intro x y hxy
    have := hcols hxy
    lia
  simpa [hurwitz_schurProduct_det_submatrix_eq_toeplitz_of_band a b hbandall] using
    hPF ha hb hrows hdbl

/-- The Pólya-frequency reduction, transported to the original in-band `3 × 3`
Hurwitz Schur-product core through the existing full-band reduction. -/
theorem hurwitzMatrixSchurProductDetFinThreeInBand_of_polyaFreq
    (hPF : ∀ {a b : ℕ → ℝ},
      (hurwitz a).IsTotallyNonneg →
      (hurwitz b).IsTotallyNonneg →
      IsPolyaFreqSeq (fun k => hurwitz a k 0 * hurwitz b k 0)) :
    HurwitzMatrixSchurProductDetFinThreeInBandStatement :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_fullBand
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_polyaFreq hPF)

/-- The Pólya-frequency reduction, transported to the low-order size-`≤ 3`
Hurwitz Schur-product statement. -/
theorem hurwitzMatrixSchurProductDetLeThree_of_polyaFreq
    (hPF : ∀ {a b : ℕ → ℝ},
      (hurwitz a).IsTotallyNonneg →
      (hurwitz b).IsTotallyNonneg →
      IsPolyaFreqSeq (fun k => hurwitz a k 0 * hurwitz b k 0)) :
    HurwitzMatrixSchurProductDetLeThreeStatement :=
  hurwitzMatrixSchurProductDetLeThree_of_fullBand
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_polyaFreq hPF)

/-- Even-column Toeplitz nonnegativity leaf for the column-`0` product
sequence.  Only doubled columns `2 * cols j` are selected, so this is strictly
weaker than the false full column-`0` product Pólya-frequency leaf. -/
def HurwitzColumnZeroProductEvenColToeplitzStatement : Prop :=
  ∀ {a b : ℕ → ℝ},
    (hurwitz a).IsTotallyNonneg →
    (hurwitz b).IsTotallyNonneg →
    ∀ {n : ℕ} {rows cols : Fin n → ℕ},
      StrictMono rows →
      StrictMono cols →
      0 ≤ ((toeplitz (fun k => hurwitz a k 0 * hurwitz b k 0)).submatrix rows
        (fun j => 2 * cols j)).det

/-- Sharpened reduction of the full-band `3 × 3` Hurwitz Schur-product core
(GitHub issue #34) to the even-column Toeplitz leaf. -/
theorem hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_evenColToeplitz
    (hEven : HurwitzColumnZeroProductEvenColToeplitzStatement) :
    HurwitzMatrixSchurProductDetFinThreeCoreFullBandStatement := by
  intro a b ha hb rows cols hrows hcols _hband _h01 _h12 h02
  have hbandall : ∀ i j : Fin 3, 2 * cols j ≤ rows i := by
    intro i j
    have hcj : cols j ≤ cols 2 := hcols.monotone (Fin.le_last j)
    have hri : rows 0 ≤ rows i := hrows.monotone (Fin.zero_le i)
    calc
      2 * cols j ≤ 2 * cols 2 := Nat.mul_le_mul_left 2 hcj
      _ ≤ rows 0 := h02
      _ ≤ rows i := hri
  simpa [hurwitz_schurProduct_det_submatrix_eq_toeplitz_of_band a b hbandall] using
    hEven ha hb hrows hcols

/-- The even-column Toeplitz reduction, transported to the original in-band
`3 × 3` Hurwitz Schur-product core. -/
theorem hurwitzMatrixSchurProductDetFinThreeInBand_of_evenColToeplitz
    (hEven : HurwitzColumnZeroProductEvenColToeplitzStatement) :
    HurwitzMatrixSchurProductDetFinThreeInBandStatement :=
  hurwitzMatrixSchurProductDetFinThreeInBand_of_fullBand
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_evenColToeplitz hEven)

/-- The even-column Toeplitz reduction, transported to the low-order size-`≤ 3`
Hurwitz Schur-product statement. -/
theorem hurwitzMatrixSchurProductDetLeThree_of_evenColToeplitz
    (hEven : HurwitzColumnZeroProductEvenColToeplitzStatement) :
    HurwitzMatrixSchurProductDetLeThreeStatement :=
  hurwitzMatrixSchurProductDetLeThree_of_fullBand
    (hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_evenColToeplitz hEven)

/-- The full column-`0` product Pólya-frequency leaf implies the sharper
even-column Toeplitz leaf: doubled columns are a special case of arbitrary
columns.  The converse is not known and is the point of the sharper leaf. -/
theorem hurwitzColumnZeroProductEvenColToeplitz_of_polyaFreq
    (hPF : ∀ {a b : ℕ → ℝ},
      (hurwitz a).IsTotallyNonneg →
      (hurwitz b).IsTotallyNonneg →
      IsPolyaFreqSeq (fun k => hurwitz a k 0 * hurwitz b k 0)) :
    HurwitzColumnZeroProductEvenColToeplitzStatement := by
  intro a b ha hb n rows cols hrows hcols
  have hdbl : StrictMono (fun j : Fin n => 2 * cols j) := by
    intro x y hxy
    have h := hcols hxy
    exact Nat.mul_lt_mul_of_pos_left h (by decide : 0 < 2)
  exact hPF ha hb hrows hdbl

/-! ### Hadamard normal form for the even-column Toeplitz leaf

The even-column Toeplitz minor of the pointwise product of the two column-`0`
sequences is, entry by entry, the Hadamard product of the two Hurwitz
submatrices selected by the same rows and columns.  This holds with no band
hypothesis: off the staircase every entry on both sides vanishes. -/

/-- Non-band Toeplitz/Hadamard normal form for the column-`0` product minor.
For arbitrary rows and columns, the even-column Toeplitz submatrix of the
pointwise product of the two column-`0` sequences equals the entrywise product
of the corresponding submatrices of the two Hurwitz matrices. -/
theorem toeplitz_colZeroProduct_submatrix_eq_hadamard
    (a b : ℕ → ℝ) {n : ℕ} (rows cols : Fin n → ℕ) :
    (toeplitz (fun k => hurwitz a k 0 * hurwitz b k 0)).submatrix rows
        (fun j => 2 * cols j)
      = Matrix.of fun i j =>
          (hurwitz a).submatrix rows cols i j *
            (hurwitz b).submatrix rows cols i j := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, toeplitz_apply]
  by_cases h : 2 * cols j ≤ rows i
  · rw [if_pos h, hurwitz_eq_toeplitz_colZero a h, hurwitz_eq_toeplitz_colZero b h]
    simp only [toeplitz_apply, if_pos h]
  · rw [if_neg h, hurwitz_apply_eq_zero_of_lt a (by lia), zero_mul]

/-- The determinant of the Hadamard product of two `2 × 2` totally
nonnegative matrices is nonnegative. -/
theorem det_hadamard_fin_two_nonneg
    {M N : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M.IsTotallyNonneg) (hN : N.IsTotallyNonneg) :
    0 ≤ (Matrix.of fun i j => M i j * N i j).det := by
  have hM01 : 0 ≤ M 0 1 := hM.nonneg 0 1
  have hM10 : 0 ≤ M 1 0 := hM.nonneg 1 0
  have hN01 : 0 ≤ N 0 1 := hN.nonneg 0 1
  have hN10 : 0 ≤ N 1 0 := hN.nonneg 1 0
  have hdM : 0 ≤ M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
    have h := hM (rows := id) (cols := id) strictMono_id strictMono_id
    simpa [Matrix.det_fin_two] using h
  have hdN : 0 ≤ N 0 0 * N 1 1 - N 0 1 * N 1 0 := by
    have h := hN (rows := id) (cols := id) strictMono_id strictMono_id
    simpa [Matrix.det_fin_two] using h
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply]
  nlinarith [mul_nonneg hM01 hM10, mul_nonneg hN01 hN10,
    mul_nonneg (mul_nonneg hM01 hM10) hdN, mul_nonneg hdM (mul_nonneg hN01 hN10),
    mul_nonneg hdM hdN]

/-- The even-column Toeplitz leaf holds at every size `n ≤ 2`.  This is the
size-`≤ 2` part of `HurwitzColumnZeroProductEvenColToeplitzStatement`, obtained
from the Hadamard normal form and the fact that the Hadamard product of two
totally nonnegative matrices has nonnegative determinant in sizes `≤ 2`. -/
theorem hurwitzColumnZeroProductEvenColToeplitz_of_size_le_two
    {a b : ℕ → ℝ}
    (ha : (hurwitz a).IsTotallyNonneg) (hb : (hurwitz b).IsTotallyNonneg)
    {n : ℕ} (hn : n ≤ 2) {rows cols : Fin n → ℕ}
    (hrows : StrictMono rows) (hcols : StrictMono cols) :
    0 ≤ ((toeplitz (fun k => hurwitz a k 0 * hurwitz b k 0)).submatrix rows
        (fun j => 2 * cols j)).det := by
  rw [toeplitz_colZeroProduct_submatrix_eq_hadamard a b rows cols]
  have hMa := ha.submatrix hrows hcols
  have hMb := hb.submatrix hrows hcols
  interval_cases n
  · simp
  · rw [Matrix.det_fin_one]
    simp only [Matrix.of_apply, Matrix.submatrix_apply]
    exact mul_nonneg (ha.nonneg _ _) (hb.nonneg _ _)
  · exact det_hadamard_fin_two_nonneg hMa hMb

/-! ### Hurwitz normal form for the even-column Toeplitz leaf

The entrywise product of two Hurwitz matrices is again a Hurwitz matrix,
namely the Hurwitz matrix of the pointwise product of the two coefficient
sequences.  Thus the even-column Toeplitz leaf is equivalent to total
nonnegativity of this pointwise-product Hurwitz matrix. -/

/-- The Hurwitz matrix of the pointwise product of two coefficient sequences is
the entrywise product of the two Hurwitz matrices. -/
theorem hurwitz_mul_apply (a b : ℕ → ℝ) (i j : ℕ) :
    hurwitz (fun k => a k * b k) i j = hurwitz a i j * hurwitz b i j := by
  rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m = 2 * m by ring, hurwitz_even_row_apply, hurwitz_even_row_apply,
      hurwitz_even_row_apply]
    split <;> simp
  · subst hm
    rw [hurwitz_odd_row_apply, hurwitz_odd_row_apply, hurwitz_odd_row_apply]
    split <;> simp

/-- Pointwise even-column identity: the even-column entry of the Toeplitz matrix
of the column-`0` product sequence equals the corresponding entry of the
Hurwitz matrix of the pointwise product. -/
theorem toeplitz_colZeroProduct_apply_eq_hurwitz_mul (a b : ℕ → ℝ) (i j : ℕ) :
    toeplitz (fun k => hurwitz a k 0 * hurwitz b k 0) i (2 * j) =
      hurwitz (fun k => a k * b k) i j := by
  rw [toeplitz_apply]
  rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m = 2 * m by ring, hurwitz_even_row_apply]
    by_cases h : j ≤ m
    · rw [if_pos (by lia), if_pos h, show 2 * m - 2 * j = 2 * (m - j) by lia,
        hurwitz_even_row_apply, hurwitz_even_row_apply]
      simp
    · rw [if_neg (by lia), if_neg h]
  · subst hm
    rw [hurwitz_odd_row_apply]
    by_cases h : j ≤ m
    · rw [if_pos (by lia), if_pos h, show 2 * m + 1 - 2 * j = 2 * (m - j) + 1 by lia,
        hurwitz_odd_row_apply, hurwitz_odd_row_apply]
      simp
    · rw [if_neg (by lia), if_neg h]

/-- Hurwitz normal form for the column-`0` product minor.  For arbitrary rows
and columns, the even-column Toeplitz submatrix of the pointwise product of the
two column-`0` sequences equals the corresponding submatrix of the Hurwitz
matrix of the pointwise product `fun k => a k * b k`. -/
theorem toeplitz_colZeroProduct_submatrix_eq_hurwitz_mul
    (a b : ℕ → ℝ) {n : ℕ} (rows cols : Fin n → ℕ) :
    (toeplitz (fun k => hurwitz a k 0 * hurwitz b k 0)).submatrix rows
        (fun j => 2 * cols j)
      = (hurwitz (fun k => a k * b k)).submatrix rows cols := by
  ext i j
  simp only [Matrix.submatrix_apply]
  exact toeplitz_colZeroProduct_apply_eq_hurwitz_mul a b (rows i) (cols j)

/-- Total-nonnegativity leaf in Hurwitz normal form: the Hurwitz matrix of the
pointwise product of two coefficient sequences with totally nonnegative Hurwitz
matrices is itself totally nonnegative.  This is the clean Garloff--Wagner
content of GitHub issue #34, equivalent to the even-column Toeplitz leaf. -/
def HurwitzMulTotallyNonnegStatement : Prop :=
  ∀ {a b : ℕ → ℝ},
    (hurwitz a).IsTotallyNonneg →
    (hurwitz b).IsTotallyNonneg →
    (hurwitz (fun k => a k * b k)).IsTotallyNonneg

/-- The Hurwitz normal-form leaf implies the even-column Toeplitz leaf. -/
theorem hurwitzColumnZeroProductEvenColToeplitz_of_hurwitzMul
    (h : HurwitzMulTotallyNonnegStatement) :
    HurwitzColumnZeroProductEvenColToeplitzStatement :=
  fun {_ _} ha hb {_} {_} {_} hrows hcols => by
    simpa [toeplitz_colZeroProduct_submatrix_eq_hurwitz_mul] using
      h ha hb hrows hcols

/-- Conversely, the even-column Toeplitz leaf implies the Hurwitz normal-form
leaf: every minor of the Hurwitz matrix of the pointwise product is an
even-column Toeplitz minor of the column-`0` product sequence. -/
theorem hurwitzMul_of_hurwitzColumnZeroProductEvenColToeplitz
    (h : HurwitzColumnZeroProductEvenColToeplitzStatement) :
    HurwitzMulTotallyNonnegStatement :=
  fun {_ _} ha hb {_} {_} {_} hrows hcols => by
    simpa [toeplitz_colZeroProduct_submatrix_eq_hurwitz_mul] using
      h ha hb hrows hcols

/-! ### The column-`0` product Pólya-frequency leaf is false

The full-band reduction
`hurwitzMatrixSchurProductDetFinThreeCoreFullBand_of_polyaFreq` only shows
that the column-`0` product Pólya-frequency statement is a sufficient condition
for the full-band `3 × 3` Hurwitz Schur-product core.  That statement itself is
false: total nonnegativity of a Hurwitz matrix does not force its column-`0`
sequence to be Pólya-frequency, and the pointwise product of the column-`0`
sequences of two totally nonnegative Hurwitz matrices can fail to be
Pólya-frequency.  This rules out this particular Pólya-frequency route to
GitHub issue #34, without bearing on the truth of the classical
Garloff--Wagner theorem itself. -/

/-- If all odd-indexed entries of a coefficient sequence vanish, then every
even row of its Hurwitz matrix is identically zero. -/
theorem hurwitz_even_row_eq_zero_of_odd_zero {a : ℕ → ℝ}
    (hodd : ∀ n, a (2 * n + 1) = 0) (i j : ℕ) :
    hurwitz a (2 * i) j = 0 := by
  rw [hurwitz_even_row_apply]
  split
  · rw [hodd]
  · rfl

/-- Total nonnegativity of a Hurwitz matrix whose odd-indexed coefficients all
vanish and whose even coefficient subsequence is Pólya-frequency.  The even
rows of the Hurwitz matrix vanish, so every finite minor either contains a
zero row or selects only odd rows, in which case it is a Toeplitz minor of the
even subsequence. -/
theorem hurwitz_isTotallyNonneg_of_odd_zero {a : ℕ → ℝ}
    (hodd : ∀ n, a (2 * n + 1) = 0)
    (heven : IsPolyaFreqSeq (fun n => a (2 * n))) :
    (hurwitz a).IsTotallyNonneg := by
  rw [IsPolyaFreqSeq] at heven
  intro n rows cols hrows hcols
  by_cases hall : ∀ k, rows k % 2 = 1
  · have hsub : (hurwitz a).submatrix rows cols =
        (toeplitz (fun t => a (2 * t))).submatrix (fun k => rows k / 2) cols := by
      ext k l
      simp only [Matrix.submatrix_apply]
      have hr : rows k % 2 = 1 := hall k
      unfold hurwitz
      simp only [Matrix.of_apply]
      rw [if_neg (by lia)]
    rw [hsub]
    refine heven ?_ hcols
    intro k1 k2 hk
    have h1 : rows k1 % 2 = 1 := hall k1
    have h2 : rows k2 % 2 = 1 := hall k2
    have hlt := hrows hk
    lia
  · obtain ⟨k, hk⟩ := not_forall.mp hall
    have hke : rows k % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (rows k) with h | h
      · exact h
      · exact absurd h hk
    have hzero : ∀ l, ((hurwitz a).submatrix rows cols) k l = 0 := by
      intro l
      simp only [Matrix.submatrix_apply]
      have hrk : rows k = 2 * (rows k / 2) := by lia
      rw [hrk]
      exact hurwitz_even_row_eq_zero_of_odd_zero hodd _ _
    exact le_of_eq (Matrix.det_eq_zero_of_row_eq_zero k hzero).symm

/-! ### The unrestricted infinite Schur-product statement is false -/

/-- First coefficient sequence in the infinite Schur-product counterexample.
Its even subsequence is `1, 2, 2, ...`, and its odd coefficients vanish. -/
def hurwitzSchurCounterexampleLeft : ℕ → ℝ :=
  fun n => if n % 2 = 0 then if n = 0 then 1 else 2 else 0

/-- Second coefficient sequence in the infinite Schur-product counterexample.
Its even subsequence is `1, 2, 3, ...`, and its odd coefficients vanish. -/
def hurwitzSchurCounterexampleRight : ℕ → ℝ :=
  fun n => if n % 2 = 0 then (n / 2 + 1 : ℕ) else 0

theorem hurwitzSchurCounterexampleLeft_odd_zero (n : ℕ) :
    hurwitzSchurCounterexampleLeft (2 * n + 1) = 0 := by
  simp [hurwitzSchurCounterexampleLeft]

theorem hurwitzSchurCounterexampleRight_odd_zero (n : ℕ) :
    hurwitzSchurCounterexampleRight (2 * n + 1) = 0 := by
  simp [hurwitzSchurCounterexampleRight]

/-- The two infinite PF certificates reduce the proposed Hurwitz Schur-product
statement to an explicit `3 × 3` minor with determinant `-4`. -/
theorem not_hurwitzMatrixSchurProductTNStatement_of_counterexamplePF
    (hleft : IsPolyaFreqSeq (fun n => hurwitzSchurCounterexampleLeft (2 * n)))
    (hright : IsPolyaFreqSeq (fun n => hurwitzSchurCounterexampleRight (2 * n))) :
    ¬ HurwitzMatrixSchurProductTNStatement := by
  intro H
  have hleftTN : (hurwitz hurwitzSchurCounterexampleLeft).IsTotallyNonneg :=
    hurwitz_isTotallyNonneg_of_odd_zero hurwitzSchurCounterexampleLeft_odd_zero hleft
  have hrightTN : (hurwitz hurwitzSchurCounterexampleRight).IsTotallyNonneg :=
    hurwitz_isTotallyNonneg_of_odd_zero hurwitzSchurCounterexampleRight_odd_zero hright
  have hminor := H hleftTN hrightTN (n := 3) (rows := ![5, 7, 9])
    (cols := ![0, 1, 2]) (by decide) (by decide)
  norm_num [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, hurwitz, toeplitz,
    hurwitzSchurCounterexampleLeft, hurwitzSchurCounterexampleRight] at hminor

/-- The unrestricted, infinite Hurwitz-matrix Schur-product statement is false. -/
theorem not_hurwitzMatrixSchurProductTNStatement :
    ¬ HurwitzMatrixSchurProductTNStatement := by
  apply not_hurwitzMatrixSchurProductTNStatement_of_counterexamplePF
  · simpa [hurwitzSchurCounterexampleLeft] using oneThenTwo_isPolyaFreqSeq
  · simpa [hurwitzSchurCounterexampleRight] using natSucc_isPolyaFreqSeq

/-- Counterexample coefficient sequence `1 + X^2`. -/
def cexOddZero : ℕ → ℝ :=
  fun n => if n = 0 then 1 else if n = 2 then 1 else 0

/-- The odd-indexed coefficients of `cexOddZero` vanish. -/
theorem cexOddZero_odd_zero (n : ℕ) : cexOddZero (2 * n + 1) = 0 := by
  simp only [cexOddZero]
  rw [if_neg (by lia), if_neg (by lia)]

/-- The even coefficient subsequence of `cexOddZero` is `(1 + X)`, a
Pólya-frequency sequence. -/
theorem cexOddZero_even_isPolyaFreqSeq :
    IsPolyaFreqSeq (fun n => cexOddZero (2 * n)) := by
  have h := IsPolyaFreqSeq.prod_X_sub_C (Multiset.replicate 1 (-1 : ℝ))
    (by
      intro r hr
      rw [Multiset.eq_of_mem_replicate hr]
      norm_num)
  have heq :
      (fun n =>
          (((Multiset.replicate 1 (-1 : ℝ)).map fun r => X - C r).prod).coeff n)
        = fun n => cexOddZero (2 * n) := by
    funext n
    rw [Multiset.map_replicate, Multiset.prod_replicate, pow_one]
    match n with
    | 0 =>
        rw [coeff_sub, coeff_X, coeff_C]
        norm_num [cexOddZero]
    | 1 =>
        rw [coeff_sub, coeff_X, coeff_C]
        norm_num [cexOddZero]
    | m + 2 =>
        have hL : ((X - C (-1 : ℝ)).coeff (m + 2)) = 0 := by
          rw [coeff_sub, coeff_X, coeff_C,
            if_neg (by lia : ¬ (1 : ℕ) = m + 2),
            if_neg (by lia : ¬ m + 2 = 0), sub_zero]
        have hR : cexOddZero (2 * (m + 2)) = 0 := by
          simp only [cexOddZero]
          rw [if_neg (by lia), if_neg (by lia)]
        rw [hL, hR]
  rwa [heq] at h

/-- The Hurwitz matrix of `cexOddZero` is totally nonnegative. -/
theorem cexOddZero_hurwitz_isTotallyNonneg :
    (hurwitz cexOddZero).IsTotallyNonneg :=
  hurwitz_isTotallyNonneg_of_odd_zero cexOddZero_odd_zero
    cexOddZero_even_isPolyaFreqSeq

/-- Column-`0` value of `hurwitz cexOddZero` at row `1` is `1`. -/
theorem cexOddZero_col0_one : hurwitz cexOddZero 1 0 = 1 := by
  rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, hurwitz_odd_row_apply,
    if_pos (Nat.zero_le 0)]
  simp [cexOddZero]

/-- Column-`0` value of `hurwitz cexOddZero` at row `2` is `0`. -/
theorem cexOddZero_col0_two : hurwitz cexOddZero 2 0 = 0 := by
  rw [show (2 : ℕ) = 2 * 1 from rfl,
    hurwitz_even_row_eq_zero_of_odd_zero cexOddZero_odd_zero]

/-- Column-`0` value of `hurwitz cexOddZero` at row `3` is `1`. -/
theorem cexOddZero_col0_three : hurwitz cexOddZero 3 0 = 1 := by
  rw [show (3 : ℕ) = 2 * 1 + 1 from rfl, hurwitz_odd_row_apply,
    if_pos (Nat.zero_le 1)]
  simp [cexOddZero]

/-- The column-`0` product Pólya-frequency leaf of GitHub issue #34 is false.

Using `a = b = cexOddZero`, both Hurwitz matrices are totally nonnegative, yet
the pointwise product of their column-`0` sequences is `0, 1, 0, 1, 0, …`,
whose Toeplitz minor on rows `(2, 3)` and columns `(0, 1)` equals `-1`. -/
theorem not_hurwitzColumnZeroProductPF :
    ¬ (∀ {a b : ℕ → ℝ},
      (hurwitz a).IsTotallyNonneg →
      (hurwitz b).IsTotallyNonneg →
      IsPolyaFreqSeq (fun k => hurwitz a k 0 * hurwitz b k 0)) := by
  intro H
  have hPF := H cexOddZero_hurwitz_isTotallyNonneg cexOddZero_hurwitz_isTotallyNonneg
  rw [IsPolyaFreqSeq] at hPF
  have hdet := hPF (strictMono_pair (by norm_num : (2 : ℕ) < 3))
    (strictMono_pair (by norm_num : (0 : ℕ) < 1))
  have hval :
      ((toeplitz (fun k => hurwitz cexOddZero k 0 * hurwitz cexOddZero k 0)).submatrix
        ![2, 3] ![0, 1]).det = -1 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      toeplitz_apply]
    norm_num [cexOddZero_col0_one, cexOddZero_col0_two, cexOddZero_col0_three]
  rw [hval] at hdet
  norm_num at hdet

end RealRooted
