import RealRooted.PolyaFrequencyConvolution
import RealRooted.VeroneseSection

open Polynomial Matrix

noncomputable section

namespace RealRooted

/-!
# Hurwitz matrix criterion interface

This file records checked lemmas for the row-oriented Hurwitz matrix used by
the Lace and Veronese developments. The classical Hurwitz criterion does not
hold for this orientation, and neither does closure of total nonnegativity
under entrywise products; both are refuted below.
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
  simp

/-- Odd-row entry of the Hurwitz matrix of an arbitrary coefficient sequence. -/
theorem hurwitz_odd_row_apply (c : ℕ → ℝ) (i j : ℕ) :
    hurwitz c (2 * i + 1) j = if j ≤ i then c (2 * (i - j)) else 0 := by
  rw [hurwitz]
  simp only [Matrix.of_apply]
  rw [ite_eq_right (by lia : ¬ (2 * i + 1) % 2 = 0),
    show (2 * i + 1) / 2 = i by lia, toeplitz_apply]

/-- Every Hurwitz-matrix entry above the staircase vanishes. -/
theorem hurwitz_apply_eq_zero_of_lt (c : ℕ → ℝ) {i j : ℕ} (h : i < 2 * j) :
    hurwitz c i j = 0 := by
  rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m = 2 * m by ring, hurwitz_even_row_apply, ite_eq_right (by lia)]
  · subst hm
    rw [hurwitz_odd_row_apply, ite_eq_right (by lia)]

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

/- The row-oriented converse Hurwitz-matrix criterion is retained only beside
its checked counterexample `not_hurwitzMatrixTotallyNonnegativeToStableStatement`.
It is not a valid theorem for the current coefficient convention. -/

/-- Legacy row-oriented converse Hurwitz-matrix criterion.  The nonzero
hypothesis rules out the zero-polynomial typo, but the statement remains false
for the current row convention; see
`not_hurwitzMatrixTotallyNonnegativeToStableStatement`. -/
abbrev LegacyHurwitzMatrixTotallyNonnegativeToStableStatement : Prop :=
  ∀ ⦃p : ℝ[X]⦄, p ≠ 0 → (hurwitz p.coeff).IsTotallyNonneg → IsHurwitzStable p

/-- Entrywise product identity for Hurwitz matrices.  The Hurwitz matrix of a
coefficientwise product of sequences agrees, entrywise, with the product of
the two Hurwitz matrices. -/
theorem hurwitz_mul_entrywise (a b : ℕ → ℝ) (i j : ℕ) :
    hurwitz (fun n ↦ a n * b n) i j = hurwitz a i j * hurwitz b i j := by
  unfold hurwitz toeplitz
  simp_all

/-- Matrix form of `hurwitz_mul_entrywise`: the Hurwitz matrix of a
coefficientwise product is the entrywise product of the two Hurwitz matrices. -/
theorem hurwitz_mul_entrywise_matrix (a b : ℕ → ℝ) :
    hurwitz (fun n => a n * b n) =
      Matrix.of (fun i j => hurwitz a i j * hurwitz b i j) := by
  ext i j
  simpa using hurwitz_mul_entrywise a b i j

/-! ### Entrywise products of Hurwitz matrices: low-order minors -/

/-- Every entry of the entrywise product of two totally nonnegative Hurwitz
matrices is nonnegative. -/
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
    ((Matrix.of fun i j ↦ hurwitz a i j * hurwitz b i j).submatrix rows cols).det = 0 := by
  have : rows 0 ≤ rows 1 := hrows.monotone (by simp)
  have : rows 1 ≤ rows 2 := hrows.monotone (by simp)
  have : rows 0 ≤ rows 2 := hrows.monotone (by simp)
  have : cols 0 ≤ cols 1 := hcols.monotone (by simp)
  have : cols 1 ≤ cols 2 := hcols.monotone (by simp)
  have : cols 0 ≤ cols 2 := hcols.monotone (by simp)
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

/-- Every minor of size at most two of the entrywise product of two totally
nonnegative Hurwitz matrices is nonnegative.  This fails already for `3 × 3`
minors; see `not_hurwitz_schurProduct_det_fin_three_nonneg`. -/
theorem hurwitz_schurProduct_det_of_card_le_two {a b : ℕ → ℝ}
    (ha : (hurwitz a).IsTotallyNonneg) (hb : (hurwitz b).IsTotallyNonneg)
    {n : ℕ} {rows cols : Fin n → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hn : n ≤ 2) :
    0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det :=
  ha.hadamard_det_of_card_le_two hb hrows hcols hn

/-- In-band entry formula: on the nonzero staircase `2 * j ≤ i`, every Hurwitz
matrix entry is a single coefficient. -/
theorem hurwitz_apply_of_band (c : ℕ → ℝ) {i j : ℕ} (h : 2 * j ≤ i) :
    hurwitz c i j = c ((if i % 2 = 0 then i + 1 else i - 1) - 2 * j) := by
  rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m = 2 * m by ring, hurwitz_even_row_apply,
      ite_eq_left (by lia : j ≤ m), ite_eq_left (by lia : (2 * m) % 2 = 0)]
    grind
  · subst hm
    rw [hurwitz_odd_row_apply, ite_eq_left (by lia : j ≤ m),
      ite_eq_right (by lia : ¬ (2 * m + 1) % 2 = 0)]
    grind

/-- `StrictMono` for a two-element index vector. -/
private theorem strictMono_pair {x y : ℕ} (hxy : x < y) :
    StrictMono ![x, y] := by simp_all

/-- Triangular reduction along the top row.  If the top selected row lies below
the staircase of the middle column, then the two entries to the right of the
top-left corner vanish and the determinant reduces to a `2 × 2` Hadamard minor. -/
theorem hurwitz_schurProduct_det_fin_three_of_row0_below {a b : ℕ → ℝ}
    (ha : (hurwitz a).IsTotallyNonneg) (hb : (hurwitz b).IsTotallyNonneg)
    {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (h : rows 0 < 2 * cols 1) :
    0 ≤ ((Matrix.of fun i j ↦ hurwitz a i j * hurwitz b i j).submatrix rows cols).det := by
  have hc12 : cols 1 < cols 2 := hcols (by simp)
  have hr12 : rows 1 < rows 2 := hrows (by simp)
  have h2 : 0 ≤ ((Matrix.of fun i j ↦ hurwitz a i j * hurwitz b i j).submatrix
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
  linarith [mul_nonneg hM00 h2]

/-- Triangular reduction along the right column.  If the middle selected row lies
below the staircase of the last column, then the two entries above the
bottom-right corner vanish and the determinant reduces to a `2 × 2` Hadamard
minor. -/
theorem hurwitz_schurProduct_det_fin_three_of_row1_below {a b : ℕ → ℝ}
    (ha : (hurwitz a).IsTotallyNonneg) (hb : (hurwitz b).IsTotallyNonneg)
    {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (h : rows 1 < 2 * cols 2) :
    0 ≤ ((Matrix.of fun i j ↦ hurwitz a i j * hurwitz b i j).submatrix rows cols).det := by
  have hc01 : cols 0 < cols 1 := hcols (by simp)
  have hr01 : rows 0 < rows 1 := hrows (by simp)
  have h2 : 0 ≤ ((Matrix.of fun i j ↦ hurwitz a i j * hurwitz b i j).submatrix
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
  linarith [mul_nonneg hM22 h2]

/-! ### Band bookkeeping and the column-shift structure -/

/-- Arithmetic band bookkeeping for a `3 × 3` window. Under the two hypotheses
`2 * cols 1 ≤ rows 0` and `2 * cols 2 ≤ rows 1`, monotonicity of the selected
rows and columns forces every selected entry except possibly the top-right
corner `(0, 2)` onto the nonzero staircase. -/
theorem hurwitz_schurProduct_core_inband_entries
    {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (h01 : 2 * cols 1 ≤ rows 0) (h12 : 2 * cols 2 ≤ rows 1) :
    2 * cols 0 ≤ rows 0 ∧ 2 * cols 0 ≤ rows 1 ∧ 2 * cols 1 ≤ rows 1 ∧
      2 * cols 0 ≤ rows 2 ∧ 2 * cols 1 ≤ rows 2 ∧ 2 * cols 2 ≤ rows 2 := by
  have : cols 0 ≤ cols 1 := hcols.monotone (by simp)
  have : cols 1 ≤ cols 2 := hcols.monotone (by simp)
  have : rows 0 ≤ rows 1 := hrows.monotone (by simp)
  have : rows 1 ≤ rows 2 := hrows.monotone (by simp)
  grind

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
  grind

/-- Iterated column-shift structure of a Hurwitz matrix: in the nonzero
staircase, moving `d` columns to the right is the same as moving `2 * d` rows
up.  This is the `hurwitz_col_shift` identity applied `d` times. -/
theorem hurwitz_col_shift_add (c : ℕ → ℝ) (j : ℕ) :
    ∀ (d i : ℕ), 2 * (j + d) ≤ i →
      hurwitz c i (j + d) = hurwitz c (i - 2 * d) j := by
  intro d
  induction d with
  | zero =>
      simp
  | succ d ih =>
      intro i h
      have h1 : hurwitz c i (j + (d + 1)) = hurwitz c (i - 2) (j + d) := by
        have hji : j + (d + 1) = (j + d) + 1 := by lia
        rw [hji, hurwitz_col_shift c (by lia)]
      grind

/-! ### The corner-zero `3 × 3` case -/

/-- Pure `3 × 3` algebraic form of the corner-zero case.  For two totally
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
  linarith [mul_nonneg detA (by positivity : (0 : ℝ) ≤ b00 * b11 * b22),
    mul_nonneg (mul_nonneg ha01 mA_r12c02) (mul_nonneg mB01 hb22),
    mul_nonneg (mul_nonneg ha12 mA02) (mul_nonneg hb00 mB_r12c12),
    mul_nonneg (mul_nonneg (mul_nonneg ha01 ha12) ha20) detB]

/-- Corner-zero `3 × 3` minors of the entrywise product of two totally
nonnegative Hurwitz matrices are nonnegative.  When the top-right corner
`(0, 2)` lies strictly above the staircase, the corresponding Hadamard-product
entry vanishes and the determinant is nonnegative by
`hadamard_det_fin_three_cornerZero_nonneg`. -/
theorem hurwitz_schurProduct_det_fin_three_nonneg_of_cornerZero {a b : ℕ → ℝ}
    (ha : (hurwitz a).IsTotallyNonneg) (hb : (hurwitz b).IsTotallyNonneg)
    {rows cols : Fin 3 → ℕ} (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hcz : rows 0 < 2 * cols 2) :
    0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det := by
  have cza : hurwitz a (rows 0) (cols 2) = 0 :=
    hurwitz_apply_eq_zero_of_lt a hcz
  have czb : hurwitz b (rows 0) (cols 2) = 0 :=
    hurwitz_apply_eq_zero_of_lt b hcz
  have hr01 : StrictMono ![rows 0, rows 1] := strictMono_pair (hrows (by simp))
  have hr02 : StrictMono ![rows 0, rows 2] := strictMono_pair (hrows (by simp))
  have hr12 : StrictMono ![rows 1, rows 2] := strictMono_pair (hrows (by simp))
  have hc01 : StrictMono ![cols 0, cols 1] := strictMono_pair (hcols (by simp))
  have hc02 : StrictMono ![cols 0, cols 2] := strictMono_pair (hcols (by simp))
  have hc12 : StrictMono ![cols 1, cols 2] := strictMono_pair (hcols (by simp))
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
    grind
  have detB :
      0 ≤ hurwitz b (rows 0) (cols 0) *
          (hurwitz b (rows 1) (cols 1) * hurwitz b (rows 2) (cols 2) -
            hurwitz b (rows 1) (cols 2) * hurwitz b (rows 2) (cols 1)) -
        hurwitz b (rows 0) (cols 1) *
          (hurwitz b (rows 1) (cols 0) * hurwitz b (rows 2) (cols 2) -
            hurwitz b (rows 1) (cols 2) * hurwitz b (rows 2) (cols 0)) := by grind
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
  simp_all

/-! ### A single-matrix corner-zeroed inequality is false

For a single totally nonnegative Hurwitz matrix, the `3 × 3` corner-zeroed
determinant (the honest minor minus the top-right corner contribution) can be
negative, even in first-column normal form.

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
  · rw [ite_eq_left h]
    simpa using hurwitz_col_shift_add c 0 j i (by grind)
  · rw [ite_eq_right h]
    exact hurwitz_apply_eq_zero_of_lt c (by lia)

/-- If the first column of a Hurwitz matrix is a Pólya-frequency sequence, then
the whole Hurwitz matrix is totally nonnegative. -/
theorem hurwitz_isTotallyNonneg_of_firstColumn_isPolyaFreqSeq (c : ℕ → ℝ)
    (h : IsPolyaFreqSeq fun k => hurwitz c k 0) :
    (hurwitz c).IsTotallyNonneg :=
  hurwitz_eq_toeplitz_firstColumn_submatrix c ▸
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
    rw [show m + m = 2 * m by ring, hurwitz_even_row_apply, ite_eq_left (Nat.zero_le m)]
    rw [show (X * (X + 1) : ℝ[X]) = X ^ 2 + X by ring]
    simp [hurwitzMatrixCriterionCounterexample, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
    lia
  · subst hm
    rw [hurwitz_odd_row_apply, ite_eq_left (Nat.zero_le m)]
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
    linarith
  · simp [hurwitzMatrixCriterionCounterexampleRoot, pow_succ,
      Complex.mul_re, Complex.mul_im]
    ring_nf
    linarith

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
    ¬ LegacyHurwitzMatrixTotallyNonnegativeToStableStatement := by
  intro h
  exact not_isHurwitzStable_hurwitzMatrixCriterionCounterexample
    (h (by
      intro hp
      have hc := congrArg (fun p : ℝ[X] => p.coeff 3) hp
      norm_num [hurwitzMatrixCriterionCounterexample, Polynomial.coeff_add,
        Polynomial.coeff_X_pow, Polynomial.coeff_one] at hc)
      hurwitzMatrixCriterionCounterexample_matrix_isTotallyNonneg)

/-- Counterexample first column: the binomial sequence `k ↦ C(16, k)`. -/
noncomputable def cexFirstColumn : ℕ → ℝ := fun k => (Nat.choose 16 k : ℝ)

/-- The binomial sequence `k ↦ C(16, k)` is a Pólya-frequency sequence. -/
theorem cexFirstColumn_isPolyaFreqSeq : IsPolyaFreqSeq cexFirstColumn := by
  have hpf := IsPolyaFreqSeq.prod_X_sub_C (Multiset.replicate 16 (-1 : ℝ))
    (by
      simp)
  have heq : ((Multiset.replicate 16 (-1 : ℝ)).map fun r ↦ X - C r).prod =
      (X + 1) ^ 16 := by
    rw [Multiset.map_replicate, Multiset.prod_replicate]
    simp
  have hfun :
      (fun n ↦ (((Multiset.replicate 16 (-1 : ℝ)).map fun r ↦ X - C r).prod).coeff n)
        = cexFirstColumn := by
    funext n
    rw [heq, Polynomial.coeff_X_add_one_pow]
    rfl
  simp_all

/-- The counterexample coefficient sequence: the parity swap of
`cexFirstColumn`, chosen so that the first column of `hurwitz cexA` is exactly
`cexFirstColumn`. -/
noncomputable def cexA : ℕ → ℝ :=
  fun n => if n % 2 = 0 then cexFirstColumn (n + 1) else cexFirstColumn (n - 1)

/-- The first column of `hurwitz cexA` is the binomial sequence. -/
theorem hurwitz_cexA_firstColumn (k : ℕ) : hurwitz cexA k 0 = cexFirstColumn k := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m = 2 * m by ring, hurwitz_even_row_apply, ite_eq_left (Nat.zero_le m),
      Nat.sub_zero]
    simp only [cexA, ite_eq_right (show ¬ (2 * m + 1) % 2 = 0 by lia), Nat.add_sub_cancel]
  · subst hm
    rw [hurwitz_odd_row_apply, ite_eq_left (Nat.zero_le m), Nat.sub_zero]
    simp only [cexA, ite_eq_left (show (2 * m) % 2 = 0 by lia)]

/-- The Hurwitz matrix of the counterexample is totally nonnegative. -/
theorem cexA_hurwitz_isTotallyNonneg : (hurwitz cexA).IsTotallyNonneg := by
  refine hurwitz_isTotallyNonneg_of_firstColumn_isPolyaFreqSeq cexA ?_
  simpa [hurwitz_cexA_firstColumn] using cexFirstColumn_isPolyaFreqSeq

/-- First-column form of the corner-zeroed single-matrix `3 × 3` determinant:
after normalizing the first selected column to `0`, the remaining columns are
shifted back to column `0` by moving rows up by twice the column index. -/
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

/-- The single-matrix first-column corner-zeroed inequality is false.  Even for
the concrete totally nonnegative Hurwitz matrix `hurwitz cexA`, the
corner-zeroed determinant at `rows = (9, 10, 11)`, `cols = (0, 1, 2)` is
negative. -/
theorem not_hurwitzFullBandCornerZeroedSingleFirstColDet_nonneg :
    ¬ ∀ {a : ℕ → ℝ},
      (hurwitz a).IsTotallyNonneg →
      ∀ {row0 row1 row2 col1 col2 : ℕ},
        row0 < row1 →
        row1 < row2 →
        0 < col1 →
        col1 < col2 →
        2 * col2 ≤ row0 →
        0 ≤ hurwitzFullBandCornerZeroedSingleFirstColDet a row0 row1 row2 col1 col2 := by
  intro H
  have key := H cexA_hurwitz_isTotallyNonneg (row0 := 9) (row1 := 10) (row2 := 11)
    (col1 := 1) (col2 := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  simp only [hurwitz_cexA_firstColumn, cexFirstColumn,
    hurwitzFullBandCornerZeroedSingleFirstColDet] at key
  norm_num [Nat.choose] at key

/-! ### Hurwitz staircase/Toeplitz normal form

The column-shift/staircase relation `hurwitz_col_shift_add` identifies, on the
nonzero staircase, a Hurwitz matrix entry with a single Toeplitz entry of its
column-`0` sequence.  This turns any fully in-band minor of the entrywise
product of two Hurwitz matrices into a Toeplitz minor of the pointwise product
of the two column-`0` sequences. -/

/-- Hurwitz staircase/Toeplitz relation.  On the nonzero staircase
`2 * j ≤ i`, the `(i, j)` entry of a Hurwitz matrix equals the `(i, 2 * j)`
entry of the Toeplitz matrix built from its column-`0` sequence
`n ↦ hurwitz c n 0`. -/
theorem hurwitz_eq_toeplitz_colZero (c : ℕ → ℝ) {i j : ℕ} (h : 2 * j ≤ i) :
    hurwitz c i j = toeplitz (fun n ↦ hurwitz c n 0) i (2 * j) := by
  have := hurwitz_col_shift_add c 0 j i (by grind)
  simp_all

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
    toeplitz_apply, ite_eq_left (hband i j), ite_eq_left (hband i j), ite_eq_left (hband i j)]

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

/-! ### Hadamard normal form for even-column Toeplitz minors

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
  · rw [ite_eq_left h, hurwitz_eq_toeplitz_colZero a h, hurwitz_eq_toeplitz_colZero b h]
    simp only [toeplitz_apply, ite_eq_left h]
  · rw [ite_eq_right h, hurwitz_apply_eq_zero_of_lt a (by lia), zero_mul]

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
  linarith [mul_nonneg hM01 hM10, mul_nonneg hN01 hN10,
    mul_nonneg (mul_nonneg hM01 hM10) hdN, mul_nonneg hdM (mul_nonneg hN01 hN10),
    mul_nonneg hdM hdN]

/-- Even-column Toeplitz minors of the column-`0` product sequence of two
totally nonnegative Hurwitz matrices are nonnegative at every size `n ≤ 2`.
This follows from the Hadamard normal form and the fact that the Hadamard
product of two totally nonnegative matrices has nonnegative determinant in
sizes `≤ 2`.  It fails at size three; see
`not_hurwitz_schurProduct_det_fin_three_nonneg`. -/
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

/-! ### Hurwitz normal form for even-column Toeplitz minors

The entrywise product of two Hurwitz matrices is again a Hurwitz matrix,
namely the Hurwitz matrix of the pointwise product of the two coefficient
sequences. -/

/-- The Hurwitz matrix of the pointwise product of two coefficient sequences is
the entrywise product of the two Hurwitz matrices. -/
theorem hurwitz_mul_apply (a b : ℕ → ℝ) (i j : ℕ) :
    hurwitz (fun k => a k * b k) i j = hurwitz a i j * hurwitz b i j := by
  rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m = 2 * m by ring, hurwitz_even_row_apply, hurwitz_even_row_apply,
      hurwitz_even_row_apply]
    simp_all
  · subst hm
    rw [hurwitz_odd_row_apply, hurwitz_odd_row_apply, hurwitz_odd_row_apply]
    simp_all

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
    · rw [ite_eq_left (by lia), ite_eq_left h, show 2 * m - 2 * j = 2 * (m - j) by lia,
        hurwitz_even_row_apply, hurwitz_even_row_apply]
      simp
    · grind
  · subst hm
    rw [hurwitz_odd_row_apply]
    by_cases h : j ≤ m
    · rw [ite_eq_left (by lia), ite_eq_left h, show 2 * m + 1 - 2 * j = 2 * (m - j) + 1 by lia,
        hurwitz_odd_row_apply, hurwitz_odd_row_apply]
      simp
    · grind

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

/-! ### The column-`0` product sequence need not be Pólya-frequency

Total nonnegativity of a Hurwitz matrix does not force its column-`0`
sequence to be Pólya-frequency, and the pointwise product of the column-`0`
sequences of two totally nonnegative Hurwitz matrices can fail to be
Pólya-frequency. -/

/-- If all odd-indexed entries of a coefficient sequence vanish, then every
even row of its Hurwitz matrix is identically zero. -/
theorem hurwitz_even_row_eq_zero_of_odd_zero {a : ℕ → ℝ}
    (hodd : ∀ n, a (2 * n + 1) = 0) (i j : ℕ) :
    hurwitz a (2 * i) j = 0 := by
  rw [hurwitz_even_row_apply]
  simp_all

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
      simp_all
    rw [hsub]
    refine heven ?_ hcols
    intro k1 k2 hk
    have h1 : rows k1 % 2 = 1 := hall k1
    have h2 : rows k2 % 2 = 1 := hall k2
    have hlt := hrows hk
    lia
  · obtain ⟨k, hk⟩ := not_forall.mp hall
    have : rows k % 2 = 0 := by simp_all
    have hzero : ∀ l, ((hurwitz a).submatrix rows cols) k l = 0 := by
      intro l
      simp only [Matrix.submatrix_apply]
      have hrk : rows k = 2 * (rows k / 2) := by lia
      rw [hrk]
      exact hurwitz_even_row_eq_zero_of_odd_zero hodd _ _
    exact le_of_eq (Matrix.det_eq_zero_of_row_eq_zero k hzero).symm

/-! ### Entrywise products of totally nonnegative Hurwitz matrices

Total nonnegativity of infinite Hurwitz matrices is not preserved by entrywise
products, already for a fully in-band `3 × 3` minor.  Garloff--Wagner,
*Hadamard products of stable polynomials are stable*, J. Math. Anal. Appl. 202
(1996), 797--809, Theorem 13, treats finite nonsingular Hurwitz matrices; it
does not cover arbitrary infinite, possibly singular matrices in the
row-oriented convention used here. -/

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

/-- The two infinite PF certificates reduce the fully in-band `3 × 3` minor
statement to an explicit minor with determinant `-4`, at rows `(5, 7, 9)` and
columns `(0, 1, 2)`. -/
theorem not_hurwitz_schurProduct_det_fin_three_nonneg_of_counterexamplePF
    (hleft : IsPolyaFreqSeq (fun n => hurwitzSchurCounterexampleLeft (2 * n)))
    (hright : IsPolyaFreqSeq (fun n => hurwitzSchurCounterexampleRight (2 * n))) :
    ¬ ∀ {a b : ℕ → ℝ},
      (hurwitz a).IsTotallyNonneg →
      (hurwitz b).IsTotallyNonneg →
      ∀ {rows cols : Fin 3 → ℕ},
        StrictMono rows →
        StrictMono cols →
        (∀ i j : Fin 3, 2 * cols j ≤ rows i) →
        0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det := by
  intro H
  have hleftTN : (hurwitz hurwitzSchurCounterexampleLeft).IsTotallyNonneg :=
    hurwitz_isTotallyNonneg_of_odd_zero hurwitzSchurCounterexampleLeft_odd_zero hleft
  have hrightTN : (hurwitz hurwitzSchurCounterexampleRight).IsTotallyNonneg :=
    hurwitz_isTotallyNonneg_of_odd_zero hurwitzSchurCounterexampleRight_odd_zero hright
  have hminor := H hleftTN hrightTN (rows := ![5, 7, 9])
    (cols := ![0, 1, 2]) (by decide) (by decide) (by decide)
  erw [Matrix.det_fin_three] at hminor
  norm_num [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, hurwitz, toeplitz,
    hurwitzSchurCounterexampleLeft, hurwitzSchurCounterexampleRight] at hminor

/-- Fully in-band `3 × 3` minors of the entrywise product of two totally
nonnegative Hurwitz matrices can be negative. -/
theorem not_hurwitz_schurProduct_det_fin_three_nonneg :
    ¬ ∀ {a b : ℕ → ℝ},
      (hurwitz a).IsTotallyNonneg →
      (hurwitz b).IsTotallyNonneg →
      ∀ {rows cols : Fin 3 → ℕ},
        StrictMono rows →
        StrictMono cols →
        (∀ i j : Fin 3, 2 * cols j ≤ rows i) →
        0 ≤ ((Matrix.of fun i j => hurwitz a i j * hurwitz b i j).submatrix rows cols).det := by
  apply not_hurwitz_schurProduct_det_fin_three_nonneg_of_counterexamplePF
  · simpa [hurwitzSchurCounterexampleLeft] using oneThenTwo_isPolyaFreqSeq
  · simpa [hurwitzSchurCounterexampleRight] using natSucc_isPolyaFreqSeq

/-- The unrestricted, infinite Hurwitz-matrix Schur-product statement is false:
the entrywise product of two totally nonnegative Hurwitz matrices need not be
totally nonnegative. -/
theorem not_hurwitz_schurProduct_isTotallyNonneg :
    ¬ ∀ {a b : ℕ → ℝ},
      (hurwitz a).IsTotallyNonneg →
      (hurwitz b).IsTotallyNonneg →
      (Matrix.of fun i j => hurwitz a i j * hurwitz b i j).IsTotallyNonneg :=
  fun H => not_hurwitz_schurProduct_det_fin_three_nonneg
    fun {_ _} ha hb {_ _} hrows hcols _hband => H ha hb hrows hcols

/-- Counterexample coefficient sequence `1 + X^2`. -/
def cexOddZero : ℕ → ℝ :=
  fun n => if n = 0 then 1 else if n = 2 then 1 else 0

/-- The odd-indexed coefficients of `cexOddZero` vanish. -/
theorem cexOddZero_odd_zero (n : ℕ) : cexOddZero (2 * n + 1) = 0 := by
  simp only [cexOddZero]
  simp

/-- The even coefficient subsequence of `cexOddZero` is `(1 + X)`, a
Pólya-frequency sequence. -/
theorem cexOddZero_even_isPolyaFreqSeq :
    IsPolyaFreqSeq (fun n ↦ cexOddZero (2 * n)) := by
  have h := IsPolyaFreqSeq.prod_X_sub_C (Multiset.replicate 1 (-1 : ℝ))
    (by
      simp)
  have heq :
      (fun n ↦
          (((Multiset.replicate 1 (-1 : ℝ)).map fun r ↦ X - C r).prod).coeff n)
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
            ite_eq_right (by lia : ¬ (1 : ℕ) = m + 2),
            ite_eq_right (by lia : ¬ m + 2 = 0), sub_zero]
        have hR : cexOddZero (2 * (m + 2)) = 0 := by
          simp only [cexOddZero]
          simp
        simp_all
  simp_all

/-- The Hurwitz matrix of `cexOddZero` is totally nonnegative. -/
theorem cexOddZero_hurwitz_isTotallyNonneg :
    (hurwitz cexOddZero).IsTotallyNonneg :=
  hurwitz_isTotallyNonneg_of_odd_zero cexOddZero_odd_zero
    cexOddZero_even_isPolyaFreqSeq

/-- Column-`0` value of `hurwitz cexOddZero` at row `1` is `1`. -/
theorem cexOddZero_col0_one : hurwitz cexOddZero 1 0 = 1 := by
  rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, hurwitz_odd_row_apply,
    ite_eq_left (Nat.zero_le 0)]
  simp [cexOddZero]

/-- Column-`0` value of `hurwitz cexOddZero` at row `2` is `0`. -/
theorem cexOddZero_col0_two : hurwitz cexOddZero 2 0 = 0 := by
  rw [show (2 : ℕ) = 2 * 1 from rfl,
    hurwitz_even_row_eq_zero_of_odd_zero cexOddZero_odd_zero]

/-- Column-`0` value of `hurwitz cexOddZero` at row `3` is `1`. -/
theorem cexOddZero_col0_three : hurwitz cexOddZero 3 0 = 1 := by
  rw [show (3 : ℕ) = 2 * 1 + 1 from rfl, hurwitz_odd_row_apply,
    ite_eq_left (Nat.zero_le 1)]
  simp [cexOddZero]

/-- The column-`0` product sequence of two totally nonnegative Hurwitz
matrices need not be Pólya-frequency.

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
  grind

end RealRooted
