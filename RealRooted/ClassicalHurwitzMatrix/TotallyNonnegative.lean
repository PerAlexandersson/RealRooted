import RealRooted.ClassicalHurwitzMatrix
import RealRooted.ClassicalHurwitzMatrix.Routh.TotallyNonnegative
import RealRooted.ClassicalHurwitzMatrix.Stability
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Total nonnegativity of the classical Hurwitz matrix

This file extracts the coefficient-sign consequences that follow immediately
from one-by-one minors of the corrected infinite matrix.
-/

namespace Matrix

open Polynomial

section Entries

variable {R : Type*} [Zero R]

@[simp]
theorem hurwitz_zero_row_apply (c : ℕ → R) (j : ℕ) :
    hurwitz c 0 j = c (2 * j) := by
  simp [hurwitz]

@[simp]
theorem hurwitz_one_row_succ_apply (c : ℕ → R) (j : ℕ) :
    hurwitz c 1 (j + 1) = c (2 * j + 1) := by
  rw [hurwitz_apply, if_pos (by lia)]
  congr 1

/-- If the initial coefficient vanishes, deleting the first row and column of
the classical Hurwitz matrix shifts the coefficient sequence by one. -/
theorem hurwitz_tail_of_zero {c : ℕ → R} (h0 : c 0 = 0) :
    hurwitz (fun n ↦ c (n + 1)) =
      (hurwitz c).submatrix (fun i ↦ i + 1) (fun j ↦ j + 1) := by
  ext i j
  simp only [hurwitz_apply, submatrix_apply]
  by_cases hij : i ≤ 2 * j
  · rw [if_pos hij, if_pos (by lia)]
    congr 1
    lia
  · rw [if_neg hij]
    by_cases hborder : i = 2 * j + 1
    · rw [hborder, if_pos (by lia)]
      rw [show 2 * (j + 1) - (2 * j + 1 + 1) = 0 by lia, h0]
    · rw [if_neg (by lia)]

end Entries

variable {R : Type*} [CommRing R] [PartialOrder R]

/-- Every coefficient occurs as an entry of the classical Hurwitz matrix, so
matrix total nonnegativity forces coefficientwise nonnegativity. -/
theorem IsTotallyNonneg.hurwitz_coeff_nonneg {c : ℕ → R}
    (h : (hurwitz c).IsTotallyNonneg) (n : ℕ) : 0 ≤ c n := by
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simpa [two_mul] using h.nonneg 0 j
  · have hentry := h.nonneg 1 (j + 1)
    rw [hurwitz_one_row_succ_apply] at hentry
    simpa [two_mul] using hentry

/-- Every finite leading principal section inherits total nonnegativity from
the infinite classical Hurwitz matrix. -/
theorem IsTotallyNonneg.hurwitzLeadingPrincipal {c : ℕ → R}
    (h : (hurwitz c).IsTotallyNonneg) (n : ℕ) :
    (Matrix.hurwitzLeadingPrincipal c n).IsTotallyNonneg :=
  h.submatrix Fin.val_strictMono Fin.val_strictMono

theorem IsTotallyNonneg.hurwitzLeadingPrincipal_det_nonneg {c : ℕ → R}
    (h : (hurwitz c).IsTotallyNonneg) (n : ℕ) :
    0 ≤ (Matrix.hurwitzLeadingPrincipal c n).det := by
  simpa [Matrix.hurwitzLeadingPrincipal] using
    h (rows := fun i : Fin n => i) (cols := fun i : Fin n => i)
      Fin.val_strictMono Fin.val_strictMono

/-- A zero-headed coefficient tail inherits total nonnegativity from the
classical Hurwitz matrix. -/
protected theorem IsTotallyNonneg.hurwitz_tail_of_zero {c : ℕ → R}
    (h : (hurwitz c).IsTotallyNonneg) (h0 : c 0 = 0) :
    (hurwitz fun n ↦ c (n + 1)).IsTotallyNonneg := by
  have hsucc : StrictMono (fun n : ℕ ↦ n + 1) := by
    intro i j hij
    lia
  rw [hurwitz_tail_of_zero h0]
  exact h.submatrix hsucc hsucc

/-- Removing a zero constant coefficient shifts the classical Hurwitz matrix
to a totally nonnegative submatrix. -/
protected theorem IsTotallyNonneg.hurwitz_divX_of_coeff_zero
    {p : Polynomial R} (h : (hurwitz p.coeff).IsTotallyNonneg)
    (h0 : p.coeff 0 = 0) :
    (hurwitz p.divX.coeff).IsTotallyNonneg := by
  rw [show p.divX.coeff = fun n ↦ p.coeff (n + 1) by
    funext n
    exact Polynomial.coeff_divX]
  exact h.hurwitz_tail_of_zero h0

section Real

/-- If the constant coefficient is positive but the linear coefficient
vanishes, total nonnegativity forces every odd-indexed coefficient to vanish. -/
theorem IsTotallyNonneg.hurwitz_odd_coeff_eq_zero_of_coeff_one_eq_zero
    {c : ℕ → ℝ} (h : (hurwitz c).IsTotallyNonneg)
    (h0 : 0 < c 0) (h1 : c 1 = 0) (n : ℕ) :
    c (2 * n + 1) = 0 := by
  cases n with
  | zero => simpa using h1
  | succ n =>
      have hrows : StrictMono (![1, 2] : Fin 2 → ℕ) := by decide
      have hcols : StrictMono (![1, n + 2] : Fin 2 → ℕ) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      have hminor := h hrows hcols
      have hcoeff : 0 ≤ c (2 * (n + 1) + 1) :=
        h.hurwitz_coeff_nonneg _
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, submatrix_cons_row,
        hurwitz_apply, Order.lt_two_iff, zero_le, le_mul_iff_one_le_right,
        submatrix_empty, Matrix.det_fin_two, Fin.isValue, cons_val',
        cons_val_zero, mul_one, Nat.one_le_ofNat, ↓reduceIte,
        Nat.add_one_sub_one, h1, Std.le_refl, tsub_self, cons_val_fin_one,
        cons_val_one, Nat.reduceLeDiff, zero_mul, ite_mul, zero_sub,
        Left.nonneg_neg_iff] at hminor
      rw [if_pos (by lia : 1 ≤ 2 * (n + 2))] at hminor
      rw [show 2 * (n + 2) - 1 = 2 * (n + 1) + 1 by lia] at hminor
      nlinarith

/-- The even rows of the classical Hurwitz matrix form the transpose of the
Toeplitz matrix of the even-indexed coefficient subsequence. -/
theorem hurwitz_even_submatrix_eq_toeplitz_transpose (c : ℕ → ℝ) :
    (hurwitz c).submatrix (fun i => 2 * i) id =
      (RealRooted.toeplitz fun n => c (2 * n)).transpose := by
  ext i j
  simp only [submatrix_apply, id_eq, transpose_apply,
    hurwitz_apply, RealRooted.toeplitz_apply]
  by_cases hij : i ≤ j
  · rw [if_pos hij, if_pos (by lia)]
    congr 1
    lia
  · rw [if_neg hij, if_neg (by lia)]

/-- Total nonnegativity of a classical Hurwitz matrix makes its even-indexed
coefficient subsequence Pólya-frequency. -/
theorem IsTotallyNonneg.hurwitz_even_isPolyaFreqSeq
    {c : ℕ → ℝ} (h : (hurwitz c).IsTotallyNonneg) :
    RealRooted.IsPolyaFreqSeq (fun n => c (2 * n)) := by
  have hrows : StrictMono (fun i : ℕ => 2 * i) := by
    intro i j hij
    lia
  have hsub := h.submatrix hrows strictMono_id
  rw [hurwitz_even_submatrix_eq_toeplitz_transpose] at hsub
  simpa [RealRooted.IsPolyaFreqSeq] using hsub.toRect.transpose.toSquare

/-- The even contraction of a polynomial inherits a Pólya-frequency
coefficient sequence from total nonnegativity of its classical Hurwitz matrix. -/
theorem IsTotallyNonneg.hurwitz_contract_two_isPolyaFreqSeq
    {p : Polynomial ℝ} (h : (hurwitz p.coeff).IsTotallyNonneg) :
    RealRooted.IsPolyaFreqSeq (Polynomial.contract 2 p).coeff := by
  have hpf := h.hurwitz_even_isPolyaFreqSeq
  convert hpf using 1
  funext n
  rw [Polynomial.coeff_contract (by decide), Nat.mul_comm]

/-- The classical Hurwitz matrix of a nonnegative constant polynomial is
totally nonnegative. -/
theorem hurwitz_C_isTotallyNonneg (a : ℝ) (ha : 0 ≤ a) :
    (hurwitz (C a).coeff).IsTotallyNonneg := by
  have hscaled : (a • (1 : Matrix ℕ ℕ ℝ)).IsTotallyNonneg :=
    IsTotallyNonneg.smul IsTotallyNonneg.one a ha
  have hdouble : StrictMono (fun j : ℕ ↦ 2 * j) := by
    intro i j hij
    lia
  have hsub := hscaled.submatrix strictMono_id hdouble
  convert hsub using 1
  ext i j
  simp only [hurwitz_apply, coeff_C, submatrix_apply, smul_apply, one_apply,
    smul_eq_mul, id_eq]
  by_cases hle : i ≤ 2 * j
  · rw [if_pos hle]
    by_cases hij : i = 2 * j
    · subst i
      simp
    · have hdiff : 2 * j - i ≠ 0 := by lia
      simp [hdiff, hij]
  · rw [if_neg hle]
    have hij : i ≠ 2 * j := by lia
    simp [hij]

open RealRooted

/-- Total nonnegativity of the original Hurwitz matrix makes every coefficient
of the canonical Routh-reduced odd part nonnegative. -/
theorem IsTotallyNonneg.hurwitz_routhReducedOddPart_coeff_nonneg
    {odd even : ℝ[X]}
    (h : (hurwitz (oddEvenPolynomial odd even).coeff).IsTotallyNonneg)
    (hodd : 0 < odd.coeff 0) (n : ℕ) :
    0 ≤ (routhReducedOddPart (routhCoefficient odd even) odd even).coeff n := by
  have hrows : StrictMono (![1, 2] : Fin 2 → ℕ) := by decide
  have hcols : StrictMono (![1, n + 2] : Fin 2 → ℕ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hminor := h hrows hcols
  simp only [submatrix_cons_row, hurwitz_apply, Order.lt_two_iff, zero_le,
    le_mul_iff_one_le_right, submatrix_empty, Matrix.det_fin_two, Fin.isValue,
    cons_val', cons_val_zero, mul_one, Nat.one_le_ofNat, ↓reduceIte,
    Nat.add_one_sub_one, Std.le_refl, tsub_self, cons_val_fin_one,
    cons_val_one, Nat.reduceLeDiff] at hminor
  rw [if_pos (by lia : 1 ≤ 2 * (n + 2))] at hminor
  rw [show 2 * (n + 2) - 1 = 2 * (n + 1) + 1 by lia,
    show 2 * (n + 2) - 2 = 2 * (n + 1) by lia] at hminor
  rw [show (0 : ℕ) = 2 * 0 by rfl,
    coeff_oddEvenPolynomial_even,
    show (1 : ℕ) = 2 * 0 + 1 by rfl,
    coeff_oddEvenPolynomial_odd] at hminor
  have hzero : (oddEvenPolynomial odd even).coeff 0 = even.coeff 0 := by
    simpa using coeff_oddEvenPolynomial_even odd even 0
  rw [hzero] at hminor
  have hdet :
      0 ≤ odd.coeff 0 * even.coeff (n + 1) -
        odd.coeff (n + 1) * even.coeff 0 := by
    simpa [Matrix.det_fin_two, Matrix.hurwitz,
      coeff_oddEvenPolynomial_even, coeff_oddEvenPolynomial_odd] using hminor
  rw [coeff_routhReducedOddPart, routhCoefficient]
  rw [show even.coeff (n + 1) - even.coeff 0 / odd.coeff 0 * odd.coeff (n + 1) =
      (odd.coeff 0 * even.coeff (n + 1) -
        odd.coeff (n + 1) * even.coeff 0) / odd.coeff 0 by
    field_simp]
  exact div_nonneg hdet hodd.le

/-- Under the same positive-pivot hypothesis, the canonical Routh-reduced
polynomial has nonnegative coefficients. -/
theorem IsTotallyNonneg.hurwitz_routhReducedPolynomial_hasNonnegCoeffs
    {odd even : ℝ[X]}
    (h : (hurwitz (oddEvenPolynomial odd even).coeff).IsTotallyNonneg)
    (hodd : 0 < odd.coeff 0) :
    HasNonnegCoeffs
      (routhReducedPolynomial (routhCoefficient odd even) odd even) := by
  intro n
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [show k + k = 2 * k by lia, routhReducedPolynomial,
      coeff_oddEvenPolynomial_even]
    have hcoeff := h.hurwitz_coeff_nonneg (2 * k + 1)
    simpa [coeff_oddEvenPolynomial_odd] using hcoeff
  · rw [routhReducedPolynomial, coeff_oddEvenPolynomial_odd]
    exact h.hurwitz_routhReducedOddPart_coeff_nonneg hodd k

/-- The classical Hurwitz matrix of `X + a` is totally nonnegative for every
nonnegative `a`. -/
theorem hurwitz_X_add_C_isTotallyNonneg (a : ℝ) (ha : 0 ≤ a) :
    (hurwitz (X + C a : ℝ[X]).coeff).IsTotallyNonneg := by
  have hred : routhReducedPolynomial a 1 (C a) = 1 := by
    simp [routhReducedPolynomial, routhReducedOddPart, oddEvenPolynomial]
  have hred_tn :
      (hurwitz (routhReducedPolynomial a 1 (C a)).coeff).IsTotallyNonneg := by
    rw [hred]
    simpa using hurwitz_C_isTotallyNonneg 1 zero_le_one
  have htn := hred_tn.hurwitz_oddEvenPolynomial_of_routhReduced ha (by simp)
  simpa [oddEvenPolynomial, add_comm] using htn

end Real

end Matrix

namespace RealRooted

/-- Total nonnegativity of the corrected Hurwitz matrix supplies the
coefficient-sign half of the project's `IsHurwitzStable` predicate. -/
theorem hasNonnegCoeffs_of_classicalHurwitzMatrix_isTotallyNonneg
    {p : Polynomial ℝ} (h : (Matrix.hurwitz p.coeff).IsTotallyNonneg) :
    HasNonnegCoeffs p :=
  h.hurwitz_coeff_nonneg

/-- If the constant coefficient is nonzero, matrix total nonnegativity makes
the classical sign normalization strictly positive. -/
theorem coeff_zero_pos_of_classicalHurwitzMatrix_isTotallyNonneg
    {p : Polynomial ℝ} (h : (Matrix.hurwitz p.coeff).IsTotallyNonneg)
    (h0 : p.coeff 0 ≠ 0) : 0 < p.coeff 0 :=
  lt_of_le_of_ne (h.hurwitz_coeff_nonneg 0) h0.symm

/-- Once root exclusion is proved, corrected-matrix total nonnegativity
supplies the remaining coefficient half of `IsHurwitzStable`. -/
theorem isHurwitzStable_of_classicalHurwitzMatrix_isTotallyNonneg
    {p : Polynomial ℝ} (h : (Matrix.hurwitz p.coeff).IsTotallyNonneg)
    (hroot : IsRightHalfPlaneStable (complexify p)) : IsHurwitzStable p :=
  ⟨hasNonnegCoeffs_of_classicalHurwitzMatrix_isTotallyNonneg h, hroot⟩

/-- The strict classical Hurwitz criterion holds for every monic linear
polynomial. -/
theorem IsStrictlyHurwitzStable.classicalHurwitzMatrix_isTotallyNonneg_X_add_C
    {a : ℝ} (h : IsStrictlyHurwitzStable (Polynomial.X + Polynomial.C a)) :
    (Matrix.hurwitz
      ((Polynomial.X + Polynomial.C a : Polynomial ℝ).coeff)).IsTotallyNonneg :=
  Matrix.hurwitz_X_add_C_isTotallyNonneg a
    ((IsStrictlyHurwitzStable.X_add_C a).mp h).le

end RealRooted
