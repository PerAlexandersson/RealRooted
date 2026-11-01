module

import RealRooted.AffineProperPosition
import RealRooted.AffineFamily
import RealRooted.QuadraticRoot
public import RealRooted.MatrixInterlacing.Converse

/-!
# Separated-characteristic interlacing matrices

This file defines the polynomial matrices associated with recurrences

`∏ i, (S - a i) P = X * ∏ j, (S - b j) P`

whose two characteristic root families are separated.  The first `h - 1`
rows are bidiagonal; the remaining rows have a common `X`-column and upper
triangular constant entries.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

private lemma separatedCharacteristicQuadratic_eq (A E s t : ℝ) :
    ((C s * X + C t) * (X + C A) + (X + C E) : ℝ[X]) =
      C s * X ^ 2 + C (s * A + t + 1) * X + C (t * A + E) := by
  simp only [C_add, C_mul, C_1]
  ring

private lemma separatedCharacteristicQuadratic_splits
    {A E s t : ℝ} (hEA : E ≤ A) (hs : 0 < s) :
    ((C s * X + C t) * (X + C A) + (X + C E) : ℝ[X]).Splits := by
  rw [separatedCharacteristicQuadratic_eq]
  apply quadraticPoly_splits_of_le hs
  nlinarith [sq_nonneg (s * A - t - 1),
    mul_nonneg hs.le (sub_nonneg.mpr hEA)]

private lemma interl_separatedCharacteristicQuadratic_self
    {A E s t : ℝ} (hEA : E ≤ A) (hs : 0 < s) :
    Interl
      ((C s * X + C t) * (X + C A) + (X + C E))
      ((C s * X + C t) * (X + C A) + (X + C E)) := by
  exact Interl.refl fun _ ↦ separatedCharacteristicQuadratic_splits hEA hs

private lemma interl_separatedCharacteristicLinear_quadratic
    {A E B D s t : ℝ}
    (hEA : E ≤ A) (hD : 0 ≤ D) (hDB : D ≤ B)
    (hBE : B * E ≤ D * A) (hs : 0 < s) (ht : 0 < t) :
    Interl
      ((C s * X + C t) * C B + C D)
      ((C s * X + C t) * (X + C A) + (X + C E)) := by
  by_cases hB0 : B = 0
  · have hD0 : D = 0 := by linarith
    simp [hB0, hD0, interl_zero_left]
  have hB : 0 < B := lt_of_le_of_ne (hD.trans hDB) (Ne.symm hB0)
  apply interl_linear_quadratic_of_eval_nonpos
  · rw [affine_mul_C_add_C]
    exact natDegree_linear (mul_ne_zero hs.ne' hB.ne')
  · rw [separatedCharacteristicQuadratic_eq]
    exact natDegree_quadratic hs.ne'
  · exact separatedCharacteristicQuadratic_splits hEA hs
  · unfold HasPosLeadingCoeff
    rw [separatedCharacteristicQuadratic_eq, leadingCoeff_quadratic hs.ne']
    exact hs
  · intro r hr
    have hroot : s * B * r + (t * B + D) = 0 := by
      simpa [affine_mul_C_add_C, Polynomial.IsRoot.def] using hr
    have hr_nonpos : r ≤ 0 := by
      nlinarith [mul_pos hs hB, mul_pos ht hB]
    rw [separatedCharacteristicQuadratic_eq]
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
    have hscaled :
        B * (s * r ^ 2 + (s * A + t + 1) * r + (t * A + E)) =
          (B - D) * r + (B * E - D * A) := by
      linear_combination (r + A) * hroot
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hDB) hr_nonpos]

private lemma interl_separatedCharacteristicConstant_X
    {A B D s t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hs : 0 < s) (ht : 0 < t) :
    Interl
      ((C s * X + C t) * C B + C D)
      ((C s * X + C t) * C A + X) := by
  by_cases hB0 : B = 0
  · refine interl_congr (p' := C D)
      (q' := C (s * A + 1) * X + C (t * A)) ?_ ?_ ?_
    · simp [hB0]
    · simp only [C_add, C_mul, C_1]
      ring
    · exact interl_C_affine_linear (by positivity)
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  refine interl_congr
    (p' := C (s * B) * X + C (t * B + D))
    (q' := C (s * A + 1) * X + C (t * A)) ?_ ?_ ?_
  · simp only [C_add, C_mul]
    ring
  · simp only [C_add, C_mul, C_1]
    ring
  · apply interl_affine_linear_affine_linear_of_cross
    · positivity
    · positivity
    · nlinarith [mul_nonneg hs.le hA, mul_nonneg ht.le hB,
        mul_nonneg (mul_nonneg hs.le hA) (mul_nonneg ht.le hB)]

private lemma interl_separatedCharacteristicConstant_affineMulX
    {B D s t : ℝ} (hD : 0 ≤ D) (hDB : D ≤ B)
    (hs : 0 < s) (ht : 0 < t) :
    Interl
      ((C s * X + C t) * C B + C D)
      ((C s * X + C t) * X + X) := by
  by_cases hB0 : B = 0
  · have hD0 : D = 0 := by linarith
    simp [hB0, hD0, interl_zero_left]
  have hBpos : 0 < B := lt_of_le_of_ne (hD.trans hDB) (Ne.symm hB0)
  rw [show ((C s * X + C t) * X + X : ℝ[X]) =
    X * (C s * X + C (t + 1)) by
      simp only [C_add, C_1]
      ring]
  convert interl_affine_to_X_mul_affine
    (u := s) (v := t + 1) (U := B * s) (V := B * t + D)
    hs (mul_pos hBpos hs) (by nlinarith) (by positivity) (by positivity) using 1
  simp only [C_add, C_mul]
  ring

private lemma interl_separatedCharacteristicConstant_pencils
    {A B c D s t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : 0 ≤ c) (hD : 0 ≤ D) (hdet : B * c ≤ A * D)
    (hs : 0 < s) :
    Interl ((C s * X + C t) * C B + C D)
      ((C s * X + C t) * C A + C c) := by
  by_cases hB0 : B = 0
  · by_cases hA0 : A = 0
    · simp [hB0, hA0, interl_C_C]
    · refine interl_congr (p' := C D)
        (q' := C (s * A) * X + C (t * A + c)) ?_ ?_ ?_
      · simp [hB0]
      · simp only [C_add, C_mul]
        ring
      · exact interl_C_affine_linear (mul_pos hs (lt_of_le_of_ne hA (Ne.symm hA0)))
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  by_cases hA0 : A = 0
  · have hc0 : c = 0 := by nlinarith
    simp [hA0, hc0, interl_zero_right]
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  refine interl_congr
    (p' := C (s * B) * X + C (t * B + D))
    (q' := C (s * A) * X + C (t * A + c)) ?_ ?_ ?_
  · simp only [C_add, C_mul]
    ring
  · simp only [C_add, C_mul]
    ring
  · apply interl_affine_linear_affine_linear_of_cross
    · exact mul_pos hs hBpos
    · exact mul_pos hs hApos
    · nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hdet)]

private lemma interl_separatedCharacteristicAffineX_self
    {A E s t : ℝ} (hA : 0 ≤ A) (hs : 0 < s) :
    Interl ((C s * X + C t) * C A + (X + C E))
      ((C s * X + C t) * C A + (X + C E)) := by
  apply Interl.refl
  intro _
  have hsA : 0 < s * A + 1 := by positivity
  have hsplit := (isRealRooted_affine_factor (s := s * A + 1)
    (t := t * A + E) hsA).2
  convert hsplit using 1
  simp only [C_add, C_mul, C_1]
  ring

/-- The tail parameter belonging to a column of a separated-characteristic
matrix.  It is zero on the initial `h` columns and equals the corresponding
entry of `b` on the final `m` columns. -/
def separatedCharacteristicTailCoeff {h m : ℕ} (b : Fin m → ℝ)
    (j : Fin (h + m)) : ℝ :=
  if hj : h ≤ j then b ⟨j - h, by have := j.isLt; lia⟩ else 0

@[simp] theorem separatedCharacteristicTailCoeff_castAdd {h m : ℕ}
    (b : Fin m → ℝ) (j : Fin h) :
    separatedCharacteristicTailCoeff b (Fin.castAdd m j) = 0 := by
  simp [separatedCharacteristicTailCoeff, Fin.castAdd, Nat.not_le.mpr j.isLt]

@[simp] theorem separatedCharacteristicTailCoeff_natAdd {h m : ℕ}
    (b : Fin m → ℝ) (j : Fin m) :
    separatedCharacteristicTailCoeff b (Fin.natAdd h j) = b j := by
  simp [separatedCharacteristicTailCoeff, Fin.natAdd]

/-- Nonpositive tail parameters remain nonpositive after extension by zero. -/
theorem separatedCharacteristicTailCoeff_nonpos {h m : ℕ}
    {b : Fin m → ℝ} (hb : ∀ j, b j ≤ 0) (j : Fin (h + m)) :
    separatedCharacteristicTailCoeff b j ≤ 0 := by
  unfold separatedCharacteristicTailCoeff
  split
  · exact hb _
  · exact le_rfl

private def separatedCharacteristicScalarEntry {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ)
    (i j : Fin (h + m)) : ℝ :=
  if i = j then a i
  else if i < j then a j - separatedCharacteristicTailCoeff b j
  else 0

private lemma separatedCharacteristicScalarEntry_nonneg {h m : ℕ}
    {a : Fin (h + m) → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, b j ≤ 0) (i j : Fin (h + m)) :
    0 ≤ separatedCharacteristicScalarEntry a b i j := by
  unfold separatedCharacteristicScalarEntry
  split_ifs
  · exact ha i
  · exact sub_nonneg.mpr ((separatedCharacteristicTailCoeff_nonpos hb j).trans (ha j))
  · exact le_rfl

private lemma separatedCharacteristicScalarEntry_eq_zero_of_lt {h m : ℕ}
    {a : Fin (h + m) → ℝ} {b : Fin m → ℝ}
    {i j : Fin (h + m)} (hji : j < i) :
    separatedCharacteristicScalarEntry a b i j = 0 := by
  unfold separatedCharacteristicScalarEntry
  simp [hji.ne', hji.not_gt]

private lemma separatedCharacteristicScalarEntry_antitone_row {h m : ℕ}
    {a : Fin (h + m) → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, b j ≤ 0)
    (i₁ i₂ j : Fin (h + m)) (hi : i₁ ≤ i₂) :
    separatedCharacteristicScalarEntry a b i₂ j ≤
      separatedCharacteristicScalarEntry a b i₁ j := by
  have ht := separatedCharacteristicTailCoeff_nonpos hb j
  unfold separatedCharacteristicScalarEntry
  split_ifs <;> simp_all <;> grind

private lemma separatedCharacteristicScalarEntry_det_nonneg {h m : ℕ}
    {a : Fin (h + m) → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, b j ≤ 0)
    (i₁ i₂ j₁ j₂ : Fin (h + m)) (hi : i₁ ≤ i₂) (hj : j₁ ≤ j₂) :
    separatedCharacteristicScalarEntry a b i₁ j₂ *
        separatedCharacteristicScalarEntry a b i₂ j₁ ≤
      separatedCharacteristicScalarEntry a b i₁ j₁ *
        separatedCharacteristicScalarEntry a b i₂ j₂ := by
  have ht₁ := separatedCharacteristicTailCoeff_nonpos hb j₁
  have ht₂ := separatedCharacteristicTailCoeff_nonpos hb j₂
  have hu₁ : 0 ≤ a j₁ - separatedCharacteristicTailCoeff b j₁ := by
    linarith [ha j₁]
  have hu₂ : 0 ≤ a j₂ - separatedCharacteristicTailCoeff b j₂ := by
    linarith [ha j₂]
  have huu : 0 ≤ (a j₁ - separatedCharacteristicTailCoeff b j₁) *
      (a j₂ - separatedCharacteristicTailCoeff b j₂) := mul_nonneg hu₁ hu₂
  have hua₁ : 0 ≤ (a j₂ - separatedCharacteristicTailCoeff b j₂) * a j₁ :=
    mul_nonneg hu₂ (ha j₁)
  have hua₂ : 0 ≤ a j₁ * (a j₂ - separatedCharacteristicTailCoeff b j₂) :=
    mul_nonneg (ha j₁) hu₂
  have hua₃ : 0 ≤ (a j₁ - separatedCharacteristicTailCoeff b j₁) * a j₂ :=
    mul_nonneg hu₁ (ha j₂)
  have haa : 0 ≤ a j₁ * a j₂ := mul_nonneg (ha j₁) (ha j₂)
  have htailprod : 0 ≤ (a j₂ - separatedCharacteristicTailCoeff b j₂) *
      (-separatedCharacteristicTailCoeff b j₁) :=
    mul_nonneg hu₂ (neg_nonneg.mpr ht₁)
  unfold separatedCharacteristicScalarEntry
  split_ifs <;> simp_all <;> grind

private def separatedCharacteristicConstantEntry {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ)
    (i j : Fin (h + m)) : ℝ :=
  if (i : ℕ) + 1 < h then
    if j = i then a i else if (j : ℕ) = i + 1 then 1 else 0
  else separatedCharacteristicScalarEntry a b i j

private lemma separatedCharacteristicConstantEntry_nonneg {h m : ℕ}
    {a : Fin (h + m) → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, b j ≤ 0) (i j : Fin (h + m)) :
    0 ≤ separatedCharacteristicConstantEntry a b i j := by
  unfold separatedCharacteristicConstantEntry
  split
  · split_ifs
    · exact ha i
    · exact zero_le_one
    · exact le_rfl
  · exact separatedCharacteristicScalarEntry_nonneg ha hb i j

private lemma separatedCharacteristicConstantEntry_det_nonneg {h m : ℕ}
    {a : Fin (h + m) → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, b j ≤ 0)
    (i₁ i₂ j₁ j₂ : Fin (h + m)) (hi : i₁ ≤ i₂) (hj : j₁ ≤ j₂) :
    separatedCharacteristicConstantEntry a b i₁ j₂ *
        separatedCharacteristicConstantEntry a b i₂ j₁ ≤
      separatedCharacteristicConstantEntry a b i₁ j₁ *
        separatedCharacteristicConstantEntry a b i₂ j₂ := by
  by_cases hi₁ : (i₁ : ℕ) + 1 < h
  · by_cases hi₂ : (i₂ : ℕ) + 1 < h
    · have haa : 0 ≤ a i₁ * a i₂ := mul_nonneg (ha i₁) (ha i₂)
      unfold separatedCharacteristicConstantEntry
      simp only [hi₁, hi₂, ite_true]
      split_ifs <;> grind
    · have hs₁ := separatedCharacteristicScalarEntry_nonneg ha hb i₂ j₁
      have hs₂ := separatedCharacteristicScalarEntry_nonneg ha hb i₂ j₂
      have has₁ : 0 ≤ a i₁ * separatedCharacteristicScalarEntry a b i₂ j₁ :=
        mul_nonneg (ha i₁) hs₁
      have has₂ : 0 ≤ a i₁ * separatedCharacteristicScalarEntry a b i₂ j₂ :=
        mul_nonneg (ha i₁) hs₂
      unfold separatedCharacteristicConstantEntry
      simp only [hi₁, hi₂, ite_true, ite_false]
      unfold separatedCharacteristicScalarEntry at hs₁ hs₂ has₁ has₂ ⊢
      split_ifs <;> grind
  · have hi₂ : ¬(i₂ : ℕ) + 1 < h := by lia
    unfold separatedCharacteristicConstantEntry
    simp only [hi₁, hi₂, ite_false]
    exact separatedCharacteristicScalarEntry_det_nonneg ha hb i₁ i₂ j₁ j₂ hi hj

/-- The finite polynomial matrix for a separated-characteristic recurrence.

The matrix has size `h + m`.  Its first `h - 1` rows are bidiagonal.  Every
remaining row contains `X` in column zero, its diagonal parameter, and the
tail weights `a j - b j` strictly above the diagonal. -/
def separatedCharacteristicFinMatrix {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ) :
    Matrix (Fin (h + m)) (Fin (h + m)) ℝ[X] := fun i j ↦
  if _hi : (i : ℕ) + 1 < h then
    (if j = i then C (a i) else 0) +
      if (j : ℕ) = i + 1 then 1 else 0
  else
    (if (j : ℕ) = 0 then X else 0) +
      (if j = i then C (a i) else 0) +
        if i < j then C (a j - separatedCharacteristicTailCoeff b j) else 0

private lemma separatedCharacteristicFinMatrix_eq_constantEntry {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ) (i j : Fin (h + m)) :
    separatedCharacteristicFinMatrix a b i j =
      (if (i : ℕ) + 1 < h then 0 else if (j : ℕ) = 0 then X else 0) +
        C (separatedCharacteristicConstantEntry a b i j) := by
  by_cases hi : (i : ℕ) + 1 < h
  · simp only [separatedCharacteristicFinMatrix, separatedCharacteristicConstantEntry,
      hi, ite_true, zero_add]
    by_cases hji : j = i
    · subst j
      simp
    by_cases hsucc : (j : ℕ) = i + 1
    · simp [hji, hsucc]
    · simp [hji, hsucc]
  · simp only [separatedCharacteristicFinMatrix, separatedCharacteristicConstantEntry,
      hi, ite_false]
    by_cases hji : j = i
    · subst j
      simp [separatedCharacteristicScalarEntry]
    have hij' : i ≠ j := Ne.symm hji
    by_cases hij : i < j
    · simp [separatedCharacteristicScalarEntry, hji, hij', hij, C_sub]
    · simp [separatedCharacteristicScalarEntry, hji, hij', hij]

/-- Under the separated-sign hypotheses, every matrix entry has nonnegative
coefficients. -/
theorem separatedCharacteristicFinMatrix_hasNonnegCoeffs {h m : ℕ}
    {a : Fin (h + m) → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, b j ≤ 0) (i j : Fin (h + m)) :
    HasNonnegCoeffs (separatedCharacteristicFinMatrix a b i j) := by
  have hdiag : HasNonnegCoeffs (if j = i then C (a i) else 0) := by
    split
    · exact hasNonnegCoeffs_C (ha i)
    · exact hasNonnegCoeffs_zero
  have hsucc : HasNonnegCoeffs (if (j : ℕ) = i + 1 then 1 else 0) := by
    split
    · exact hasNonnegCoeffs_one
    · exact hasNonnegCoeffs_zero
  have hX : HasNonnegCoeffs (if (j : ℕ) = 0 then X else 0) := by
    split
    · exact hasNonnegCoeffs_X
    · exact hasNonnegCoeffs_zero
  have hupp : HasNonnegCoeffs
      (if i < j then C (a j - separatedCharacteristicTailCoeff b j) else 0) := by
    split
    · exact hasNonnegCoeffs_C (sub_nonneg.mpr
        ((separatedCharacteristicTailCoeff_nonpos hb j).trans (ha j)))
    · exact hasNonnegCoeffs_zero
  unfold separatedCharacteristicFinMatrix
  split
  · exact hdiag.add hsucc
  · exact (hX.add hdiag).add hupp

private lemma separatedCharacteristicFinMatrix_has2x2 {h m : ℕ}
    {a : Fin (h + m) → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, b j ≤ 0)
    (i₁ i₂ j₁ j₂ : Fin (h + m)) (hi : i₁ ≤ i₂) (hj : j₁ ≤ j₂) :
    Has2x2InterlacingProperty0
      (separatedCharacteristicFinMatrix a b i₁ j₁)
      (separatedCharacteristicFinMatrix a b i₁ j₂)
      (separatedCharacteristicFinMatrix a b i₂ j₁)
      (separatedCharacteristicFinMatrix a b i₂ j₂) := by
  rw [separatedCharacteristicFinMatrix_eq_constantEntry,
    separatedCharacteristicFinMatrix_eq_constantEntry,
    separatedCharacteristicFinMatrix_eq_constantEntry,
    separatedCharacteristicFinMatrix_eq_constantEntry]
  intro s t hs ht
  have hnonneg (i j : Fin (h + m)) :
      0 ≤ separatedCharacteristicConstantEntry a b i j :=
    separatedCharacteristicConstantEntry_nonneg ha hb i j
  have hdet := separatedCharacteristicConstantEntry_det_nonneg
    ha hb i₁ i₂ j₁ j₂ hi hj
  by_cases hi₁ : (i₁ : ℕ) + 1 < h
  · by_cases hi₂ : (i₂ : ℕ) + 1 < h
    · simpa [hi₁, hi₂] using interl_separatedCharacteristicConstant_pencils
        (hnonneg i₁ j₁) (hnonneg i₁ j₂) (hnonneg i₂ j₁)
        (hnonneg i₂ j₂) hdet hs
    · by_cases hj10 : (j₁ : ℕ) = 0
      · by_cases hj20 : (j₂ : ℕ) = 0
        · have hj_eq : j₁ = j₂ := Fin.ext (by lia)
          subst j₂
          simpa [hi₁, hi₂, hj10] using interl_separatedCharacteristicAffineX_self
            (hnonneg i₁ j₁) hs
        · have hj1i2 : j₁ < i₂ := by lia
          have hzero : separatedCharacteristicConstantEntry a b i₂ j₁ = 0 := by
            unfold separatedCharacteristicConstantEntry
            simp only [hi₂, ite_false]
            exact separatedCharacteristicScalarEntry_eq_zero_of_lt hj1i2
          simpa [hi₁, hi₂, hj10, hj20, hzero] using
            interl_separatedCharacteristicConstant_X
              (hnonneg i₁ j₁) (hnonneg i₁ j₂) (hnonneg i₂ j₂) hs ht
      · have hj20 : (j₂ : ℕ) ≠ 0 := by lia
        simpa [hi₁, hi₂, hj10, hj20] using
          interl_separatedCharacteristicConstant_pencils
            (hnonneg i₁ j₁) (hnonneg i₁ j₂) (hnonneg i₂ j₁)
            (hnonneg i₂ j₂) hdet hs
  · have hi₂ : ¬(i₂ : ℕ) + 1 < h := by lia
    have hanti (j : Fin (h + m)) :
        separatedCharacteristicConstantEntry a b i₂ j ≤
          separatedCharacteristicConstantEntry a b i₁ j := by
      unfold separatedCharacteristicConstantEntry
      simp only [hi₁, hi₂, ite_false]
      exact separatedCharacteristicScalarEntry_antitone_row ha hb i₁ i₂ j hi
    by_cases hj10 : (j₁ : ℕ) = 0
    · by_cases hj20 : (j₂ : ℕ) = 0
      · have hj_eq : j₁ = j₂ := Fin.ext (by lia)
        subst j₂
        simpa [hi₁, hi₂, hj10, separatedCharacteristicConstantEntry] using
          interl_separatedCharacteristicQuadratic_self (hanti j₁) hs
      · simpa [hi₁, hi₂, hj10, hj20, separatedCharacteristicConstantEntry] using
          interl_separatedCharacteristicLinear_quadratic
            (hanti j₁) (hnonneg i₂ j₂) (hanti j₂)
            (by simpa [mul_comm] using hdet) hs ht
    · have hj20 : (j₂ : ℕ) ≠ 0 := by lia
      simpa [hi₁, hi₂, hj10, hj20] using
        interl_separatedCharacteristicConstant_pencils
          (hnonneg i₁ j₁) (hnonneg i₁ j₂) (hnonneg i₂ j₁)
          (hnonneg i₂ j₂) hdet hs

/-- The row-major list form used by the matrix-interlacing API. -/
def separatedCharacteristicMatrix {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ) : List (List ℝ[X]) :=
  List.ofFn fun i ↦ List.ofFn fun j ↦ separatedCharacteristicFinMatrix a b i j

@[simp] theorem separatedCharacteristicMatrix_length {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ) :
    (separatedCharacteristicMatrix a b).length = h + m := by
  simp [separatedCharacteristicMatrix]

/-- Every row of a separated-characteristic matrix has the expected length. -/
theorem separatedCharacteristicMatrix_rect {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ) :
    ∀ row ∈ separatedCharacteristicMatrix a b, row.length = h + m := by
  intro row hrow
  simp only [separatedCharacteristicMatrix, List.mem_ofFn] at hrow
  obtain ⟨i, rfl⟩ := hrow
  simp

@[simp] theorem getElem_getElem_separatedCharacteristicMatrix {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ)
    (i j : Fin (h + m)) :
    (separatedCharacteristicMatrix a b)[i.1][j.1]'(by
      simp [separatedCharacteristicMatrix]) =
      separatedCharacteristicFinMatrix a b i j := by
  simp [separatedCharacteristicMatrix]

/-- Separated parameters give a matrix preserving zero-aware nonnegative
real-rooted interlacing vectors. -/
theorem separatedCharacteristicMatrix_preservesInterlacingSeq0 {h m : ℕ}
    {a : Fin (h + m) → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, b j ≤ 0) :
    PreservesInterlacingSeq0 (h + m) (separatedCharacteristicMatrix a b) := by
  apply (preservesInterlacingSeq0_iff (separatedCharacteristicMatrix a b)
    (separatedCharacteristicMatrix_rect a b)).2
  constructor
  · intro row hrow p hp
    simp only [separatedCharacteristicMatrix, List.mem_ofFn] at hrow
    obtain ⟨i, rfl⟩ := hrow
    simp only [List.mem_ofFn] at hp
    obtain ⟨j, rfl⟩ := hp
    exact separatedCharacteristicFinMatrix_hasNonnegCoeffs ha hb i j
  · intro i₁ i₂ j₁ j₂ hi hj
    let i₁' : Fin (h + m) := ⟨i₁, by simpa using i₁.isLt⟩
    let i₂' : Fin (h + m) := ⟨i₂, by simpa using i₂.isLt⟩
    have hi' : i₁' ≤ i₂' := hi
    have hi₁ : i₁ = ⟨i₁', by simp [separatedCharacteristicMatrix]⟩ := Fin.ext rfl
    have hi₂ : i₂ = ⟨i₂', by simp [separatedCharacteristicMatrix]⟩ := Fin.ext rfl
    rw [hi₁, hi₂]
    simp only [List.get_eq_getElem]
    simp only [separatedCharacteristicMatrix, List.getElem_ofFn]
    exact separatedCharacteristicFinMatrix_has2x2 ha hb i₁' i₂' j₁ j₂ hi' hj

/-- Shifted form of the preservation theorem.  The displayed matrix is the
parameter form of `M - ρ I`; its upper-triangular differences are unchanged by
the common shift. -/
theorem separatedCharacteristicMatrix_preservesInterlacingSeq0_shift
    {h m : ℕ} {a : Fin (h + m) → ℝ} {b : Fin m → ℝ} {ρ : ℝ}
    (ha : ∀ i, ρ ≤ a i) (hb : ∀ j, b j ≤ ρ) :
    PreservesInterlacingSeq0 (h + m)
      (separatedCharacteristicMatrix (fun i ↦ a i - ρ) (fun j ↦ b j - ρ)) := by
  apply separatedCharacteristicMatrix_preservesInterlacingSeq0
  · intro i
    exact sub_nonneg.mpr (ha i)
  · intro j
    exact sub_nonpos.mpr (hb j)

/-- The row-major action of the separated-characteristic matrix agrees with
ordinary matrix-vector multiplication. -/
theorem separatedCharacteristicMatrix_action {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ)
    (f : Fin (h + m) → ℝ[X]) :
    matPolyAction (separatedCharacteristicMatrix a b) (List.ofFn f) =
      List.ofFn (separatedCharacteristicFinMatrix a b |>.mulVec f) := by
  exact matPolyAction_ofFn _ _

end RealRooted
