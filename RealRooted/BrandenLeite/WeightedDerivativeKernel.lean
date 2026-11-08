module

public import RealRooted.VeroneseSection
import RealRooted.ClassicalHurwitzMatrix.Stability.Lace
public import RealRooted.BrandenLeite.WeightedDerivativeKernel.Basic
import RealRooted.Derivative.Interlacing
import RealRooted.BrandenLeite.WeightedDerivativeKernel.Polynomial
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.FinTruncation
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
import Mathlib.Tactic

/-! # Total nonnegativity of weighted derivative kernels

For a real-rooted polynomial `F` with nonnegative coefficients, the weighted derivative
kernel `weightedDerivativeKernel κ F.coeff` is totally nonnegative for `κ ≥ 0`.
The proof factors its finite sections as the product of the derivative/value matrix
`derivativeValueMatrix F n`, built from the interlacing pair `(F', F)` as an upper Lace
matrix (`upperLacePair`), and the sparse derivative contraction. -/

@[expose] public section

open Polynomial Matrix RealRooted.BrandenLeite

namespace RealRooted

/-- Two upper Toeplitz coefficient families, interleaved as columns. -/
def upperLacePair (a b : ℕ → ℝ) : Matrix ℕ ℕ ℝ :=
  fun i j ↦ if j / 2 ≤ i then
    if j % 2 = 0 then a (i - j / 2) else b (i - j / 2)
  else 0

/-- A finite upper Lace matrix is the reversal of the transpose of the lower
Lace matrix with its coefficient families exchanged. -/
theorem upperLacePair_fin_eq (a b : ℕ → ℝ) (n : ℕ) :
    (upperLacePair a b).submatrix (Fin.val : Fin n → ℕ)
      (Fin.val : Fin (2 * n) → ℕ) =
    ((lacePair b a).submatrix (Fin.val : Fin (2 * n) → ℕ)
      (Fin.val : Fin n → ℕ)).transpose.submatrix Fin.rev Fin.rev := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  have hquot : (2 * n - (j.val + 1)) / 2 = n - (j.val / 2 + 1) := by lia
  have hpar : (2 * n - (j.val + 1)) % 2 = 0 ↔ j.val % 2 ≠ 0 := by lia
  have horder : n - (i.val + 1) ≤ n - (j.val / 2 + 1) ↔ j.val / 2 ≤ i.val := by lia
  have hdiff : n - (j.val / 2 + 1) - (n - (i.val + 1)) = i.val - j.val / 2 := by lia
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Fin.val_rev,
    upperLacePair, lacePair, Matrix.of_apply, toeplitz_apply, hquot, hpar,
    horder, hdiff]
  by_cases h : j.val / 2 ≤ i.val
  · by_cases hp : j.val % 2 = 0
    · simp [h, hp]
    · simp [h, hp]
  · simp [h]

/-- Total nonnegativity of the lower Lace pair controls every finite upper
Lace block. -/
theorem FullyInterlacingPair.upperLacePair_fin {a b : ℕ → ℝ}
    (h : FullyInterlacingPair b a) (n : ℕ) :
    ((upperLacePair a b).submatrix (Fin.val : Fin n → ℕ)
      (Fin.val : Fin (2 * n) → ℕ)).IsTotallyNonnegRect := by
  rw [upperLacePair_fin_eq]
  exact ((h.toRect.submatrix
    (rows := (Fin.val : Fin (2 * n) → ℕ)) (cols := (Fin.val : Fin n → ℕ))
    (fun _ _ hij ↦ hij) (fun _ _ hij ↦ hij)).transpose).finRev

/-- The finite derivative/value column family used in the kernel factorization. -/
noncomputable def derivativeValueMatrix (F : ℝ[X]) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (2 * n + 1)) ℝ :=
  (upperLacePair F.derivative.coeff F.coeff).submatrix Fin.val Fin.val

/-- Even columns of an upper Lace pair come from the first coefficient family. -/
theorem upperLacePair_two_mul (a b : ℕ → ℝ) (i j : ℕ) :
    upperLacePair a b i (2 * j) = if j ≤ i then a (i - j) else 0 := by
  have h1 : 2 * j / 2 = j := by lia
  have h2 : 2 * j % 2 = 0 := by lia
  simp [upperLacePair, h1, h2]

/-- Odd columns of an upper Lace pair come from the second coefficient family. -/
theorem upperLacePair_two_mul_add_one (a b : ℕ → ℝ) (i j : ℕ) :
    upperLacePair a b i (2 * j + 1) = if j ≤ i then b (i - j) else 0 := by
  have h1 : (2 * j + 1) / 2 = j := by lia
  have h2 : (2 * j + 1) % 2 = 1 := by lia
  simp [upperLacePair, h1, h2]

/-- Multiplying the derivative/value column family by the sparse contraction
recovers the leading weighted differential kernel. -/
theorem derivativeValueMatrix_mul_derivativeContraction (F : ℝ[X]) (n : ℕ) (κ : ℝ) :
    derivativeValueMatrix F n * derivativeContraction n κ =
      (weightedDerivativeKernel κ F.coeff).submatrix
        (Fin.val : Fin (n + 1) → ℕ) (Fin.val : Fin (n + 1) → ℕ) := by
  ext i j
  rw [mul_derivativeContraction_apply]
  change upperLacePair F.derivative.coeff F.coeff i.val (2 * j.val) * κ +
    (if hj : j.val = 0 then 0
      else upperLacePair F.derivative.coeff F.coeff i.val (2 * j.val - 1) * (j.val : ℝ)) =
    weightedDerivativeKernel κ F.coeff i.val j.val
  rw [upperLacePair_two_mul]
  rcases Nat.eq_zero_or_pos j.val with hj | hj
  · simp only [hj, dite_true, add_zero, Nat.zero_le, ite_true, Nat.sub_zero,
      Polynomial.coeff_derivative, weightedDerivativeKernel, Nat.cast_zero, zero_add]
    push_cast
    ring
  · obtain ⟨k, hk⟩ : ∃ k, j.val = k + 1 := ⟨j.val - 1, by lia⟩
    rw [dite_eq_right hj.ne', show 2 * j.val - 1 = 2 * k + 1 by lia,
      upperLacePair_two_mul_add_one]
    simp only [weightedDerivativeKernel, hk, Nat.add_le_add_iff_right]
    rcases lt_trichotomy k i.val with hki | hki | hki
    · obtain ⟨m, hm⟩ : ∃ m, i.val = k + 1 + m := ⟨i.val - (k + 1), by lia⟩
      have e1 : i.val - (k + 1) = m := by lia
      have e2 : i.val - k = m + 1 := by lia
      have e3 : i.val + 1 - (k + 1) = m + 1 := by lia
      rw [ite_eq_left (by lia : k + 1 ≤ i.val), ite_eq_left hki.le, ite_eq_left hki.le,
        e1, e2, e3, Polynomial.coeff_derivative]
      push_cast
      ring
    · have e : i.val - k = 0 := by lia
      have e' : i.val + 1 - (k + 1) = 0 := by lia
      rw [ite_eq_right (by lia : ¬ k + 1 ≤ i.val), ite_eq_left hki.le, ite_eq_left hki.le, e, e']
      push_cast
      ring
    · rw [ite_eq_right (by lia : ¬ k + 1 ≤ i.val), ite_eq_right (by lia : ¬ k ≤ i.val),
        ite_eq_right (by lia : ¬ k ≤ i.val)]
      simp

/-- A nonconstant real-rooted polynomial with nonnegative coefficients has a
TN derivative/value coefficient matrix. -/
theorem derivativeValueMatrix_isTotallyNonnegRect {F : ℝ[X]}
    (hF : F.Splits) (hnn : HasNonnegCoeffs F) (hdeg : F.natDegree ≠ 0) (n : ℕ) :
    (derivativeValueMatrix F n).IsTotallyNonnegRect := by
  have hpair :=
    (derivative_interlaces_of_natDegree_ne_zero hF hdeg).toStrictInterl.fullyInterlacingPair
      hnn.derivative hnn
  have hU := hpair.upperLacePair_fin (n + 1)
  let cols : Fin (2 * n + 1) → Fin (2 * (n + 1)) := Fin.castLE (by lia)
  have hcols : StrictMono cols := by intro a b hab; exact hab
  have hsmall := hU.submatrix (strictMono_id) hcols
  exact hsmall


/-- Every finite weighted differential kernel of a real-rooted polynomial
with nonnegative coefficients is totally nonnegative. -/
theorem weightedDerivativeKernel_fin_isTotallyNonneg {F : ℝ[X]} (hF : F.Splits)
    (hnn : HasNonnegCoeffs F) {κ : ℝ} (hκ : 0 ≤ κ) (n : ℕ) :
    ((weightedDerivativeKernel κ F.coeff).submatrix
      (Fin.val : Fin (n + 1) → ℕ) (Fin.val : Fin (n + 1) → ℕ)).IsTotallyNonneg := by
  by_cases hdeg : F.natDegree = 0
  · have hconst := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    rw [hconst]
    exact weightedDerivativeKernel_C_fin_isTotallyNonneg _ _ (hnn 0) n
  · rw [← derivativeValueMatrix_mul_derivativeContraction]
    exact ((derivativeValueMatrix_isTotallyNonnegRect hF hnn hdeg n).mul
      (derivativeContraction_isTotallyNonnegRect n hκ)).toSquare

/-- The weighted differential kernel of a real-rooted polynomial with
nonnegative coefficients is totally nonnegative for every nonnegative weight. -/
theorem weightedDerivativeKernel_isTotallyNonneg {F : ℝ[X]} (hF : F.Splits)
    (hnn : HasNonnegCoeffs F) {κ : ℝ} (hκ : 0 ≤ κ) :
    (weightedDerivativeKernel κ F.coeff).IsTotallyNonneg := by
  apply Matrix.IsTotallyNonneg.of_fin_truncations
    (weightedDerivativeKernel κ F.coeff)
    (fun n ↦ (weightedDerivativeKernel κ F.coeff).submatrix
      (Fin.val : Fin (n + 1) → ℕ) (Fin.val : Fin (n + 1) → ℕ))
    (fun _ _ _ ↦ rfl)
  exact fun n ↦ weightedDerivativeKernel_fin_isTotallyNonneg hF hnn hκ n


end RealRooted
