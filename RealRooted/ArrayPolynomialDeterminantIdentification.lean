import RealRooted.ArrayPolynomialDeterminantRecurrence
import RealRooted.ArrayPolynomialSchur

open Matrix
open Polynomial

noncomputable section

namespace RealRooted

/-!
# Identification of the array determinant

This file identifies the lower-Hessenberg determinant recurrence with the
totally nonnegative determinant polynomial used for `A262704`.
-/

/-- The weighted lower shift associated with a sequence of nonzero scale
factors. -/
def scaledLowerShiftFin (N : ℕ) (d : Fin (N + 1) → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i j => if i.val = j.val + 1 then d i / d j else 0

lemma scaledLowerShiftFin_mul_scaledLowerFin (N : ℕ)
    (d : Fin (N + 1) → ℝ) (hd : ∀ i, d i ≠ 0) :
    scaledLowerShiftFin N d * scaledLowerFin N d = scaledLowerFin N d - 1 := by
  classical
  ext i k
  simp only [Matrix.mul_apply]
  rcases i with ⟨_ | r, hir⟩
  · by_cases hk : k = ⟨0, hir⟩
    · subst k
      simp [scaledLowerShiftFin, scaledLowerFin, hd]
    · have hk' : k ≠ (0 : Fin (N + 1)) := by simpa using hk
      simp [scaledLowerShiftFin, scaledLowerFin, hk', Ne.symm hk']
  · let j₀ : Fin (N + 1) := ⟨r, by omega⟩
    rw [Finset.sum_eq_single j₀]
    · by_cases hk : k.val ≤ r
      · have hkj₀ : k ≤ j₀ := hk
        have hki : k ≤ (⟨r + 1, hir⟩ : Fin (N + 1)) := by
          exact Fin.mk_le_mk.mpr (hk.trans (Nat.le_succ r))
        have hik : (⟨r + 1, hir⟩ : Fin (N + 1)) ≠ k := by
          intro h
          have hv : r + 1 = k.val := by simpa using congrArg Fin.val h
          omega
        simp [scaledLowerShiftFin, scaledLowerFin, j₀, hkj₀, hki, hik]
        field_simp [hd]
      · by_cases hkeq : k.val = r + 1
        · have hki : k = (⟨r + 1, hir⟩ : Fin (N + 1)) := Fin.ext hkeq
          subst k
          simp [scaledLowerShiftFin, scaledLowerFin, j₀, hd]
        · have hkj₀ : ¬k ≤ j₀ := by
            intro h
            exact hk h
          have hki : ¬k ≤ (⟨r + 1, hir⟩ : Fin (N + 1)) := by
            change ¬k.val ≤ r + 1
            omega
          have hik : (⟨r + 1, hir⟩ : Fin (N + 1)) ≠ k := by
            intro h
            exact hkeq (congrArg Fin.val h).symm
          simp [scaledLowerShiftFin, scaledLowerFin, j₀, hkj₀, hki, hik]
    · intro j hj hne
      have hval : r ≠ j.val := by
        intro h
        apply hne
        apply Fin.ext
        simp [j₀, h]
      simp [scaledLowerShiftFin, hval]
    · simp [j₀]

/-- The unit lower-bidiagonal matrix that inverts a scaled lower-ones
matrix. -/
def scaledLowerDifferenceFin (N : ℕ) (d : Fin (N + 1) → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  1 - scaledLowerShiftFin N d

theorem scaledLowerDifferenceFin_mul_scaledLowerFin (N : ℕ)
    (d : Fin (N + 1) → ℝ) (hd : ∀ i, d i ≠ 0) :
    scaledLowerDifferenceFin N d * scaledLowerFin N d = 1 := by
  rw [scaledLowerDifferenceFin, sub_mul, one_mul,
    scaledLowerShiftFin_mul_scaledLowerFin N d hd]
  abel

lemma scaledLowerShiftFin_mul_apply_succ (N : ℕ)
    (d e : Fin (N + 1) → ℝ) (r : ℕ) (hr : r + 1 < N + 1)
    (j : Fin (N + 1)) :
    (scaledLowerShiftFin N d * scaledLowerShiftFin N e)
        ⟨r + 1, hr⟩ j =
      (d ⟨r + 1, hr⟩ / d ⟨r, by omega⟩) *
        (if r = j.val + 1 then e ⟨r, by omega⟩ / e j else 0) := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨r, by omega⟩ : Fin (N + 1))]
  · simp [scaledLowerShiftFin]
  · intro k hk hne
    have hval : r ≠ k.val := by
      intro h
      apply hne
      apply Fin.ext
      simpa using h.symm
    simp [scaledLowerShiftFin, hval]
  · simp

/-- The two lower-bidiagonal factors whose inverse is `arrayKernelFin`. -/
def arrayBandBaseFin (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  scaledLowerDifferenceFin N arrayUScale *
    scaledLowerDifferenceFin N arrayVScale

theorem arrayBandBaseFin_mul_arrayKernelFin (N : ℕ) :
    arrayBandBaseFin N * arrayKernelFin N = 1 := by
  rw [arrayBandBaseFin, arrayKernelFin, mul_assoc,
    ← mul_assoc (scaledLowerDifferenceFin N arrayVScale),
    scaledLowerDifferenceFin_mul_scaledLowerFin N arrayVScale
      (fun i => (arrayVScale_pos i).ne'), one_mul,
    scaledLowerDifferenceFin_mul_scaledLowerFin N arrayUScale
      (fun i => (arrayUScale_pos i).ne')]

/-- First lower-bidiagonal weight. -/
def arrayUWeight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) ^ 2 * ((n : ℝ) - 1))

/-- Second lower-bidiagonal weight. -/
def arrayVWeight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * ((n : ℝ) - 1) ^ 2)

lemma arrayUScale_succ_div (N r : ℕ) (hr : r + 1 < N + 1) :
    arrayUScale (N := N) ⟨r + 1, hr⟩ / arrayUScale (N := N) ⟨r, by omega⟩ =
      arrayUWeight (r + 2) := by
  have hf : (Nat.factorial r : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
  have hr2 : (r : ℝ) + 2 ≠ 0 := by positivity
  unfold arrayUScale arrayUWeight
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.factorial_succ]
  push_cast
  field_simp [hf, hr1, hr2]
  rw [show (r : ℝ) + 2 - 1 = (r : ℝ) + 1 by ring,
    show ((r : ℝ) + 1) * ((r : ℝ) + 1 + 1) ^ 2 =
      ((r : ℝ) + 1) * ((r : ℝ) + 2) ^ 2 by ring,
    mul_div_cancel_left₀ _ hr1]

lemma arrayVScale_succ_div (N r : ℕ) (hr : r + 1 < N + 1) :
    arrayVScale (N := N) ⟨r + 1, hr⟩ / arrayVScale (N := N) ⟨r, by omega⟩ =
      arrayVWeight (r + 2) := by
  have hf : (Nat.factorial r : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
  have hr2 : (r : ℝ) + 2 ≠ 0 := by positivity
  have hrsq : 1 + (r : ℝ) * 2 + (r : ℝ) ^ 2 ≠ 0 := by
    have hp : 0 < ((r : ℝ) + 1) ^ 2 := sq_pos_of_pos (by positivity)
    nlinarith
  unfold arrayVScale arrayVWeight
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.factorial_succ]
  push_cast
  field_simp [hf, hr1, hr2]
  rw [show (r : ℝ) + 2 - 1 = (r : ℝ) + 1 by ring,
    show ((r : ℝ) + 1) ^ 2 * ((r : ℝ) + 1 + 1) =
      ((r : ℝ) + 1) ^ 2 * ((r : ℝ) + 2) by ring,
    mul_div_cancel_left₀ _ (pow_ne_zero 2 hr1)]

lemma arrayUWeight_add_arrayVWeight (n : ℕ) (hn : 2 ≤ n) :
    arrayUWeight n + arrayVWeight n = alphaC n := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  unfold arrayUWeight arrayVWeight alphaC
  field_simp
  ring

lemma arrayUWeight_mul_arrayVWeight_pred (n : ℕ) (hn : 3 ≤ n) :
    arrayUWeight n * arrayVWeight (n - 1) = betaC n := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have hpoly : 4 - (n : ℝ) * 4 + (n : ℝ) ^ 2 ≠ 0 := by
    have hp : 0 < ((n : ℝ) - 2) ^ 2 := sq_pos_of_ne_zero hn2
    nlinarith
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  unfold arrayUWeight arrayVWeight betaC
  rw [hcast]
  field_simp [hpoly]
  rw [show (n : ℝ) - 1 - 1 = (n : ℝ) - 2 by ring,
    div_self (pow_ne_zero 2 hn2)]

lemma scaledLowerShiftFin_arrayUScale_apply_succ (N r : ℕ)
    (hr : r + 1 < N + 1) (j : Fin (N + 1)) :
    scaledLowerShiftFin N arrayUScale ⟨r + 1, hr⟩ j =
      if r = j.val then arrayUWeight (r + 2) else 0 := by
  by_cases h : r = j.val
  · have hj : j = (⟨r, by omega⟩ : Fin (N + 1)) := Fin.ext h.symm
    rw [hj]
    simp [scaledLowerShiftFin, arrayUScale_succ_div N r hr]
  · simp [scaledLowerShiftFin, h]

lemma scaledLowerShiftFin_arrayVScale_apply_succ (N r : ℕ)
    (hr : r + 1 < N + 1) (j : Fin (N + 1)) :
    scaledLowerShiftFin N arrayVScale ⟨r + 1, hr⟩ j =
      if r = j.val then arrayVWeight (r + 2) else 0 := by
  by_cases h : r = j.val
  · have hj : j = (⟨r, by omega⟩ : Fin (N + 1)) := Fin.ext h.symm
    rw [hj]
    simp [scaledLowerShiftFin, arrayVScale_succ_div N r hr]
  · simp [scaledLowerShiftFin, h]

lemma arrayBandBaseFin_apply (N : ℕ) (i j : Fin (N + 1)) :
    arrayBandBaseFin N i j =
      if i = j then 1
      else if i.val = j.val + 1 then -alphaC (i.val + 1)
      else if i.val = j.val + 2 then betaC (i.val + 1)
      else 0 := by
  classical
  simp only [arrayBandBaseFin, scaledLowerDifferenceFin, sub_mul, one_mul,
    mul_sub, mul_one]
  rcases i with ⟨_ | r, hir⟩
  · simp [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
      scaledLowerShiftFin]
  · simp only [Matrix.sub_apply, Matrix.one_apply]
    rw [scaledLowerShiftFin_mul_apply_succ]
    rw [arrayUScale_succ_div N r hir,
      scaledLowerShiftFin_arrayUScale_apply_succ N r hir,
      scaledLowerShiftFin_arrayVScale_apply_succ N r hir]
    by_cases hsub : r = j.val
    · have hij : (⟨r + 1, hir⟩ : Fin (N + 1)) ≠ j := by
        intro h
        have hv : r + 1 = j.val := by simpa using congrArg Fin.val h
        omega
      have hrow1 : r + 1 = j.val + 1 := by omega
      have hinner : r ≠ j.val + 1 := by omega
      simp only [if_neg hij, if_pos hsub, if_pos hrow1, if_neg hinner,
        mul_zero, sub_zero]
      rw [show 0 - arrayUWeight (r + 2) - arrayVWeight (r + 2) =
        -(arrayUWeight (r + 2) + arrayVWeight (r + 2)) by ring]
      rw [arrayUWeight_add_arrayVWeight (r + 2) (by omega)]
    · by_cases hsub2 : r = j.val + 1
      · have hij : (⟨r + 1, hir⟩ : Fin (N + 1)) ≠ j := by
          intro h
          have hv : r + 1 = j.val := by simpa using congrArg Fin.val h
          omega
        have hnot1 : r + 1 ≠ j.val + 1 := by omega
        have hrow2 : r + 1 = j.val + 2 := by omega
        have hratio :
            arrayVScale (N := N) ⟨r, by omega⟩ / arrayVScale (N := N) j =
              arrayVWeight (r + 1) := by
          subst r
          simpa using arrayVScale_succ_div N j.val (by omega)
        have hprod :
            arrayUWeight (r + 2) * arrayVWeight (r + 1) = betaC (r + 2) := by
          simpa using arrayUWeight_mul_arrayVWeight_pred (r + 2) (by omega)
        simp only [if_neg hij, if_neg hsub, if_pos hsub2, if_neg hnot1,
          if_pos hrow2, sub_zero, zero_sub]
        rw [hratio, hprod]
        ring
      · by_cases hdiag : r + 1 = j.val
        · have hij : (⟨r + 1, hir⟩ : Fin (N + 1)) = j := Fin.ext hdiag
          simp only [if_pos hij, if_neg hsub, if_neg hsub2, sub_zero]
          ring
        · have hnot1 : r + 1 ≠ j.val + 1 := by omega
          have hnot2 : r + 1 ≠ j.val + 2 := by omega
          have hij : (⟨r + 1, hir⟩ : Fin (N + 1)) ≠ j := by
            intro h
            exact hdiag (by simpa using congrArg Fin.val h)
          simp only [if_neg hij, if_neg hsub, if_neg hsub2, if_neg hnot1,
            if_neg hnot2, sub_zero, zero_sub]
          ring

lemma arrayBandBaseFin_det (N : ℕ) : (arrayBandBaseFin N).det = 1 := by
  have hdet := congrArg Matrix.det (arrayBandBaseFin_mul_arrayKernelFin N)
  simpa [Matrix.det_mul] using hdet

lemma arrayBandPolynomialMatrix_eq (N : ℕ) :
    (arrayBandBaseFin N).map Polynomial.C +
        (Polynomial.X : ℝ[X]) • (upperBidiagonalFin N 0).map Polynomial.C =
      lowerHessenbergTwo (fun n => Polynomial.C (alphaC n))
        (fun n => Polynomial.C (betaC n)) Polynomial.X (N + 1) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [arrayBandBaseFin_apply, lowerHessenbergTwo,
      upperBidiagonalFin_apply]
  · have hji : j ≠ i := Ne.symm hij
    by_cases hsuper : j.val = i.val + 1
    · have hfalse1 : i.val ≠ i.val + 1 + 1 := by omega
      have hfalse2 : i.val ≠ i.val + 1 + 2 := by omega
      simp [arrayBandBaseFin_apply, lowerHessenbergTwo,
        upperBidiagonalFin_apply, hij, hji, hsuper, hfalse1, hfalse2]
    · by_cases hsub : i.val = j.val + 1
      · have hsub2 : i.val ≠ j.val + 2 := by omega
        simp [arrayBandBaseFin_apply, lowerHessenbergTwo,
          upperBidiagonalFin_apply, hij, hji, hsub]
        have hfalse : j.val ≠ j.val + 1 + 1 := by omega
        simp [hfalse]
      · by_cases hsub2 : i.val = j.val + 2
        · simp [arrayBandBaseFin_apply, lowerHessenbergTwo,
            upperBidiagonalFin_apply, hij, hji, hsub2]
          have hfalse : j.val ≠ j.val + 2 + 1 := by omega
          simp [hfalse]
        · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
          simp only [Matrix.add_apply, map_apply, Matrix.smul_apply,
            upperBidiagonalFin_apply, smul_eq_mul,
            lowerHessenbergTwo_apply, arrayBandBaseFin_apply, if_neg hij,
            if_neg hsub, if_neg hsub2, if_neg hji, if_neg hsuper,
            if_neg hval, map_zero, mul_zero, add_zero]

lemma arrayBandBaseFin_map_mul_arrayDetMatrix (N : ℕ) :
    (arrayBandBaseFin N).map Polynomial.C *
        (1 + (Polynomial.X : ℝ[X]) •
          (arrayKernelShiftFin N).map Polynomial.C) =
      (arrayBandBaseFin N).map Polynomial.C +
        (Polynomial.X : ℝ[X]) •
          (upperBidiagonalFin N 0).map Polynomial.C := by
  rw [mul_add, mul_one, Algebra.mul_smul_comm]
  congr 1
  rw [arrayKernelShiftFin, arrayPerturbedKernelFin, Matrix.map_mul,
    ← mul_assoc, ← Matrix.map_mul, arrayBandBaseFin_mul_arrayKernelFin]
  simp

/-- The normalized array polynomial in its lower-Hessenberg determinant
form. -/
def arrayNormalizedDeterminant (n : ℕ) : ℝ[X] :=
  (lowerHessenbergTwo (fun m => Polynomial.C (alphaC m))
    (fun m => Polynomial.C (betaC m)) Polynomial.X n).det

lemma arrayNormalizedDeterminant_succ_eq (N : ℕ) :
    arrayNormalizedDeterminant (N + 1) = arrayDetPolynomialFin N := by
  rw [arrayNormalizedDeterminant, ← arrayBandPolynomialMatrix_eq,
    ← arrayBandBaseFin_map_mul_arrayDetMatrix, Matrix.det_mul]
  have hdetMap : ((arrayBandBaseFin N).map Polynomial.C).det = 1 := by
    calc
      ((arrayBandBaseFin N).map Polynomial.C).det =
          Polynomial.C (arrayBandBaseFin N).det :=
        (RingHom.map_det Polynomial.C (arrayBandBaseFin N)).symm
      _ = 1 := by simp [arrayBandBaseFin_det]
  rw [hdetMap, one_mul]
  rfl

theorem arrayNormalizedDeterminant_isPFPolynomial (n : ℕ) :
    IsPFPolynomial (arrayNormalizedDeterminant n) := by
  cases n with
  | zero => simpa [arrayNormalizedDeterminant] using isPFPolynomial_one
  | succ N =>
      rw [arrayNormalizedDeterminant_succ_eq]
      exact arrayDetPolynomialFin_isPFPolynomial N

theorem arrayNormalizedDeterminant_recurrence (n : ℕ) :
    arrayNormalizedDeterminant (n + 3) =
      arrayNormalizedDeterminant (n + 2) +
        Polynomial.C (alphaC (n + 3)) * Polynomial.X *
          arrayNormalizedDeterminant (n + 1) +
        Polynomial.C (betaC (n + 3)) * Polynomial.X ^ 2 *
          arrayNormalizedDeterminant n := by
  exact lowerHessenbergTwo_det_recurrence
    (fun m => Polynomial.C (alphaC m))
    (fun m => Polynomial.C (betaC m)) Polynomial.X n

end RealRooted
