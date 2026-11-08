/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import RealRooted.Mathlib.Algebra.Polynomial.LinearFactors
import RealRooted.BrandenLeite.WeightedDerivativeKernel
import RealRooted.BrandenLeite.PositiveLinearFactors
import RealRooted.BrandenLeite.PositivePowerFactors
import RealRooted.BrandenLeite.PositivePowerInterlacing
public import RealRooted.Mathlib.RingTheory.PowerSeries.AffineNegativePower
public import RealRooted.Mathlib.LinearAlgebra.Matrix.WeightedDerivativeKernel
public import RealRooted.Mathlib.LinearAlgebra.Matrix.Checkerboard
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Basic.Real.Basic
import RealRooted.TotallyNonnegPencil.StrictInterlacing
import RealRooted.Mathlib.LinearAlgebra.Matrix.CheckerboardAdjacent
import RealRooted.Mathlib.Algebra.Polynomial.Roots
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas
import RealRooted.Mathlib.LinearAlgebra.Matrix.Charpoly.DeterminantPencil
import RealRooted.Mathlib.LinearAlgebra.Matrix.LeadingSections
import Mathlib.Tactic

/-! # Optional simple roots and disjoint consecutive positive-power rows

For valuation-one numerators, a positive quadratic coefficient in the
denominator or numerator gives simple roots and disjoint consecutive rows.
These conclusions are stated separately from the (weak) oriented interlacing;
together they separate the roots of consecutive rows.
The logarithmic limit is not covered by this strengthening.
-/

public section

open Polynomial PowerSeries Matrix

namespace RealRooted.BrandenLeite

/-- Canonical valuation-one rows and the common TN matrix model have the
same root multiplicities after reflection. No TN hypothesis is needed for
this algebraic transport. -/
theorem affineNegativePowerCoeff_charpoly_root_data
    {κ : ℝ} (hκ : 0 < κ) (Q B : PowerSeries ℝ)
    (hQ : PowerSeries.constantCoeff Q = 1) (hB : PowerSeries.constantCoeff B = 0)
    (hB₁ : 0 < PowerSeries.coeff 1 B) (n : ℕ) (x : ℝ) :
    let M := ((weightedDerivativeKernel κ
      (fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k Q)).submatrix Fin.val Fin.val :
        Matrix (Fin n) (Fin n) ℝ)
    let L := ((weightedDerivativeKernel κ (fun k => PowerSeries.coeff k B)).submatrix
      Fin.val Fin.val : Matrix (Fin n) (Fin n) ℝ)
    let H := (checkerboard L)⁻¹ * M
    ((affineNegativePowerCoeff κ Q B n).IsRoot x ↔ H.charpoly.IsRoot (-x)) ∧
      (affineNegativePowerCoeff κ Q B n).rootMultiplicity x =
        H.charpoly.rootMultiplicity (-x) := by
  let M := ((weightedDerivativeKernel κ
    (fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k Q)).submatrix Fin.val Fin.val :
      Matrix (Fin n) (Fin n) ℝ)
  let L := ((weightedDerivativeKernel κ (fun k => PowerSeries.coeff k B)).submatrix
    Fin.val Fin.val : Matrix (Fin n) (Fin n) ℝ)
  let A := checkerboard L
  let H := A⁻¹ * M
  have hLdet : 0 < L.det :=
    det_weightedDerivativeKernel_fin_pos_of_coeff_one_pos hκ B hB hB₁ n
  have hAunit : IsUnit A.det := isUnit_det_checkerboard L hLdet.ne'.isUnit
  have hdet := det_weightedDerivativeKernel_affineNegativePowerCoeff κ Q B hQ hB n
  change det (M.map Polynomial.C + (Polynomial.X : ℝ[X]) • A.map Polynomial.C) =
    (n.factorial : ℝ[X]) * affineNegativePowerCoeff κ Q B n at hdet
  rw [Matrix.det_map_add_X_smul_eq_det_mul_of_mul_eq_one M A A⁻¹
      (A.mul_nonsing_inv hAunit),
    Matrix.det_X_smul_one_add_map_eq_C_mul_charpoly_comp_neg_X] at hdet
  have hpoly : Polynomial.C (n.factorial : ℝ) * affineNegativePowerCoeff κ Q B n =
      Polynomial.C (A.det * (-1 : ℝ) ^ n) * H.charpoly.comp (-Polynomial.X) := by
    simpa only [Fintype.card_fin, ← mul_assoc, ← Polynomial.C_mul,
      Polynomial.C_eq_natCast] using hdet.symm
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hc : A.det * (-1 : ℝ) ^ n ≠ 0 :=
    mul_ne_zero hAunit.ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  constructor
  · have hr : (Polynomial.C (n.factorial : ℝ) *
        affineNegativePowerCoeff κ Q B n).IsRoot x ↔
      (Polynomial.C (A.det * (-1 : ℝ) ^ n) *
        H.charpoly.comp (-Polynomial.X)).IsRoot x := by rw [hpoly]
    simpa only [Polynomial.IsRoot.def, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
      mul_eq_zero, hf, hc, false_or] using hr
  · have hm := congrArg (fun p : ℝ[X] => p.rootMultiplicity x) hpoly
    rw [Polynomial.rootMultiplicity_C_mul hf,
      Polynomial.rootMultiplicity_C_mul hc] at hm
    apply hm.trans
    simpa using Polynomial.rootMultiplicity_comp_C_mul_X_add_C
      H.charpoly (-1) 0 x (isUnit_iff_ne_zero.mpr (by norm_num))

/-- The first superdiagonal of the signed denominator kernel is positive when `Q(0) = 1`. -/
private theorem signedKernel_superdiagonal_pos {κ : ℝ} {Q : PowerSeries ℝ}
    (hQ : PowerSeries.constantCoeff Q = 1) {n : ℕ} (i : Fin n) :
    0 < ((weightedDerivativeKernel κ
      (fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k Q)).submatrix Fin.val Fin.val :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.castSucc i.succ := by
  have hQ₀ : PowerSeries.coeff 0 Q = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hQ
  have hi : i.val + 1 - (i.val + 1) = 0 := by lia
  simp only [Matrix.submatrix_apply, weightedDerivativeKernel,
    Fin.val_castSucc, Fin.val_succ, le_refl, ite_true, hi,
    Nat.cast_zero, mul_zero, add_zero, pow_zero, hQ₀, mul_one]
  positivity

/-- A positive quadratic coefficient of `Q` makes the first subdiagonal of the signed
denominator kernel positive. -/
private theorem signedKernel_subdiagonal_pos {κ : ℝ} (hκ : 0 < κ) {Q : PowerSeries ℝ}
    (hQ₂ : 0 < PowerSeries.coeff 2 Q) {n : ℕ} (i : Fin n) :
    0 < ((weightedDerivativeKernel κ
      (fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k Q)).submatrix Fin.val Fin.val :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.succ i.castSucc := by
  have hi : i.val + 1 + 1 - i.val = 2 := by lia
  simp only [Matrix.submatrix_apply, weightedDerivativeKernel,
    Fin.val_castSucc, Fin.val_succ, show i.val ≤ i.val + 1 + 1 by lia, ite_true, hi,
    pow_two, neg_one_mul, neg_neg, one_mul]
  exact mul_pos (by positivity) hQ₂

/-- A positive quadratic coefficient of `B` makes the first subdiagonal of the numerator
kernel positive. -/
private theorem numeratorKernel_subdiagonal_pos {κ : ℝ} (hκ : 0 < κ) {B : PowerSeries ℝ}
    (hB₂ : 0 < PowerSeries.coeff 2 B) {n : ℕ} (i : Fin n) :
    0 < ((weightedDerivativeKernel κ (fun k => PowerSeries.coeff k B)).submatrix
      Fin.val Fin.val : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.succ i.castSucc := by
  have hi : i.val + 1 + 1 - i.val = 2 := by lia
  simp only [Matrix.submatrix_apply, weightedDerivativeKernel,
    Fin.val_castSucc, Fin.val_succ, show i.val ≤ i.val + 1 + 1 by lia, ite_true, hi]
  exact mul_pos (by positivity) hB₂

/-- A negative linear coefficient of `Q` and `κ > 0` make the diagonal of the signed
denominator kernel positive. -/
private theorem signedKernel_diagonal_pos {κ : ℝ} (hκ : 0 < κ) {Q : PowerSeries ℝ}
    (hQ₁ : 0 < -PowerSeries.coeff 1 Q) {n : ℕ} (i : Fin n) :
    0 < ((weightedDerivativeKernel κ
      (fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k Q)).submatrix Fin.val Fin.val :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.castSucc i.castSucc := by
  have hi : i.val + 1 - i.val = 1 := by lia
  simp only [Matrix.submatrix_apply, weightedDerivativeKernel,
    Fin.val_castSucc, show i.val ≤ i.val + 1 by lia, ite_true,
    hi, pow_one, neg_one_mul, Nat.cast_one, mul_one]
  exact mul_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hκ) hQ₁

/-- Under the elementary second-coefficient strictness condition, TN kernel
models give simple roots and disjoint consecutive canonical rows. -/
theorem affineNegativePowerCoeff_simple_and_disjoint_of_kernels
    {κ : ℝ} (hκ : 0 < κ) (Q B : PowerSeries ℝ)
    (hQ : PowerSeries.constantCoeff Q = 1) (hB : PowerSeries.constantCoeff B = 0)
    (hB₁ : 0 < PowerSeries.coeff 1 B)
    (hQ₁ : 0 < -PowerSeries.coeff 1 Q)
    (hsecond : 0 < PowerSeries.coeff 2 Q ∨ 0 < PowerSeries.coeff 2 B)
    (n : ℕ)
    (hM : ((weightedDerivativeKernel κ
      (fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k Q)).submatrix Fin.val Fin.val :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).IsTotallyNonneg)
    (hL : ((weightedDerivativeKernel κ (fun k => PowerSeries.coeff k B)).submatrix
      Fin.val Fin.val : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).IsTotallyNonneg)
    (hMdet : ((weightedDerivativeKernel κ
      (fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k Q)).submatrix Fin.val Fin.val :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det ≠ 0) :
    (∀ x : ℝ, (affineNegativePowerCoeff κ Q B n).IsRoot x →
      (affineNegativePowerCoeff κ Q B n).rootMultiplicity x = 1) ∧
    (∀ x : ℝ, (affineNegativePowerCoeff κ Q B (n + 1)).IsRoot x →
      (affineNegativePowerCoeff κ Q B (n + 1)).rootMultiplicity x = 1) ∧
    ∀ x : ℝ, ¬((affineNegativePowerCoeff κ Q B n).IsRoot x ∧
      (affineNegativePowerCoeff κ Q B (n + 1)).IsRoot x) := by
  let M := ((weightedDerivativeKernel κ
    (fun k => (-1 : ℝ) ^ k * PowerSeries.coeff k Q)).submatrix Fin.val Fin.val :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
  let L := ((weightedDerivativeKernel κ (fun k => PowerSeries.coeff k B)).submatrix
    Fin.val Fin.val : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
  let H := (checkerboard L)⁻¹ * M
  have hLtri : L.IsLowerTriangular :=
    weightedDerivativeKernel_isLowerTriangular_fin κ B hB (n + 1)
  have hLdet : 0 < L.det :=
    det_weightedDerivativeKernel_fin_pos_of_coeff_one_pos hκ B hB hB₁ (n + 1)
  have hsuper : ∀ i : Fin n, 0 < M i.castSucc i.succ := fun i =>
    signedKernel_superdiagonal_pos hQ i
  have hsub : ∀ i : Fin n, 0 < M i.succ i.castSucc ∨
      (0 < L i.succ i.castSucc ∧ 0 < M i.castSucc i.castSucc) := fun i =>
    hsecond.imp (fun hQ₂ => signedKernel_subdiagonal_pos hκ hQ₂ i)
      fun hB₂ =>
        ⟨numeratorKernel_subdiagonal_pos hκ hB₂ i, signedKernel_diagonal_pos hκ hQ₁ i⟩
  obtain ⟨-, hfull, hsmall, hdisjoint, -⟩ :=
    hLtri.checkerboard_inv_mul_leading_charpoly_strictInterlaces
      hL hLdet hM hMdet hsuper hsub
  have hAunit := isUnit_det_checkerboard L hLdet.ne'.isUnit
  have hlead : H.submatrix Fin.castSucc Fin.castSucc =
      (checkerboard (L.submatrix Fin.castSucc Fin.castSucc))⁻¹ *
        M.submatrix Fin.castSucc Fin.castSucc := by
    dsimp only [H]
    rw [(isLowerTriangular_checkerboard hLtri).leading_submatrix_inv_mul hAunit,
      checkerboard_submatrix_castSucc]
  have hrowFull (x : ℝ) :=
    affineNegativePowerCoeff_charpoly_root_data hκ Q B hQ hB hB₁ (n + 1) x
  constructor
  · intro x hx
    have hd := affineNegativePowerCoeff_charpoly_root_data hκ Q B hQ hB hB₁ n x
    rw [hlead] at hsmall
    exact hd.2.trans (hsmall (-x) (hd.1.mp hx))
  constructor
  · intro x hx
    exact (hrowFull x).2.trans (hfull (-x) ((hrowFull x).1.mp hx))
  · intro x hx
    apply hdisjoint (-x)
    constructor
    · exact (hrowFull x).1.mp hx.2
    · rw [hlead]
      exact (affineNegativePowerCoeff_charpoly_root_data hκ Q B hQ hB hB₁ n x).1.mp hx.1

/-- A nonempty product of positive normalized linear factors has a positive
linear coefficient. -/
private theorem coeff_one_prod_one_add_C_mul_X_pos
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) :
    0 < (∏ i ∈ s, (1 + Polynomial.C (α i) * Polynomial.X : ℝ[X])).coeff 1 := by
  classical
  obtain ⟨i, hi⟩ := hs
  have hrest0 :
      (∏ j ∈ s.erase i, (1 + Polynomial.C (α j) * Polynomial.X : ℝ[X])).coeff 0 = 1 := by
    simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  have hrest1 : 0 ≤
      (∏ j ∈ s.erase i, (1 + Polynomial.C (α j) * Polynomial.X : ℝ[X])).coeff 1 := by
    exact hasNonnegCoeffs_prod_one_add_C_mul_X (s.erase i) α
      (fun j hj => (hα j (Finset.mem_of_mem_erase hj)).le) 1
  rw [← Finset.mul_prod_erase s
    (fun j => (1 + Polynomial.C (α j) * Polynomial.X : ℝ[X])) hi,
    Polynomial.mul_coeff_one]
  simpa [hrest0, Polynomial.coeff_one] using add_pos_of_nonneg_of_pos hrest1 (hα i hi)

/-- Optional strict separation for the valuation-one factored family:
every root is simple and consecutive polynomials have no common root when
one of the signed-denominator or numerator second coefficients is positive.
Combined with the checked weak oriented interlacing theorem, every root
comparison is then strict. -/
theorem affineNegativePowerCoeff_factor_simple_and_disjoint
    {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
    (hβ : ∀ j ∈ t, 0 ≤ β j) {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) (n : ℕ) :
    let Q : ℝ[X] := ∏ i ∈ s, (1 - Polynomial.C (α i) * Polynomial.X)
    let B : ℝ[X] := Polynomial.C c * Polynomial.X *
      ∏ j ∈ t, (1 + Polynomial.C (β j) * Polynomial.X)
    (0 < Q.coeff 2 ∨ 0 < B.coeff 2) →
    let q := fun m => affineNegativePowerCoeff κ (Q : PowerSeries ℝ) B m
    (∀ x : ℝ, (q n).IsRoot x → (q n).rootMultiplicity x = 1) ∧
      (∀ x : ℝ, (q (n + 1)).IsRoot x → (q (n + 1)).rootMultiplicity x = 1) ∧
      ∀ x : ℝ, ¬((q n).IsRoot x ∧ (q (n + 1)).IsRoot x) := by
  let Q : ℝ[X] := ∏ i ∈ s, (1 - Polynomial.C (α i) * Polynomial.X)
  let B : ℝ[X] := Polynomial.C c * Polynomial.X *
    ∏ j ∈ t, (1 + Polynomial.C (β j) * Polynomial.X)
  dsimp only
  intro hsecond
  have hQ0 : Q.coeff 0 = 1 := Polynomial.coeff_zero_prod_one_sub_C_mul_X s α
  have hB0 : B.coeff 0 = 0 := by
    simp [B, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  have hB1 : B.coeff 1 = c := by
    dsimp only [B]
    rw [mul_assoc, Polynomial.coeff_C_mul]
    rw [show 1 = 0 + 1 from rfl, Polynomial.coeff_X_mul]
    simp [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  have hQ1 : 0 < -Q.coeff 1 := by
    have hpos := coeff_one_prod_one_add_C_mul_X_pos s hs α hα
    rw [← Polynomial.prod_one_sub_C_mul_X_comp_neg_X s α] at hpos
    simpa [Q, Polynomial.coeff_comp_neg_X] using hpos
  obtain ⟨hQs, hQnn⟩ :=
    splits_and_hasNonnegCoeffs_prod_one_sub_C_mul_X_comp_neg_X s α fun i hi => (hα i hi).le
  have hBs : B.Splits := by
    simpa [B] using (Polynomial.Splits.C_mul_X_pow c 1).mul
      (Polynomial.splits_prod_one_add_C_mul_X t β)
  have hBnn : HasNonnegCoeffs B := by
    exact (hasNonnegCoeffs_C_mul hc.le hasNonnegCoeffs_X).mul
      (hasNonnegCoeffs_prod_one_add_C_mul_X t β hβ)
  apply affineNegativePowerCoeff_simple_and_disjoint_of_kernels hκ
    (Q : PowerSeries ℝ) B (by simpa using hQ0) (by simpa using hB0)
    (by simpa [hB1] using hc) (by simpa using hQ1)
    (by simpa only [Polynomial.coeff_coe] using hsecond) n
  · exact weightedDerivativeKernel_submatrix_signed_isTotallyNonneg hQs hQnn hκ.le _
  · exact weightedDerivativeKernel_submatrix_isTotallyNonneg hBs hBnn hκ.le _
  · have hd := det_weightedDerivativeKernel_prod_linear_comp_neg_X_pos
      s hs α hα hκ (n + 1)
    rw [Polynomial.coeff_comp_neg_X_eq_neg_one_pow_mul] at hd
    simpa only [Polynomial.coeff_coe] using hd.ne'

end RealRooted.BrandenLeite
