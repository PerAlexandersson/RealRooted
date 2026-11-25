module

import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
import RealRooted.Mathlib.LinearAlgebra.Matrix.LeadingSections
import RealRooted.PolyaFrequencyConvolution
import RealRooted.OscillatoryInterlacing
import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.BandedHessenberg
import RealRooted.Mathlib.LinearAlgebra.Matrix.Charpoly.DeterminantPencil
public import RealRooted.MatrixInterlacing.ThreeBidiagonalProduction
import RealRooted.TotallyNonnegPencil
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Charpoly
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Spectrum
public import RealRooted.MultiplierSequence
import RealRooted.MultiplierSequence.InvPochhammer
import RealRooted.Hadamard.SchurSzegoStrict
import RealRooted.Interlacing.Reversal
public import RealRooted.ExponentialRows.Insertion
import RealRooted.ExponentialRows.SubstitutionRows
import Mathlib.Tactic

/-!
# Matrices for two-edge clustering on balanced complete bipartite graphs

We construct the nested matrix family from the unpublished proof in
RealRooted issue #2647, https://github.com/PerAlexandersson/RealRooted/issues/2647.
The lower factors are `I + D/2` and `I + 3D/2`, where `D` has subdiagonal
`1, 2, ...`; the upper factor has ones on and above the diagonal.

We identify the determinant rows with the factorial coefficients of
`exp(z + u z(1+z/2)²)` and prove degree, simple negative roots and strict
consecutive interlacing, including after factorial compression and reversal.
The two resulting polynomial families have the required falling-factorial
coefficient rescaling. Their identification with graph packing counts remains
a separate, unproved counting identity; no graph enumeration theorem is claimed here.
-/

@[expose] public section

open Matrix Polynomial BigOperators

noncomputable section

namespace RealRooted.BipartiteClustering

/-- The lower factor `I + c D` in dimension `n`. -/
def lowerFactor (c : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  lowerBidiagonalFin n (fun _ => 1) (fun j => c * (j + 1))

/-- The upper triangular matrix with every entry on or above the diagonal equal to one. -/
def upperSum (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i ≤ j then 1 else 0

/-- The oscillatory matrix for the reversed, coefficient-rescaled clustering row. -/
def production (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  lowerFactor (1 / 2) n * lowerFactor (3 / 2) n * upperSum n

private lemma lowerFactor_lower (c : ℝ) (n : ℕ) :
    (lowerFactor c n).IsLowerTriangular := by
  intro i j h
  have hlt : i < j := h
  have hij : i ≠ j := ne_of_lt hlt
  have hv : ¬ i.val = j.val + 1 := by have := Fin.lt_def.mp hlt; lia
  simp [lowerFactor, lowerBidiagonalFin_apply, hij, hv]

private lemma lowerFactor_det (c : ℝ) (n : ℕ) : (lowerFactor c n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (lowerFactor_lower c n)]
  simp [lowerFactor]

private lemma lowerFactor_nonneg {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    (lowerFactor c n).IsTotallyNonneg := by
  apply isTotallyNonneg_lowerBidiagonalFin
  · simp
  · intro j
    positivity

private lemma upperSum_upper (n : ℕ) : (upperSum n).IsUpperTriangular := by
  intro i j h
  have hlt : j < i := h
  simp [upperSum, not_le.mpr hlt]

private lemma upperSum_det (n : ℕ) : (upperSum n).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (upperSum_upper n)]
  simp [upperSum]

private lemma upperSum_nonneg (n : ℕ) : (upperSum n).IsTotallyNonneg := by
  have h := constantOne_isPolyaFreqSeq.submatrix
    (Fin.val_strictMono (n := n)) (Fin.val_strictMono (n := n))
  convert h.transpose using 1
  ext i j
  simp [upperSum, Matrix.transpose_apply, Matrix.submatrix_apply, toeplitz_apply]

/-- Every clustering production matrix is totally nonnegative. -/
theorem production_isTotallyNonneg (n : ℕ) : (production n).IsTotallyNonneg :=
  ((lowerFactor_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n).mul
    (lowerFactor_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) n)).mul (upperSum_nonneg n)

/-- The production matrices are nonsingular, with determinant one. -/
@[simp] theorem production_det (n : ℕ) : (production n).det = 1 := by
  simp [production, Matrix.det_mul, lowerFactor_det, upperSum_det]

private lemma lowerFactor_leading (c : ℝ) (n : ℕ) :
    (lowerFactor c (n + 1)).submatrix Fin.castSucc Fin.castSucc = lowerFactor c n := by
  ext i j
  simp [lowerFactor, lowerBidiagonalFin_apply, Matrix.submatrix_apply]

private lemma upperSum_leading (n : ℕ) :
    (upperSum (n + 1)).submatrix Fin.castSucc Fin.castSucc = upperSum n := by
  ext i j
  simp [upperSum, Matrix.submatrix_apply]

/-- The leading principal block is exactly the preceding production matrix. -/
theorem production_leading (n : ℕ) :
    (production (n + 1)).submatrix Fin.castSucc Fin.castSucc = production n := by
  unfold production
  rw [Matrix.IsLowerTriangular.leading_submatrix_mul
    ((lowerFactor_lower (1 / 2) (n + 1)).mul (lowerFactor_lower (3 / 2) (n + 1))),
    Matrix.IsLowerTriangular.leading_submatrix_mul (lowerFactor_lower (1 / 2) (n + 1)),
    lowerFactor_leading, lowerFactor_leading, upperSum_leading]

private lemma mul_entry_pos {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsTotallyNonneg) (hB : B.IsTotallyNonneg)
    (i j k : Fin n) (ha : 0 < A i k) (hb : 0 < B k j) :
    0 < (A * B) i j := by
  rw [Matrix.mul_apply]
  exact lt_of_lt_of_le (mul_pos ha hb)
    (Finset.single_le_sum (fun a _ => mul_nonneg (hA.nonneg i a) (hB.nonneg a j))
      (Finset.mem_univ k))

private lemma lowerFactor_diag (c : ℝ) {n : ℕ} (i : Fin n) :
    lowerFactor c n i i = 1 := by
  simp [lowerFactor]

private lemma lowerFactor_sub (c : ℝ) {n : ℕ} (i : Fin n) :
    lowerFactor c (n + 1) i.succ i.castSucc = c * (i + 1) := by
  simp [lowerFactor, lowerBidiagonalFin_apply, Fin.ext_iff]

private lemma production_super (n : ℕ) (i : Fin n) :
    0 < production (n + 1) i.castSucc i.succ := by
  have h₀ := lowerFactor_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (n + 1)
  have h₁ := lowerFactor_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) (n + 1)
  apply mul_entry_pos (h₀.mul h₁) (upperSum_nonneg _) _ _ i.castSucc
  · exact mul_entry_pos h₀ h₁ _ _ i.castSucc
      (by rw [lowerFactor_diag]; norm_num) (by rw [lowerFactor_diag]; norm_num)
  · simp [upperSum, Fin.le_def]

private lemma production_sub (n : ℕ) (i : Fin n) :
    0 < production (n + 1) i.succ i.castSucc := by
  have h₀ := lowerFactor_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (n + 1)
  have h₁ := lowerFactor_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) (n + 1)
  apply mul_entry_pos (h₀.mul h₁) (upperSum_nonneg _) _ _ i.castSucc
  · exact mul_entry_pos h₀ h₁ _ _ i.castSucc
      (by rw [lowerFactor_sub]; positivity) (by rw [lowerFactor_diag]; norm_num)
  · simp [upperSum]

/-- Consecutive characteristic polynomials strictly interlace: both have simple
roots, they have no common root, and the larger section has positive roots.
The separate multiplicity and disjointness conclusions make the inequalities strict. -/
theorem production_charpoly_strictInterlaces (n : ℕ) :
    Interlaces (production n).charpoly (production (n + 1)).charpoly ∧
      (∀ x : ℝ, (production (n + 1)).charpoly.IsRoot x →
        (production (n + 1)).charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, (production n).charpoly.IsRoot x →
        (production n).charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, ¬ ((production (n + 1)).charpoly.IsRoot x ∧
        (production n).charpoly.IsRoot x)) ∧
      ∀ x ∈ (production (n + 1)).charpoly.roots, 0 < x := by
  have h := (production_isTotallyNonneg (n + 1)).leading_charpoly_strictInterlaces
    (by simp) (production_super n) (production_sub n)
  simpa only [production_leading] using h

/-- The normalized determinant pencil for the reversed, rescaled row `Gₙ`.
Its identification with graph packing counts is a separate counting identity. -/
def row (n : ℕ) : ℝ[X] :=
  Matrix.det (1 + (X : ℝ[X]) • (production n).map C)

private lemma reflectedReciprocal_eq (p : ℝ[X]) :
    RealRooted.reflectedReciprocal p = p.reverse.comp (-X) := by
  have hdeg : (p.comp (-X)).natDegree = p.natDegree := by
    simp [Polynomial.natDegree_comp]
  unfold RealRooted.reflectedReciprocal Polynomial.reverse
  rw [hdeg, Polynomial.reflect_comp_neg_X_of_natDegree_le le_rfl]
  rw [← mul_assoc, ← map_mul]
  have hsign : (-1 : ℝ) ^ p.natDegree * (-1) ^ p.natDegree = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hsign, map_one, one_mul]

/-- The determinant pencil is the reflected reciprocal of the characteristic polynomial. -/
theorem row_eq_reflectedReciprocal (n : ℕ) :
    row n = RealRooted.reflectedReciprocal (production n).charpoly := by
  rw [row, reflectedReciprocal_eq,
    Matrix.det_one_add_X_smul_eq_reverse_charpoly_comp_neg_X]

private lemma production_roots_pos (n : ℕ) :
    ∀ x ∈ (production n).charpoly.roots, 0 < x := by
  intro x hx
  exact (production_isTotallyNonneg n).pos_of_isRoot_charpoly_of_det_ne_zero
    (by simp) ((Polynomial.mem_roots (production n).charpoly_monic.ne_zero).mp hx)

/-- The determinant rows strictly interlace, have only simple negative roots, and
have no common root. This includes all dimensions, rather than a finite check. -/
theorem row_strictInterlaces (n : ℕ) :
    StrictInterl (row n) (row (n + 1)) ∧
      HasSimpleRoots (row n) ∧ HasSimpleRoots (row (n + 1)) ∧
      (∀ x : ℝ, ¬ ((row n).IsRoot x ∧ (row (n + 1)).IsRoot x)) ∧
      (∀ x ∈ (row n).roots, x < 0) ∧
      ∀ x ∈ (row (n + 1)).roots, x < 0 := by
  obtain ⟨hi, _, _, hno, _⟩ := production_charpoly_strictInterlaces n
  have h := hi.reflectedReciprocal_strict (production_roots_pos n)
    (production_roots_pos (n + 1)) (fun x hx => hno x hx.symm)
  simpa only [← row_eq_reflectedReciprocal] using h

/-- The determinant row is a nonzero real-rooted polynomial of degree exactly `n`. -/
theorem row_natDegree (n : ℕ) : (row n).natDegree = n := by
  have hs := (row_strictInterlaces n).1.1.2
  rw [← Polynomial.splits_iff_card_roots.mp hs, row_eq_reflectedReciprocal,
    RealRooted.reflectedReciprocal_roots (production n).charpoly_monic.ne_zero
      (production_isTotallyNonneg n).charpoly_splits (production_roots_pos n),
    Multiset.card_map,
    Polynomial.splits_iff_card_roots.mp (production_isTotallyNonneg n).charpoly_splits]
  simp

/-- Consecutive determinant rows have degree gap one and strictly alternating negative zeros. -/
theorem row_interlaces (n : ℕ) : Interlaces (row n) (row (n + 1)) := by
  exact (row_strictInterlaces n).1.toInterlaces (by rw [row_natDegree, row_natDegree])

/-- The determinant row has nonnegative coefficients and splits over the reals. -/
theorem row_isPFPolynomial (n : ℕ) : IsPFPolynomial (row n) :=
  (production_isTotallyNonneg n).isPFPolynomial_det_one_add_X_smul

private def upperShift (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  upperBidiagonalFin n (fun _ => 0) (fun _ => 1)

private lemma upperShift_mul_upperSum (n : ℕ) :
    upperShift n * upperSum n = fun i j => if i < j then 1 else 0 := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : i < j
  · let k : Fin n := ⟨i.val + 1, by have := j.isLt; have := Fin.lt_def.mp hij; lia⟩
    rw [Finset.sum_eq_single k]
    · have hik : i ≠ k := by apply Fin.ne_of_val_ne; dsimp [k]; lia
      have hkj : k ≤ j := by
        apply Fin.le_def.mpr
        dsimp [k]
        have := Fin.lt_def.mp hij
        lia
      simp [upperShift, upperBidiagonalFin_apply, upperSum, hik, k, hkj, hij]
    · intro a _ ha
      have hia : a.val ≠ i.val + 1 := fun h => ha (Fin.ext h)
      simp [upperShift, upperBidiagonalFin_apply, hia]
    · simp
  · rw [ite_eq_right hij]
    apply Finset.sum_eq_zero
    intro k _
    have hkj : i.val + 1 = k.val → ¬ k ≤ j := by
      intro hk hle
      apply hij
      exact Fin.lt_def.mpr (by have := Fin.le_def.mp hle; lia)
    by_cases hk : k.val = i.val + 1
    · simp [upperShift, upperBidiagonalFin_apply, upperSum, hkj hk.symm]
    · simp [upperShift, upperBidiagonalFin_apply, hk]

private lemma upperSum_right_inverse (n : ℕ) :
    (1 - upperShift n) * upperSum n = 1 := by
  rw [sub_mul, one_mul, upperShift_mul_upperSum]
  ext i j
  change (if i ≤ j then (1 : ℝ) else 0) - (if i < j then 1 else 0) =
    if i = j then 1 else 0
  by_cases h : i = j
  · subst j
    simp
  · by_cases hij : i < j
    · simp [h, hij, le_of_lt hij]
    · have hji : ¬ i ≤ j := fun hi => h (le_antisymm hi (le_of_not_gt hij))
      simp [h, hij, hji]

private lemma lowerProduct_eq (n : ℕ) :
    lowerFactor (1 / 2) n * lowerFactor (3 / 2) n =
      threeBidiagonalProduction (fun _ => (1 : ℝ)) (fun j => 1 / 2 * (j + 1))
        (fun _ => 1) (fun j => 3 / 2 * (j + 1)) (fun _ => 1) (fun _ => 0) n := by
  have hunit : upperBidiagonalFin n (fun _ => (1 : ℝ)) (fun _ => 0) = 1 := by
    ext i j
    simp [upperBidiagonalFin_apply, Matrix.one_apply]
  simp [threeBidiagonalProduction, lowerFactor, hunit]

private lemma lowerProduct_apply (n : ℕ) (i j : Fin n) :
    (lowerFactor (1 / 2) n * lowerFactor (3 / 2) n) i j =
      if i.val = j.val then 1
      else if i.val = j.val + 1 then 2 * (i.val : ℝ)
      else if i.val = j.val + 2 then 3 / 4 * (i.val : ℝ) * (i.val - 1)
      else 0 := by
  rw [lowerProduct_eq, threeBidiagonalProduction_apply]
  have hd (k : ℕ) :
      threeBidiagonalDiag (fun _ => (1 : ℝ)) (fun j => 1 / 2 * (j + 1))
        (fun _ => 1) (fun j => 3 / 2 * (j + 1)) (fun _ => 1) (fun _ => 0) k = 1 := by
    cases k <;> simp [threeBidiagonalDiag]
  have hs (k : ℕ) :
      threeBidiagonalSub (fun _ => (1 : ℝ)) (fun j => 1 / 2 * (j + 1))
        (fun _ => 1) (fun j => 3 / 2 * (j + 1)) (fun _ => 1) (fun _ => 0) k =
      2 * (k + 1) := by
    cases k <;> simp [threeBidiagonalSub] <;> ring
  rw [hd, hs]
  by_cases hdiag : i.val = j.val
  · rw [ite_eq_left hdiag, ite_eq_left hdiag]
  · rw [ite_eq_right hdiag, ite_eq_right hdiag]
    by_cases hsuper : j.val = i.val + 1
    · rw [ite_eq_left hsuper,
        ite_eq_right (by lia : i.val ≠ j.val + 1),
        ite_eq_right (by lia : i.val ≠ j.val + 2)]
      ring
    · rw [ite_eq_right hsuper]
      by_cases hsub : i.val = j.val + 1
      · rw [ite_eq_left hsub, ite_eq_left hsub, hsub]
        push_cast
        ring
      · rw [ite_eq_right hsub, ite_eq_right hsub]
        by_cases hsubtwo : i.val = j.val + 2
        · rw [ite_eq_left hsubtwo, ite_eq_left hsubtwo, hsubtwo]
          push_cast
          ring
        · rw [ite_eq_right hsubtwo, ite_eq_right hsubtwo]

private def pencil (n : ℕ) : Matrix (Fin n) (Fin n) ℝ[X] :=
  (1 - upperShift n).map C +
    (X : ℝ[X]) • (lowerFactor (1 / 2) n * lowerFactor (3 / 2) n).map C

private lemma det_pencil (n : ℕ) : (pencil n).det = row n := by
  have hmul : pencil n * (upperSum n).map C =
      1 + (X : ℝ[X]) • (production n).map C := by
    rw [pencil, Matrix.add_mul, Matrix.smul_mul, ← Matrix.map_mul,
      upperSum_right_inverse]
    simp only [← Matrix.map_mul, production]
    simp [Matrix.map_one, map_zero, map_one]
  have hdet := congrArg Matrix.det hmul
  have hu : ((upperSum n).map C).det = (1 : ℝ[X]) := by
    calc
      _ = C (upperSum n).det := (C.map_det (upperSum n)).symm
      _ = 1 := by rw [upperSum_det, map_one]
  rw [Matrix.det_mul, hu, mul_one] at hdet
  exact hdet

private lemma pencil_eq_banded (n : ℕ) :
    pencil n = Matrix.bandedLowerHessenberg (fun _ => (1 : ℝ[X]) + X)
      (fun i => C (2 * (i : ℝ)) * X)
      (fun i => C (3 / 4 * (i : ℝ) * (i - 1)) * X) (-1) n := by
  ext i j
  simp only [pencil, Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, lowerProduct_apply,
    upperShift, upperBidiagonalFin_apply, Matrix.bandedLowerHessenberg_apply,
    Fin.ext_iff]
  split_ifs <;> norm_num <;> first | ac_rfl | (exfalso; lia)

/-- Last-row expansion gives exactly the three-lag recurrence in issue #2647. -/
theorem row_add_three (n : ℕ) :
    row (n + 3) = (1 + X) * row (n + 2) +
      C (2 * (n + 2 : ℝ)) * X * row (n + 1) +
      C (3 / 4 * (n + 2 : ℝ) * (n + 1)) * X * row n := by
  simp_rw [← det_pencil, pencil_eq_banded]
  rw [Matrix.det_bandedLowerHessenberg_add_three]
  push_cast
  simp only [map_mul, map_add, map_sub, map_natCast, map_ofNat, map_one]
  ring

/-- The empty determinant row is one. -/
@[simp] theorem row_zero : row 0 = 1 := by
  simp [row]

/-- The first determinant row is `1 + X`. -/
@[simp] theorem row_one : row 1 = 1 + X := by
  rw [← det_pencil, pencil_eq_banded, Matrix.det_fin_one]
  simp

/-- The second determinant row is `1 + 4X + X²`. -/
@[simp] theorem row_two : row 2 = 1 + C 4 * X + X ^ 2 := by
  rw [← det_pencil, pencil_eq_banded, Matrix.det_fin_two]
  norm_num [Matrix.bandedLowerHessenberg_apply, Polynomial.C_ofNat]
  ring

/-- The three initial values and the recurrence uniquely specify the determinant rows. -/
theorem eq_row {F : ℕ → ℝ[X]} (h₀ : F 0 = 1) (h₁ : F 1 = 1 + X)
    (h₂ : F 2 = 1 + C 4 * X + X ^ 2)
    (hrec : ∀ n, F (n + 3) = (1 + X) * F (n + 2) +
      C (2 * (n + 2 : ℝ)) * X * F (n + 1) +
      C (3 / 4 * (n + 2 : ℝ) * (n + 1)) * X * F n) (n : ℕ) : F n = row n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => simpa using h₀
    | 1 => simpa using h₁
    | 2 => simpa using h₂
    | n + 3 => rw [hrec, row_add_three, ih (n + 2) (by lia),
        ih (n + 1) (by lia), ih n (by lia)]

/-- The constant term of each determinant row is one. -/
@[simp] theorem row_coeff_zero (n : ℕ) : (row n).coeff 0 = 1 := by
  rw [row, Polynomial.coeff_zero_eq_eval_zero, eval_det_add_X_smul]
  simp

/-- Factorial compression of the reversed, rescaled row. Its reversal, times `n!`,
is the ordinary row once the graph counting identity is established. -/
def compressedRow (n : ℕ) : ℝ[X] :=
  diagonalOperator (fun k => (k.factorial : ℝ)⁻¹) (row n)

private lemma invFactorial_pos (k : ℕ) : 0 < (k.factorial : ℝ)⁻¹ := by
  positivity

private lemma compressedRow_isPFPolynomial (n : ℕ) : IsPFPolynomial (compressedRow n) :=
  isPFMultiplierSequence_inv_factorial.diagonalOperator_isPF (row_isPFPolynomial n)

/-- Factorial compression preserves exact degree. -/
theorem compressedRow_natDegree (n : ℕ) : (compressedRow n).natDegree = n := by
  apply le_antisymm ((natDegree_diagonalOperator_le _ _).trans (row_natDegree n).le)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [coeff_diagonalOperator]
  have htop : (row n).coeff n ≠ 0 := by
    simpa only [Polynomial.leadingCoeff, row_natDegree] using
      (Polynomial.leadingCoeff_ne_zero.mpr (row_strictInterlaces n).1.1.1)
  exact mul_ne_zero (invFactorial_pos n).ne' htop

/-- The factorial-compressed rows still have constant coefficient one. -/
@[simp] theorem compressedRow_coeff_zero (n : ℕ) : (compressedRow n).coeff 0 = 1 := by
  simp [compressedRow, coeff_diagonalOperator]

/-- Factorial compression preserves strict separation of consecutive rows,
including absence of common roots. The finite Schur--Szegő theorem applies to
the reciprocal-factorial Jensen polynomial. -/
theorem compressedRow_strictInterlaces (n : ℕ) :
    StrictInterl (compressedRow n) (compressedRow (n + 1)) ∧
      ∀ x : ℝ, ¬ ((compressedRow n).IsRoot x ∧ (compressedRow (n + 1)).IsRoot x) := by
  let γ : ℕ → ℝ := fun k => (k.factorial : ℝ)⁻¹
  let Q := jensenPolynomial (n + 1) γ
  have hQpf : IsPFPolynomial Q :=
    isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence
      isPFMultiplierSequence_inv_factorial (n + 1)
  have hQzero : Q.coeff 0 ≠ 0 := by simp [Q, coeff_jensenPolynomial, γ]
  have hQne : Q ≠ 0 := fun h => hQzero (by simp [h])
  have hQdeg : Q.natDegree = n + 1 := by
    apply le_antisymm (natDegree_jensenPolynomial_le _ _)
    apply Polynomial.le_natDegree_of_ne_zero
    simpa [Q, coeff_jensenPolynomial, γ] using (invFactorial_pos (n + 1)).ne'
  have hQpos : HasPosLeadingCoeff Q := hQpf.hasNonnegCoeffs.pos_leadingCoeff hQne
  have hQneg : ∀ x ∈ Q.roots, x < 0 :=
    roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hQpf.hasNonnegCoeffs hQzero
  have hrow := row_strictInterlaces n
  have h := strictInterl_schurSzegoComp_of_roots_neg (by lia : n + 1 ≠ 0)
    (by rw [row_natDegree]; lia : (row n).natDegree ≤ n + 1)
    (by rw [row_natDegree] : (row (n + 1)).natDegree ≤ n + 1)
    ((row_isPFPolynomial n).hasNonnegCoeffs.pos_leadingCoeff hrow.1.1.1)
    ((row_isPFPolynomial (n + 1)).hasNonnegCoeffs.pos_leadingCoeff hrow.1.2.1.1)
    hrow.1 (fun r hr hgr => hrow.2.2.2.1 r ⟨hr, hgr⟩)
    hQdeg hQpf.splits hQpos hQneg
  have hid (k : ℕ) (hk : k ≤ n + 1) :
      schurSzegoComp (n + 1) (row k) Q = compressedRow k := by
    rw [schurSzegoComp_comm]
    exact schurSzegoComp_jensenPolynomial_eq_diagonalOperator_of_natDegree_le
      (by rwa [row_natDegree])
  rw [hid n (by lia), hid (n + 1) le_rfl] at h
  exact ⟨h.1, fun x hx => h.2 x hx.1 hx.2⟩

/-- Every factorial-compressed row has simple negative zeros. -/
theorem compressedRow_roots (n : ℕ) :
    HasSimpleRoots (compressedRow n) ∧ ∀ x ∈ (compressedRow n).roots, x < 0 := by
  have h := compressedRow_strictInterlaces n
  exact ⟨(h.1.hasSimpleRoots_of_no_common_root h.2).1,
    roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne
      (compressedRow_isPFPolynomial n).hasNonnegCoeffs (by simp)⟩

private lemma reverse_pair {f g : ℝ[X]} (hfg : Interlaces f g)
    (hf0 : f.coeff 0 ≠ 0) (hg0 : g.coeff 0 ≠ 0)
    (hfneg : ∀ x ∈ f.roots, x < 0) (hgneg : ∀ x ∈ g.roots, x < 0)
    (hno : ∀ x, ¬ (f.IsRoot x ∧ g.IsRoot x)) :
    Interlaces f.reverse g.reverse ∧
      HasSimpleRoots f.reverse ∧ HasSimpleRoots g.reverse ∧
      (∀ x, ¬ (f.reverse.IsRoot x ∧ g.reverse.IsRoot x)) ∧
      (∀ x ∈ f.reverse.roots, x < 0) ∧ ∀ x ∈ g.reverse.roots, x < 0 := by
  have hi := interlaces_reverse_of_roots_neg hfg hgneg hfneg
  have hn : ∀ x, ¬ (f.reverse.IsRoot x ∧ g.reverse.IsRoot x) := by
    intro x hx
    have hxf := (Polynomial.mem_roots hi.2.1.1).mpr hx.1
    have hxg := (Polynomial.mem_roots hi.1.1).mpr hx.2
    rw [Polynomial.roots_reverse_eq_map_inv hfg.2.1.2 hf0, Multiset.mem_map] at hxf
    rw [Polynomial.roots_reverse_eq_map_inv hfg.1.2 hg0, Multiset.mem_map] at hxg
    obtain ⟨a, ha, hax⟩ := hxf
    obtain ⟨b, hb, hbx⟩ := hxg
    have hab : a = b := inv_injective (hax.trans hbx.symm)
    exact hno a ⟨Polynomial.isRoot_of_mem_roots ha,
      hab.symm ▸ Polynomial.isRoot_of_mem_roots hb⟩
  have hs := hi.toStrictInterl.hasSimpleRoots_of_no_common_root hn
  refine ⟨hi, hs.1, hs.2, hn, ?_, ?_⟩
  · intro x hx
    rw [Polynomial.roots_reverse_eq_map_inv hfg.2.1.2 hf0, Multiset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact inv_lt_zero.mpr (hfneg a ha)
  · intro x hx
    rw [Polynomial.roots_reverse_eq_map_inv hfg.1.2 hg0, Multiset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact inv_lt_zero.mpr (hgneg a ha)

/-- The candidate coefficient-rescaled clustering polynomial, obtained by reversing `Gₙ`.
The graph counting identity is required to identify these coefficients with packings. -/
def rescaledPolynomial (n : ℕ) : ℝ[X] := (row n).reverse

/-- The ordinary candidate clustering row: reverse the factorial compression and multiply by `n!`.
This definition does not assert a graph enumeration identity. -/
def polynomial (n : ℕ) : ℝ[X] :=
  C (n.factorial : ℝ) * (compressedRow n).reverse

/-- Reversal of the determinant rows has exact degree `n`. -/
theorem rescaledPolynomial_natDegree (n : ℕ) : (rescaledPolynomial n).natDegree = n := by
  rw [rescaledPolynomial, Polynomial.reverse_natDegree,
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by simp)), Nat.sub_zero, row_natDegree]

/-- The coefficient-rescaled candidates strictly interlace, with simple negative zeros. -/
theorem rescaledPolynomial_roots (n : ℕ) :
    Interlaces (rescaledPolynomial n) (rescaledPolynomial (n + 1)) ∧
      HasSimpleRoots (rescaledPolynomial n) ∧ HasSimpleRoots (rescaledPolynomial (n + 1)) ∧
      (∀ x, ¬ ((rescaledPolynomial n).IsRoot x ∧
        (rescaledPolynomial (n + 1)).IsRoot x)) ∧
      (∀ x ∈ (rescaledPolynomial n).roots, x < 0) ∧
      ∀ x ∈ (rescaledPolynomial (n + 1)).roots, x < 0 := by
  have h := row_strictInterlaces n
  exact reverse_pair (row_interlaces n) (by simp) (by simp) h.2.2.2.2.1 h.2.2.2.2.2
    h.2.2.2.1

/-- The ordinary candidates have exact degree `n`. -/
theorem polynomial_natDegree (n : ℕ) : (polynomial n).natDegree = n := by
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [polynomial, Polynomial.natDegree_C_mul hfac, Polynomial.reverse_natDegree,
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by simp)), Nat.sub_zero,
    compressedRow_natDegree]

/-- The ordinary candidates strictly interlace, with simple negative zeros.
No graph-counting hypothesis is hidden in this algebraic statement. -/
theorem polynomial_roots (n : ℕ) :
    Interlaces (polynomial n) (polynomial (n + 1)) ∧
      HasSimpleRoots (polynomial n) ∧ HasSimpleRoots (polynomial (n + 1)) ∧
      (∀ x, ¬ ((polynomial n).IsRoot x ∧ (polynomial (n + 1)).IsRoot x)) ∧
      (∀ x ∈ (polynomial n).roots, x < 0) ∧
      ∀ x ∈ (polynomial (n + 1)).roots, x < 0 := by
  have hc := compressedRow_strictInterlaces n
  have hci := hc.1.toInterlaces (by rw [compressedRow_natDegree, compressedRow_natDegree])
  have hr := reverse_pair hci (by simp) (by simp)
    (compressedRow_roots n).2 (compressedRow_roots (n + 1)).2 hc.2
  have hfac (k : ℕ) : (k.factorial : ℝ) ≠ 0 := by positivity
  have hi : StrictInterl (polynomial n) (polynomial (n + 1)) :=
    (hr.1.toStrictInterl.C_mul_left (hfac n)).C_mul_right (hfac (n + 1))
  refine ⟨hi.toInterlaces (by rw [polynomial_natDegree, polynomial_natDegree]),
    hr.2.1.C_mul (hfac n), hr.2.2.1.C_mul (hfac (n + 1)), ?_, ?_, ?_⟩
  · intro x hx
    apply hr.2.2.2.1 x
    simpa [polynomial, Polynomial.IsRoot.def, hfac] using hx
  · intro x hx
    apply hr.2.2.2.2.1 x
    simpa only [polynomial, Polynomial.roots_C_mul _ (hfac n)] using hx
  · intro x hx
    apply hr.2.2.2.2.2 x
    simpa only [polynomial, Polynomial.roots_C_mul _ (hfac (n + 1))] using hx

/-- The two candidate families have exactly the falling-factorial coefficient relation
required by issue #2647, including coefficients beyond the degree. -/
theorem coeff_polynomial (n j : ℕ) :
    (polynomial n).coeff j = (n.descFactorial j : ℝ) * (rescaledPolynomial n).coeff j := by
  by_cases hj : j ≤ n
  · rw [polynomial, Polynomial.coeff_C_mul, Polynomial.coeff_reverse,
      compressedRow_natDegree, Polynomial.revAt_le hj, compressedRow,
      coeff_diagonalOperator, rescaledPolynomial, Polynomial.coeff_reverse,
      row_natDegree, Polynomial.revAt_le hj]
    have hfac : ((n - j).factorial : ℝ) ≠ 0 := by positivity
    have heq : ((n - j).factorial : ℝ) * (n.descFactorial j : ℝ) =
        (n.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hj
    rw [← heq]
    field_simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [polynomial_natDegree]; lia),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [rescaledPolynomial_natDegree]; lia),
      mul_zero]

/-- Dividing by the falling factorial recovers precisely the rescaled candidate row. -/
theorem coeff_rescaledPolynomial (n j : ℕ) :
    (rescaledPolynomial n).coeff j = (polynomial n).coeff j / (n.descFactorial j : ℝ) := by
  by_cases hj : j ≤ n
  · rw [coeff_polynomial]
    have hd : (n.descFactorial j : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hj).ne'
    field_simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [rescaledPolynomial_natDegree]; lia),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [polynomial_natDegree]; lia),
      zero_div]

/-- Block weights for `exp(z + u z (1 + z/2)²)`. -/
def blockWeights : ℕ → ℝ[X]
  | 1 => 1 + X
  | 2 => C 2 * X
  | 3 => C (3 / 2) * X
  | _ => 0

private lemma insertionRow_add_three (n : ℕ) :
    ExponentialRows.insertionRow blockWeights (n + 3) =
      (1 + X) * ExponentialRows.insertionRow blockWeights (n + 2) +
      C (2 * (n + 2 : ℝ)) * X * ExponentialRows.insertionRow blockWeights (n + 1) +
      C (3 / 4 * (n + 2 : ℝ) * (n + 1)) * X *
        ExponentialRows.insertionRow blockWeights n := by
  rw [show n + 3 = (n + 2) + 1 by lia, ExponentialRows.insertionRow_succ]
  rw [show n + 2 + 1 = 3 + n by lia, Finset.sum_range_add]
  have ht : ∑ k ∈ Finset.range n, C ((n + 2).choose (3 + k) : ℝ) *
      blockWeights (3 + k + 1) *
        ExponentialRows.insertionRow blockWeights (n + 2 - (3 + k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [show 3 + k + 1 = k + 4 by lia]
    simp [blockWeights]
  rw [ht, add_zero]
  have h2 : 2 * ((n + 2).choose 2 : ℝ) = (n + 2 : ℝ) * (n + 1) := by
    have hh := congrArg (fun k : ℕ => (k : ℝ))
      (Nat.descFactorial_eq_factorial_mul_choose (n + 2) 2)
    norm_num [Nat.descFactorial_succ] at hh
    nlinarith [hh]
  norm_num [Finset.sum_range_succ, blockWeights,
    show n + 2 - 1 = n + 1 by lia] at ⊢
  have hp2 := congrArg C h2
  simp only [map_mul, map_add, map_natCast, map_ofNat, map_one] at hp2
  have hscale : (C (3 / 2 : ℝ) : ℝ[X]) = C (3 / 4 : ℝ) * 2 := by
    change C (3 / 2 : ℝ) = C (3 / 4 : ℝ) * C (2 : ℝ)
    rw [← map_mul]
    norm_num
  simp only [Polynomial.C_ofNat] at hscale ⊢
  linear_combination
    (C (3 / 4) * X * ExponentialRows.insertionRow blockWeights n) * hp2 +
    (((n + 2).choose 2 : ℝ[X]) * X *
      ExponentialRows.insertionRow blockWeights n) * hscale

/-- The determinant rows are the standard block-weight insertion rows. -/
theorem row_eq_insertionRow (n : ℕ) :
    row n = ExponentialRows.insertionRow blockWeights n := by
  symm
  apply eq_row
  · simp
  · norm_num [ExponentialRows.insertionRow_succ, Finset.sum_range_succ, blockWeights]
  · norm_num [ExponentialRows.insertionRow_succ, Finset.sum_range_succ, blockWeights,
      Polynomial.C_ofNat]
    ring
  · exact insertionRow_add_three

/-- The determinant rows have the factorial-coefficient exponential generating function
with the three specified block weights. This is an identity of formal power series. -/
theorem row_eq_factorialCoeff (n : ℕ) :
    row n = ExponentialRows.factorialCoeff
      ((PowerSeries.exp ℝ[X]).subst (ExponentialRows.blockWeightSeries blockWeights)) n := by
  rw [row_eq_insertionRow, ExponentialRows.insertionRow_eq_factorialCoeff]
  rfl

/-- The marked block polynomial `z(1+z/2)²` in the exponential generating function. -/
def blockPolynomial : ℝ[X] := X + X ^ 2 + C (1 / 4) * X ^ 3

/-- The cubic marked block polynomial has a double zero at `-2`. -/
theorem blockPolynomial_eq : blockPolynomial = X * (1 + C (1 / 2) * X) ^ 2 := by
  symm
  calc
    X * (1 + C (1 / 2) * X) ^ 2 =
        X + C ((1 / 2 : ℝ) + 1 / 2) * X ^ 2 +
          C ((1 / 2 : ℝ) * (1 / 2)) * X ^ 3 := by
      rw [map_add, map_mul]
      ring
    _ = blockPolynomial := by norm_num [blockPolynomial]

private lemma blockWeights_eq_affine :
    blockWeights = ExponentialRows.affineBlockWeights PowerSeries.X
      (blockPolynomial : PowerSeries ℝ) := by
  funext r
  match r with
  | 0 =>
    norm_num [blockWeights, ExponentialRows.affineBlockWeights, blockPolynomial,
      PowerSeries.coeff_X]
  | 1 =>
    norm_num [blockWeights, ExponentialRows.affineBlockWeights, blockPolynomial,
      PowerSeries.coeff_X]
  | 2 =>
    norm_num [blockWeights, ExponentialRows.affineBlockWeights, blockPolynomial,
      PowerSeries.coeff_X]
  | 3 =>
    norm_num [blockWeights, ExponentialRows.affineBlockWeights, blockPolynomial,
      PowerSeries.coeff_X]
  | r + 4 =>
    simp [blockWeights, ExponentialRows.affineBlockWeights, blockPolynomial,
      PowerSeries.coeff_X, show r + 4 ≠ 2 by lia, show r + 4 ≠ 3 by lia]

/-- The exact formal generating function from issue #2647:
`Gₙ(u) = n! [zⁿ] exp(z + u z(1+z/2)²)`. -/
theorem row_eq_exponential (n : ℕ) :
    row n = ExponentialRows.factorialCoeff ((PowerSeries.exp ℝ[X]).subst
      (PowerSeries.X + PowerSeries.C X *
        (blockPolynomial : PowerSeries ℝ).map C)) n := by
  rw [row_eq_insertionRow, blockWeights_eq_affine,
    ExponentialRows.insertionRow_eq_factorialCoeff, ExponentialRows.insertionSeries,
    ExponentialRows.blockWeightSeries_affineBlockWeights (by simp)
      (by simp [blockPolynomial])]
  simp

end RealRooted.BipartiteClustering
