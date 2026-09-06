import RealRooted.BrandenLeite.Resolvable
import RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Core

/-!
# Whitney reduction for Brändén--Saud Leite resolutions

This file connects the finite Whitney elimination API to infinite lower
unitriangular matrices and constructs the resolution attached to a totally
nonnegative matrix.
-/

open Matrix Polynomial BigOperators

noncomputable section

namespace Matrix

theorem whitneyClearFirstAux_apply_of_le {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∀ t, t ≤ N → ∀ i j, i.val ≤ N - t →
      whitneyClearFirstAux A t i j = A i j := by
  intro t ht
  induction t with
  | zero =>
      intro i j hi
      rfl
  | succ t ih =>
      intro i j hi
      have htN : t < N := by lia
      let s : Fin N := ⟨N - (t + 1), by lia⟩
      let B := whitneyClearFirstAux A t
      rw [whitneyClearFirstAux, dif_pos htN]
      by_cases hzero : B s.succ 0 = 0
      · rw [if_pos hzero]
        exact ih htN.le i j (by lia)
      · rw [if_neg hzero]
        have his : i ≠ s.succ := by
          intro his
          have hval : i.val = N - t := by
            rw [his]
            simp [s]
            lia
          lia
        have his' : i ≠ (⟨N - (t + 1), by lia⟩ : Fin N).succ := by
          simpa only [s] using his
        simp only [whitneyEliminateFirst, whitneyEliminateAt,
          Matrix.updateRow_apply, his', if_false]
        exact ih htN.le i j (by lia)

theorem whitneyClearFirstAux_succ_apply_of_ne {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (t : ℕ) (ht : t < N) (i j : Fin (N + 1))
    (hi : i.val ≠ N - t) :
    whitneyClearFirstAux A (t + 1) i j =
      whitneyClearFirstAux A t i j := by
  let s : Fin N := ⟨N - (t + 1), by lia⟩
  rw [whitneyClearFirstAux, dif_pos ht]
  by_cases hzero : whitneyClearFirstAux A t s.succ 0 = 0
  · rw [if_pos hzero]
  · rw [if_neg hzero]
    have his : i ≠ s.succ := by
      intro his
      apply hi
      rw [his]
      simp [s]
      lia
    have his' : i ≠ (⟨N - (t + 1), by lia⟩ : Fin N).succ := by
      simpa only [s] using his
    simp only [whitneyEliminateFirst, whitneyEliminateAt,
      Matrix.updateRow_apply, his', if_false]

theorem whitneyClearFirstAux_apply_eq_final_of_lt {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (t : ℕ) (ht : t ≤ N) (i j : Fin (N + 1))
    (hi : N - t < i.val) :
    whitneyClearFirstAux A t i j = whitneyClearFirstAux A N i j := by
  have hstable : ∀ u, t ≤ u → u ≤ N →
      whitneyClearFirstAux A u i j = whitneyClearFirstAux A t i j := by
    intro u htu huN
    induction u, htu using Nat.le_induction with
    | base => rfl
    | succ u htu ih =>
        rw [whitneyClearFirstAux_succ_apply_of_ne A u (by lia) i j (by lia)]
        exact ih (by lia)
  exact (hstable N ht le_rfl).symm

/-- The completed bottom-up Whitney sweep has the expected adjacent-row
formula on its trailing block. -/
theorem whitneyClearFirstAux_apply_succ {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (i j : Fin N) :
    whitneyClearFirstAux A N i.succ j.succ =
      A i.succ j.succ -
        (A i.succ 0 / A i.castSucc 0) * A i.castSucc j.succ := by
  let t := N - (i.val + 1)
  have htN : t < N := by
    dsimp [t]
    lia
  have ht1N : t + 1 ≤ N := htN
  let s : Fin N := ⟨N - (t + 1), by lia⟩
  have hs : s = i := by
    apply Fin.ext
    dsimp [s, t]
    lia
  have htarget : whitneyClearFirstAux A t i.succ 0 = A i.succ 0 :=
    whitneyClearFirstAux_apply_of_le A t htN.le i.succ 0 (by
      dsimp [t]
      lia)
  have hpivot : whitneyClearFirstAux A t i.castSucc 0 = A i.castSucc 0 :=
    whitneyClearFirstAux_apply_of_le A t htN.le i.castSucc 0 (by
      dsimp [t]
      lia)
  have htargetj : whitneyClearFirstAux A t i.succ j.succ = A i.succ j.succ :=
    whitneyClearFirstAux_apply_of_le A t htN.le i.succ j.succ (by
      dsimp [t]
      lia)
  have hpivotj : whitneyClearFirstAux A t i.castSucc j.succ =
      A i.castSucc j.succ :=
    whitneyClearFirstAux_apply_of_le A t htN.le i.castSucc j.succ (by
      dsimp [t]
      lia)
  have hstage : whitneyClearFirstAux A (t + 1) i.succ j.succ =
      A i.succ j.succ -
        (A i.succ 0 / A i.castSucc 0) * A i.castSucc j.succ := by
    rw [whitneyClearFirstAux, dif_pos htN]
    by_cases hzero : whitneyClearFirstAux A t s.succ 0 = 0
    · rw [if_pos hzero]
      rw [hs] at hzero
      rw [htarget] at hzero
      rw [htargetj]
      simp [hzero]
    · rw [if_neg hzero]
      have hs' : (⟨N - (t + 1), by lia⟩ : Fin N) = i := by
        simpa only [s] using hs
      simp only [whitneyEliminateFirst, whitneyEliminateAt,
        Matrix.updateRow_apply, hs', if_pos]
      rw [htargetj, htarget, hpivot, hpivotj]
  have hstable := whitneyClearFirstAux_apply_eq_final_of_lt
    A (t + 1) ht1N i.succ j.succ (by
      dsimp [t]
      lia)
  exact hstable.symm.trans hstage

end Matrix

namespace RealRooted

namespace BrandenLeite

/-- The leading `N × N` section of an infinite lower-triangular matrix. -/
def principalSection (R : LowerTriangularMatrix ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j ↦ R i j

/-- The multiplier removed from rows `n + 1` and `n` by one Whitney sweep. -/
def firstColumnRatio (R : LowerTriangularMatrix ℝ) (n : ℕ) : ℝ :=
  R (n + 1) 0 / R n 0

/-- Remove the first column of a lower-triangular matrix by Whitney elimination. -/
def whitneyReduce (R : LowerTriangularMatrix ℝ) : LowerTriangularMatrix ℝ :=
  fun n k ↦
    R (n + 1) (k + 1) - firstColumnRatio R n * R n (k + 1)

/-- Iterated Whitney reduction. -/
def whitneyIterate (R : LowerTriangularMatrix ℝ) :
    ℕ → LowerTriangularMatrix ℝ
  | 0 => R
  | k + 1 => whitneyReduce (whitneyIterate R k)

theorem whitneyClearFirst_trailing_eq_principalSection_whitneyReduce
    (R : LowerTriangularMatrix ℝ) (N : ℕ) :
    (Matrix.whitneyClearFirstAux (principalSection R (N + 1)) N).submatrix
        Fin.succ Fin.succ =
      principalSection (whitneyReduce R) N := by
  ext i j
  simpa [principalSection, whitneyReduce, firstColumnRatio] using
    Matrix.whitneyClearFirstAux_apply_succ
      (principalSection R (N + 1)) i j

@[simp] theorem whitneyIterate_zero (R : LowerTriangularMatrix ℝ) :
    whitneyIterate R 0 = R :=
  rfl

@[simp] theorem whitneyIterate_succ (R : LowerTriangularMatrix ℝ) (k : ℕ) :
    whitneyIterate R (k + 1) = whitneyReduce (whitneyIterate R k) :=
  rfl

theorem principalSection_isTotallyNonneg
    {R : LowerTriangularMatrix ℝ} (hR : Matrix.IsTotallyNonneg R) (N : ℕ) :
    Matrix.IsTotallyNonneg (principalSection R N) := by
  exact hR.submatrix Fin.val_strictMono Fin.val_strictMono

theorem isTotallyNonneg_of_principalSections (M : Matrix ℕ ℕ ℝ)
    (hM : ∀ N, Matrix.IsTotallyNonneg
      (M.submatrix (fun i : Fin (N + 1) ↦ i.val)
        (fun i : Fin (N + 1) ↦ i.val))) :
    Matrix.IsTotallyNonneg M := by
  intro n rows cols hrows hcols
  cases n with
  | zero => simp
  | succ n =>
      let B := max (rows (Fin.last n)) (cols (Fin.last n))
      let rows' : Fin (n + 1) → Fin (B + 1) := fun i ↦
        ⟨rows i, Nat.lt_succ_of_le <|
          le_trans (hrows.monotone (Fin.le_last i)) (le_max_left _ _)⟩
      let cols' : Fin (n + 1) → Fin (B + 1) := fun i ↦
        ⟨cols i, Nat.lt_succ_of_le <|
          le_trans (hcols.monotone (Fin.le_last i)) (le_max_right _ _)⟩
      have hrows' : StrictMono rows' := by
        intro i j hij
        exact Fin.lt_def.mpr (hrows hij)
      have hcols' : StrictMono cols' := by
        intro i j hij
        exact Fin.lt_def.mpr (hcols hij)
      have hminor : M.submatrix rows cols =
          (M.submatrix (fun i : Fin (B + 1) ↦ i.val)
            (fun i : Fin (B + 1) ↦ i.val)).submatrix rows' cols' := by
        rfl
      rw [hminor]
      exact hM B hrows' hcols'

theorem det_principalSection_eq_one
    {R : LowerTriangularMatrix ℝ}
    (hR : LowerTriangularMatrix.IsLowerUnitriangular R) (N : ℕ) :
    (principalSection R N).det = 1 := by
  have hlower : (principalSection R N).BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact hR.lower hij
  rw [Matrix.det_of_lowerTriangular _ hlower]
  simp [principalSection, hR.diagonal]

theorem whitneyReduce_isTotallyNonneg
    {R : LowerTriangularMatrix ℝ}
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) :
    Matrix.IsTotallyNonneg (whitneyReduce R) := by
  apply isTotallyNonneg_of_principalSections
  intro N
  change Matrix.IsTotallyNonneg (principalSection (whitneyReduce R) (N + 1))
  have hsection : Matrix.IsTotallyNonneg (principalSection R (N + 2)) :=
    principalSection_isTotallyNonneg hR (N + 2)
  have hdet : (principalSection R (N + 2)).det ≠ 0 := by
    rw [det_principalSection_eq_one hunit]
    exact one_ne_zero
  have htrailing :=
    (Matrix.whitneyClearFirst_trailing
      (principalSection R (N + 2)) hsection hdet).1
  rw [whitneyClearFirst_trailing_eq_principalSection_whitneyReduce] at htrailing
  exact htrailing

theorem whitneyReduce_isLowerUnitriangular
    {R : LowerTriangularMatrix ℝ}
    (hR : LowerTriangularMatrix.IsLowerUnitriangular R) :
    LowerTriangularMatrix.IsLowerUnitriangular (whitneyReduce R) := by
  constructor
  · intro n k hnk
    simp only [whitneyReduce]
    rw [hR.lower (by lia), hR.lower (by lia)]
    ring
  · intro n
    have hzero : R n (n + 1) = 0 := hR.lower (Nat.lt_succ_self n)
    simp only [whitneyReduce]
    rw [hR.diagonal, hzero, mul_zero, sub_zero]

theorem firstColumnRatio_nonneg
    {R : LowerTriangularMatrix ℝ} (hR : Matrix.IsTotallyNonneg R) (n : ℕ) :
    0 ≤ firstColumnRatio R n := by
  exact div_nonneg (hR.nonneg (n + 1) 0) (hR.nonneg n 0)

/-- A zero in the first column of a lower unitriangular TN matrix propagates
one row downward. -/
theorem firstColumn_zero_succ
    {R : LowerTriangularMatrix ℝ}
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) {n : ℕ} (hn : R n 0 = 0) :
    R (n + 1) 0 = 0 := by
  have hnpos : 0 < n := by
    by_contra h
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    simp [hunit.diagonal] at hn
  let rows : Fin 2 → ℕ := ![n, n + 1]
  let cols : Fin 2 → ℕ := ![0, n]
  have hrows : StrictMono rows := by
    simp [rows, Fin.strictMono_iff_lt_succ]
  have hcols : StrictMono cols := by
    simpa [cols, Fin.strictMono_iff_lt_succ] using hnpos
  have hminor := hR hrows hcols
  have hentry := hR.nonneg (n + 1) 0
  simp [rows, cols, Matrix.det_fin_two, hn, hunit.diagonal] at hminor
  exact le_antisymm (by linarith) hentry

theorem firstColumnRatio_mul
    {R : LowerTriangularMatrix ℝ}
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) (n : ℕ) :
    firstColumnRatio R n * R n 0 = R (n + 1) 0 := by
  by_cases hn : R n 0 = 0
  · rw [hn, mul_zero, firstColumn_zero_succ hunit hR hn]
  · simp [firstColumnRatio, hn]

theorem coeff_rowPolynomial
    {R : LowerTriangularMatrix ℝ} (hR : LowerTriangularMatrix.IsLowerTriangular R)
    (n k : ℕ) :
    (LowerTriangularMatrix.rowPolynomial R n).coeff k = R n k := by
  by_cases hkn : k ≤ n
  · exact LowerTriangularMatrix.coeff_rowPolynomial_of_le R hkn
  · have hnk : n < k := Nat.lt_of_not_ge hkn
    rw [LowerTriangularMatrix.coeff_rowPolynomial_of_gt R hnk,
      hR hnk]

theorem rowPolynomial_monic
    {R : LowerTriangularMatrix ℝ}
    (hR : LowerTriangularMatrix.IsLowerUnitriangular R) (n : ℕ) :
    (LowerTriangularMatrix.rowPolynomial R n).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
  · exact LowerTriangularMatrix.natDegree_rowPolynomial_le R n
  · rw [LowerTriangularMatrix.coeff_rowPolynomial_of_le R le_rfl,
      hR.diagonal]

/-- One Whitney reduction is exactly the row-polynomial recurrence used in a
Brändén--Saud Leite resolution. -/
theorem rowPolynomial_whitney_recurrence
    {R : LowerTriangularMatrix ℝ}
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) (n : ℕ) :
    LowerTriangularMatrix.rowPolynomial R (n + 1) =
      X * LowerTriangularMatrix.rowPolynomial (whitneyReduce R) n +
        C (firstColumnRatio R n) *
          LowerTriangularMatrix.rowPolynomial R n := by
  ext k
  rcases k with _ | k
  · simp [coeff_rowPolynomial hunit.lower, firstColumnRatio_mul hunit hR]
  · by_cases hkn : k ≤ n
    · rw [coeff_add, coeff_X_mul, coeff_C_mul,
        coeff_rowPolynomial (whitneyReduce_isLowerUnitriangular hunit).lower,
        coeff_rowPolynomial hunit.lower, coeff_rowPolynomial hunit.lower]
      simp only [whitneyReduce]
      ring
    · have hnk : n < k := Nat.lt_of_not_ge hkn
      rw [LowerTriangularMatrix.coeff_rowPolynomial_of_gt R (by lia),
        coeff_add, coeff_X_mul,
        LowerTriangularMatrix.coeff_rowPolynomial_of_gt (whitneyReduce R) hnk,
        coeff_C_mul,
        LowerTriangularMatrix.coeff_rowPolynomial_of_gt R (by lia)]
      ring

theorem whitneyIterate_invariant
    {R : LowerTriangularMatrix ℝ}
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) (k : ℕ) :
    LowerTriangularMatrix.IsLowerUnitriangular (whitneyIterate R k) ∧
      Matrix.IsTotallyNonneg (whitneyIterate R k) := by
  induction k with
  | zero => exact ⟨hunit, hR⟩
  | succ k ih =>
      rw [whitneyIterate_succ]
      exact ⟨whitneyReduce_isLowerUnitriangular ih.1,
        whitneyReduce_isTotallyNonneg ih.1 ih.2⟩

/-- The canonical Whitney multiplier at position `(n,k)`. -/
def resolutionLambda (R : LowerTriangularMatrix ℝ) (n k : ℕ) : ℝ :=
  firstColumnRatio (whitneyIterate R k) (n - k)

/-- The canonical resolving polynomial obtained after `k` Whitney reductions. -/
def resolutionPolynomial (R : LowerTriangularMatrix ℝ) (n k : ℕ) : ℝ[X] :=
  X ^ k * LowerTriangularMatrix.rowPolynomial
    (whitneyIterate R k) (n - k)

theorem resolutionPolynomial_recurrence
    {R : LowerTriangularMatrix ℝ}
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) {n k : ℕ} (hk : k ≤ n) :
    resolutionPolynomial R (n + 1) k =
      resolutionPolynomial R (n + 1) (k + 1) +
        C (resolutionLambda R n k) * resolutionPolynomial R n k := by
  obtain ⟨hiterUnit, hiterTN⟩ := whitneyIterate_invariant hunit hR k
  have hrow := rowPolynomial_whitney_recurrence hiterUnit hiterTN (n - k)
  unfold resolutionPolynomial resolutionLambda
  rw [show n + 1 - k = (n - k) + 1 by lia,
    show n + 1 - (k + 1) = n - k by lia, whitneyIterate_succ, hrow]
  ring

/-- The canonical Brändén--Saud Leite resolution of a lower unitriangular TN
matrix. -/
def resolutionOfTotallyNonneg
    (R : LowerTriangularMatrix ℝ)
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) : Resolution R where
  lowerUnitriangular := hunit
  lambda := resolutionLambda R
  polynomial := resolutionPolynomial R
  lambda_nonneg := by
    intro n k hk
    exact firstColumnRatio_nonneg
      (whitneyIterate_invariant hunit hR k).2 (n - k)
  monic := by
    intro n k hk
    exact (Polynomial.monic_X_pow k).mul <|
      rowPolynomial_monic (whitneyIterate_invariant hunit hR k).1 (n - k)
  row_zero := by
    intro n
    simp [resolutionPolynomial]
  diagonal := by
    intro n
    have hdiag := (whitneyIterate_invariant hunit hR n).1.diagonal 0
    simp [resolutionPolynomial, LowerTriangularMatrix.rowPolynomial, hdiag]
  dvd_X_pow := by
    intro n k hk
    exact ⟨LowerTriangularMatrix.rowPolynomial
      (whitneyIterate R k) (n - k), rfl⟩
  recurrence := by
    intro n k hk
    exact resolutionPolynomial_recurrence hunit hR hk

theorem isResolvable_of_isTotallyNonneg
    {R : LowerTriangularMatrix ℝ}
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R)
    (hR : Matrix.IsTotallyNonneg R) : IsResolvable R :=
  ⟨resolutionOfTotallyNonneg R hunit hR⟩

end BrandenLeite

end RealRooted
