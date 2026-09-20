import RealRooted.BrandenLeite.WhitneyReduction

/-!
# Resolvability and total nonnegativity

This file proves the converse to the canonical Whitney construction. Finite
coefficient stages of a resolution are related by nonnegative adjacent-row
restorations, so every leading section of the original matrix is totally
nonnegative.
-/

open Matrix Polynomial

noncomputable section

namespace RealRooted.BrandenLeite

namespace Resolution

variable {R : LowerTriangularMatrix ℝ} (resolution : Resolution R)

/-- The coefficient matrix at level `k`; earlier rows remain identity rows. -/
def coefficientStage (N k : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j ↦
    if i.val < k then (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) i j
    else (resolution.polynomial i.val k).coeff j.val

theorem coefficientStage_top (N : ℕ) :
    resolution.coefficientStage N N = 1 := by
  ext i j
  by_cases hi : i.val < N
  · simp [coefficientStage, hi]
  · have hiN : i.val = N := by lia
    simp only [coefficientStage, hi, ite_false]
    rw [hiN, resolution.diagonal]
    simp only [Polynomial.coeff_X_pow, Matrix.one_apply]
    by_cases hij : i = j
    · rw [ite_eq_left hij, ite_eq_left]
      simpa [hij] using hiN
    · rw [ite_eq_right hij, ite_eq_right]
      intro hNj
      apply hij
      apply Fin.ext
      simpa [hiN] using hNj.symm

theorem coefficientStage_succ_apply_of_le (N k : ℕ)
    (i j : Fin (N + 1)) (hi : i.val ≤ k) :
    resolution.coefficientStage N (k + 1) i j =
      resolution.coefficientStage N k i j := by
  unfold coefficientStage
  rw [ite_eq_left (by lia : i.val < k + 1)]
  by_cases hik : i.val < k
  · rw [ite_eq_left hik]
  · rw [ite_eq_right hik]
    have hik_eq : i.val = k := by lia
    rw [hik_eq, resolution.diagonal]
    rw [Matrix.one_apply, Polynomial.coeff_X_pow]
    by_cases hval : i.val = j.val
    · have hij : i = j := Fin.ext hval
      have hkj : j.val = k := hval.symm.trans hik_eq
      rw [ite_eq_left hij, ite_eq_left hkj]
    · have hij : i ≠ j := fun h ↦ hval (congrArg Fin.val h)
      have hkj : j.val ≠ k := fun h ↦ hval (hik_eq.trans h.symm)
      rw [ite_eq_right hij, ite_eq_right hkj]

/-- Starting at stage `k + 1`, restore rows `k + 1, ..., k + t`. -/
def restoreAux (resolution : Resolution R) (N k : ℕ) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  | 0 => resolution.coefficientStage N (k + 1)
  | t + 1 =>
      if ht : k + t < N then
        Matrix.whitneyRestoreFirst (resolution.restoreAux N k t)
          (⟨k + t, ht⟩ : Fin N) (resolution.lambda (k + t) k)
      else resolution.restoreAux N k t

@[simp] theorem restoreAux_zero (N k : ℕ) :
    resolution.restoreAux N k 0 = resolution.coefficientStage N (k + 1) :=
  rfl

theorem restoreAux_succ_of_lt (N k t : ℕ) (ht : k + t < N) :
    resolution.restoreAux N k (t + 1) =
      Matrix.whitneyRestoreFirst (resolution.restoreAux N k t)
        (⟨k + t, ht⟩ : Fin N) (resolution.lambda (k + t) k) := by
  rw [restoreAux]
  simp only [dite_eq_left ht]

theorem restoreAux_apply (N k t : ℕ) (hk : k < N) (ht : t ≤ N - k)
    (i j : Fin (N + 1)) :
    resolution.restoreAux N k t i j =
      if i.val ≤ k + t then resolution.coefficientStage N k i j
      else resolution.coefficientStage N (k + 1) i j := by
  induction t generalizing i j with
  | zero =>
      rw [restoreAux_zero]
      by_cases hi : i.val ≤ k
      · rw [ite_eq_left (by simpa using hi)]
        exact resolution.coefficientStage_succ_apply_of_le N k i j hi
      · rw [ite_eq_right (by simpa using hi)]
  | succ t ih =>
      have hktN : k + t < N := by lia
      rw [resolution.restoreAux_succ_of_lt N k t hktN]
      simp only [Matrix.whitneyRestoreFirst, Matrix.updateRow_apply]
      let s : Fin N := ⟨k + t, hktN⟩
      by_cases his : i = s.succ
      · rw [ite_eq_left his]
        subst i
        have hsval : s.succ.val = k + t + 1 := by simp [s]
        have hpval : s.castSucc.val = k + t := by rfl
        rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          ih (by lia) s.succ j, ih (by lia) s.castSucc j]
        rw [ite_eq_right (by rw [hsval]; lia), ite_eq_left (by rw [hpval]),
          ite_eq_left (by rw [hsval]; lia)]
        unfold coefficientStage
        rw [ite_eq_right (by rw [hsval]; lia), ite_eq_right (by rw [hpval]; lia),
          ite_eq_right (by rw [hsval]; lia)]
        have hrec := resolution.recurrence (k + t) k (by lia)
        have hcoeff := congrArg (fun p : ℝ[X] ↦ p.coeff j.val) hrec
        simpa only [hsval, hpval, coeff_add, coeff_C_mul] using hcoeff.symm
      · rw [ite_eq_right his]
        rw [ih (by lia) i j]
        by_cases hiold : i.val ≤ k + t
        · rw [ite_eq_left hiold, ite_eq_left (by lia)]
        · rw [ite_eq_right hiold]
          have hinew : ¬i.val ≤ k + (t + 1) := by
            intro hinew
            have hval : i.val = k + t + 1 := by lia
            apply his
            apply Fin.ext
            simpa [s] using hval
          rw [ite_eq_right hinew]

theorem restoreAux_final (N k : ℕ) (hk : k < N) :
    resolution.restoreAux N k (N - k) =
      resolution.coefficientStage N k := by
  ext i j
  rw [resolution.restoreAux_apply N k (N - k) hk le_rfl]
  rw [ite_eq_left (by lia)]

theorem restoreAux_isTotallyNonneg (N k t : ℕ) (hk : k < N)
    (ht : t ≤ N - k)
    (hstage : Matrix.IsTotallyNonneg
      (resolution.coefficientStage N (k + 1))) :
    Matrix.IsTotallyNonneg (resolution.restoreAux N k t) := by
  induction t with
  | zero =>
      simpa only [restoreAux_zero] using hstage
  | succ t ih =>
      have hktN : k + t < N := by lia
      rw [resolution.restoreAux_succ_of_lt N k t hktN]
      exact ((ih (by lia)).toRect.whitneyRestoreFirst_nonneg
        (⟨k + t, hktN⟩ : Fin N) (resolution.lambda (k + t) k)
        (resolution.lambda_nonneg (k + t) k (by lia))).toSquare

theorem coefficientStage_isTotallyNonneg (N k : ℕ) (hk : k ≤ N) :
    Matrix.IsTotallyNonneg (resolution.coefficientStage N k) := by
  induction hk using Nat.decreasingInduction with
  | self =>
      rw [resolution.coefficientStage_top]
      simpa [Matrix.submatrix_one Fin.val Fin.val_injective] using
        (Matrix.IsTotallyNonneg.one (R := ℝ)).submatrix
          Fin.val_strictMono Fin.val_strictMono
  | of_succ k hk ih =>
      rw [← resolution.restoreAux_final N k hk]
      exact resolution.restoreAux_isTotallyNonneg N k (N - k) hk le_rfl ih

theorem coefficientStage_zero_eq_principalSection (N : ℕ) :
    resolution.coefficientStage N 0 = principalSection R (N + 1) := by
  ext i j
  rw [coefficientStage]
  simp only [Nat.not_lt_zero, ite_false, resolution.row_zero]
  exact coeff_rowPolynomial resolution.lowerUnitriangular.lower i.val j.val

/-- Every resolvable lower unitriangular matrix is totally nonnegative. -/
theorem isTotallyNonneg (resolution : Resolution R) :
    Matrix.IsTotallyNonneg R := by
  apply isTotallyNonneg_of_principalSections
  intro N
  change Matrix.IsTotallyNonneg (principalSection R (N + 1))
  rw [← coefficientStage_zero_eq_principalSection resolution N]
  exact resolution.coefficientStage_isTotallyNonneg N 0 (Nat.zero_le N)

end Resolution

theorem isTotallyNonneg_of_isResolvable
    {R : LowerTriangularMatrix ℝ} (hR : IsResolvable R) :
    Matrix.IsTotallyNonneg R := by
  rcases hR with ⟨resolution⟩
  exact Resolution.isTotallyNonneg resolution

theorem isResolvable_iff_isTotallyNonneg
    {R : LowerTriangularMatrix ℝ}
    (hunit : LowerTriangularMatrix.IsLowerUnitriangular R) :
    IsResolvable R ↔ Matrix.IsTotallyNonneg R :=
  ⟨isTotallyNonneg_of_isResolvable,
    isResolvable_of_isTotallyNonneg hunit⟩

theorem isResolvable_iff_lowerUnitriangular_and_isTotallyNonneg
    {R : LowerTriangularMatrix ℝ} :
    IsResolvable R ↔
      LowerTriangularMatrix.IsLowerUnitriangular R ∧
        Matrix.IsTotallyNonneg R := by
  constructor
  · rintro ⟨resolution⟩
    exact ⟨resolution.lowerUnitriangular,
      Resolution.isTotallyNonneg resolution⟩
  · rintro ⟨hunit, hR⟩
    exact isResolvable_of_isTotallyNonneg hunit hR

end RealRooted.BrandenLeite
