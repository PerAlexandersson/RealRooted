/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.CombinatorialExamples.CaoFu.Basic
public import RealRooted.CombinatorialExamples.CaoFu.Chebyshev
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.BandedHessenberg
import Mathlib.Tactic

/-!
# The characteristic determinant of the minimum-entry matrix

We prove the binomial formula for `det (I - z K_n)` used in Cao--Fu,
arXiv:2610.40496v1, Lemma 3.2. Adjacent row and column differences preserve
the determinant and leave a tridiagonal matrix. Its determinant recurrence
agrees with the recurrence of the binomial polynomial.
-/

@[expose] public section
noncomputable section
open Matrix Polynomial Finset
namespace RealRooted.CaoFu

private def backwardRowDiff {R : Type*} [AddGroup R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j => Fin.cases (A 0 j) (fun k => A k.succ j - A k.castSucc j) i

private theorem det_backwardRowDiff {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : (backwardRowDiff A).det = A.det := by
  symm
  apply det_eq_of_forall_row_eq_smul_add_pred (fun _ => (1 : R))
  · intro j
    simp [backwardRowDiff]
  · intro i j
    simp [backwardRowDiff]

private theorem min_second_difference {R : Type*} [CommRing R] (i j : ℕ) :
    ((min (i + 1) (j + 1) : ℕ) : R) - ((min i (j + 1) : ℕ) : R) -
      ((min (i + 1) j : ℕ) : R) + ((min i j : ℕ) : R) = if i = j then 1 else 0 := by
  rcases lt_trichotomy i j with h | h | h
  · rw [min_eq_left (by lia), min_eq_left (by lia), min_eq_left (by lia),
      min_eq_left h.le, ite_eq_right h.ne]
    push_cast
    ring
  · subst j
    simp only [min_self, min_eq_left (Nat.le_add_right _ _),
      min_eq_right (Nat.le_add_right _ _), ite_true]
    push_cast
    ring
  · rw [min_eq_right (by lia), min_eq_right (by lia), min_eq_right (by lia),
      min_eq_right h.le, ite_eq_right h.ne']
    push_cast
    ring

private def minimumPencil (n : ℕ) : Matrix (Fin n) (Fin n) ℝ[X] :=
  1 - (X : ℝ[X]) • Matrix.of (fun i j : Fin n => ((min i.val j.val + 1 : ℕ) : ℝ[X]))

private def differencePencil (n : ℕ) : Matrix (Fin n) (Fin n) ℝ[X] :=
  Matrix.bandedLowerHessenberg (fun i => if i = 0 then 1 - X else 2 - X)
    (fun _ => -1) (fun _ => 0) (-1) n

private theorem backwardRowDiff_minimumPencil (n : ℕ) :
    backwardRowDiff (backwardRowDiff (minimumPencil (n + 1))).transpose =
      differencePencil (n + 1) := by
  apply Matrix.ext
  intro i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp [backwardRowDiff, minimumPencil, differencePencil, Matrix.one_apply]
    | succ j =>
      by_cases hj : j.val = 0
      · simp [backwardRowDiff, minimumPencil, differencePencil, Matrix.one_apply,
          Fin.ext_iff, hj]
        ring
      · simp [backwardRowDiff, minimumPencil, differencePencil, Matrix.one_apply,
          Fin.ext_iff, hj]
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      by_cases hi : i.val = 0
      · simp [backwardRowDiff, minimumPencil, differencePencil, Matrix.one_apply,
          Fin.ext_iff, hi]
        ring
      · simp [backwardRowDiff, minimumPencil, differencePencil, Matrix.one_apply,
          Fin.ext_iff, hi, Ne.symm hi]
    | succ j =>
      simp only [backwardRowDiff, Matrix.transpose_apply, Fin.cases_succ, minimumPencil,
        Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
        Fin.ext_iff, Fin.val_succ, Fin.val_castSucc, differencePencil,
        Matrix.bandedLowerHessenberg_apply]
      have hmin := min_second_difference (R := ℝ[X]) j.val i.val
      simp only [Nat.add_right_cancel_iff, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ite_false]
      by_cases hij : i.val = j.val
      · have heq : i = j := Fin.ext hij
        subst j
        simp
        ring
      · have hji : j.val ≠ i.val := Ne.symm hij
        simp only [hij, hji, ite_false] at hmin ⊢
        by_cases hleft : i.val = j.val + 1
        · have hright : j.val ≠ i.val + 1 := by lia
          have hleft' : j.val + 1 = i.val := hleft.symm
          simp only [ite_eq_left hleft, ite_eq_left hleft', ite_eq_right hright,
            ite_self]
          push_cast at hmin ⊢
          linear_combination -X * hmin
        · by_cases hright : j.val = i.val + 1
          · have hleft' : j.val + 1 ≠ i.val := Ne.symm hleft
            simp only [ite_eq_right hleft, ite_eq_right hleft', ite_eq_left hright,
              ite_self]
            push_cast at hmin ⊢
            linear_combination -X * hmin
          · have hleft' : j.val + 1 ≠ i.val := Ne.symm hleft
            simp only [ite_eq_right hleft, ite_eq_right hleft', ite_eq_right hright,
              ite_self]
            push_cast at hmin ⊢
            linear_combination -X * hmin

private theorem det_minimumPencil_eq_differencePencil (n : ℕ) :
    (minimumPencil n).det = (differencePencil n).det := by
  cases n with
  | zero => simp
  | succ n =>
    rw [← backwardRowDiff_minimumPencil, det_backwardRowDiff, Matrix.det_transpose,
      det_backwardRowDiff]

private theorem det_differencePencil_eq_traceDenominator (n : ℕ) :
    (differencePencil n).det = traceDenominator n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [differencePencil, Matrix.bandedLowerHessenberg]
  | more n ih0 ih1 =>
    cases n with
    | zero =>
      change (differencePencil 2).det = traceDenominator 2
      rw [differencePencil, Matrix.det_fin_two]
      norm_num [Matrix.bandedLowerHessenberg, traceDenominator, Finset.sum_range_succ]
      ring
    | succ n =>
      have h := Matrix.det_bandedLowerHessenberg_add_three
        (fun i => if i = 0 then (1 - X : ℝ[X]) else 2 - X)
        (fun _ => (-1 : ℝ[X])) (fun _ => (0 : ℝ[X])) (-1) n
      change (differencePencil (n + 1 + 2)).det = traceDenominator (n + 1 + 2)
      rw [show n + 1 + 2 = n + 3 by lia, differencePencil, h]
      change (2 - X) * (differencePencil (n + 2)).det -
        (-1 : ℝ[X]) * (-1) * (differencePencil (n + 1)).det +
        0 * (-1) ^ 2 * (differencePencil n).det = traceDenominator (n + 3)
      rw [show n + 2 = n + 1 + 1 by lia, ih1, ih0]
      conv_rhs => rw [show n + 3 = (n + 1) + 2 by lia, traceDenominator_add_two]
      simp only [map_ofNat]
      ring

/-- The one-based minimum-entry transfer matrix of size `n`. -/
def minimumMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ((min i.val j.val + 1 : ℕ) : ℝ)

/-- The existing transfer trace is the power trace of the minimum-entry matrix. -/
theorem transferTrace_eq_trace_minimumMatrix_pow (r q : ℕ) :
    transferTrace r q = Matrix.trace (minimumMatrix (q + 1) ^ r) := by
  simp only [transferTrace, minimumMatrix, Nat.cast_add, Nat.cast_one, Nat.cast_min]

/-- The determinant generating polynomial of the minimum-entry matrix is the
explicit binomial polynomial in Cao--Fu, Lemma 3.2. -/
theorem det_one_sub_X_smul_minimumMatrix (n : ℕ) :
    (1 - (X : ℝ[X]) • (minimumMatrix n).map Polynomial.C).det = traceDenominator n := by
  have hm : (minimumMatrix n).map Polynomial.C =
      Matrix.of (fun i j : Fin n => ((min i.val j.val + 1 : ℕ) : ℝ[X])) := by
    apply Matrix.ext
    intro i j
    change Polynomial.C (((min i.val j.val + 1 : ℕ) : ℝ)) =
      ((min i.val j.val + 1 : ℕ) : ℝ[X])
    rw [map_natCast]
  rw [hm]
  change (minimumPencil n).det = traceDenominator n
  rw [det_minimumPencil_eq_differencePencil, det_differencePencil_eq_traceDenominator]

end RealRooted.CaoFu
