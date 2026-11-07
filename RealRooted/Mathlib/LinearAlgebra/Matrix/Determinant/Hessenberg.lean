/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Nat.Factorial.BigOperators

/-! A division-free determinant identity from a sparse matrix-vector product. -/

public section

namespace Matrix

variable {R : Type*} [CommRing R]

/-- A sparse matrix-vector product determines a determinant whenever one
coordinate of the vector is one. No invertibility hypothesis is needed. -/
theorem det_eq_adjugate_mul_of_mulVec_eq_single
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (v : ι → R) (i j : ι) (a : R)
    (hv : v i = 1) (hAv : A *ᵥ v = Pi.single j a) :
    A.det = A.adjugate i j * a := by
  have h := congrArg (fun w : ι → R => w i)
    (congrArg (fun w : ι → R => A.adjugate *ᵥ w) hAv)
  simpa [mulVec_mulVec, adjugate_mul, smul_mulVec, hv, mulVec_single] using h

/-- Deleting the last row and first column of a lower-Hessenberg matrix
leaves a lower-triangular matrix. Its determinant is the product of the
original superdiagonal entries. -/
theorem det_submatrix_castSucc_succ_of_hessenberg {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hA : ∀ i j, i.val + 1 < j.val → A i j = 0) :
    (A.submatrix Fin.castSucc Fin.succ).det =
      ∏ i : Fin n, A i.castSucc i.succ := by
  apply det_of_isLowerTriangular
  intro i j hij
  apply hA
  change i.val + 1 < j.val + 1
  exact Nat.add_lt_add_right hij 1

/-- A lower-Hessenberg determinant is recovered from a vector with first
coordinate one whose image is supported at the last coordinate. -/
theorem det_eq_superdiagonal_prod_mul_of_mulVec_eq_single {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hA : ∀ i j, i.val + 1 < j.val → A i j = 0)
    (v : Fin (n + 1) → R) (hv : v 0 = 1) (a : R)
    (hAv : A *ᵥ v = Pi.single (Fin.last n) a) :
    A.det = (-1 : R) ^ n *
      (∏ i : Fin n, A i.castSucc i.succ) * a := by
  rw [det_eq_adjugate_mul_of_mulVec_eq_single A v 0 (Fin.last n) a hv hAv,
    adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_last, Fin.val_zero, add_zero, Fin.succAbove_last,
    Fin.succAbove_zero]
  rw [det_submatrix_castSucc_succ_of_hessenberg A hA]

/-- Truncating an annihilated vector for a lower-Hessenberg matrix leaves
only the final boundary term. -/
theorem leading_mulVec_eq_single_of_sum_eq_zero
    (A : Matrix ℕ ℕ R) (v : ℕ → R)
    (hA : ∀ i j, i + 1 < j → A i j = 0)
    (hv : ∀ i, ∑ j ∈ Finset.range (i + 2), A i j * v j = 0)
    (n : ℕ) :
    (A.submatrix Fin.val Fin.val : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ
        (fun j => v j.val) =
      Pi.single (Fin.last n) (-(A n (n + 1) * v (n + 1))) := by
  ext i
  change (∑ j : Fin (n + 1), A i.val j.val * v j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun j => A i.val j * v j) (n + 1)]
  by_cases hi : i = Fin.last n
  · subst i
    simp only [Fin.val_last, Pi.single_eq_same]
    have hn := hv n
    rw [show n + 2 = (n + 1) + 1 by lia, Finset.sum_range_succ] at hn
    exact eq_neg_of_add_eq_zero_left hn
  · rw [Pi.single_eq_of_ne hi]
    have hin : i.val < n := by
      have hi' := i.isLt
      have : i.val ≠ n := by
        intro h
        apply hi
        exact Fin.ext h
      lia
    have hsum :
        (∑ j ∈ Finset.range (i.val + 2), A i.val j * v j) =
          ∑ j ∈ Finset.range (n + 1), A i.val j * v j := by
      apply Finset.sum_subset (Finset.range_mono (by lia))
      intro j _ hj
      have hj' : ¬j < i.val + 2 := by simpa using hj
      rw [hA i.val j (by lia)]
      simp
    rw [← hsum]
    exact hv i.val

/-- If a normalized formal vector is annihilated by a lower-Hessenberg
matrix with superdiagonal `1,2,3,...`, each leading determinant recovers
its next coordinate, multiplied by a signed factorial. -/
theorem det_leading_eq_factorial_mul_of_sum_eq_zero
    (A : Matrix ℕ ℕ R) (v : ℕ → R)
    (hA : ∀ i j, i + 1 < j → A i j = 0)
    (hsuper : ∀ i, A i (i + 1) = (i + 1 : ℕ))
    (hzero : v 0 = 1)
    (hv : ∀ i, ∑ j ∈ Finset.range (i + 2), A i j * v j = 0)
    (n : ℕ) :
    (A.submatrix Fin.val Fin.val : Matrix (Fin n) (Fin n) R).det =
      (-1 : R) ^ n * (n.factorial : R) * v n := by
  cases n with
  | zero => simp [hzero]
  | succ n =>
    rw [det_eq_superdiagonal_prod_mul_of_mulVec_eq_single
      (A.submatrix (Fin.val : Fin (n + 1) → ℕ) Fin.val)
      (fun i j hij => hA i.val j.val hij) (fun j => v j.val)
      hzero _ (leading_mulVec_eq_single_of_sum_eq_zero A v hA hv n)]
    have hprod :
        (∏ i : Fin n, A i.val (i.val + 1)) = (n.factorial : R) := by
      simp only [hsuper]
      rw [Fin.prod_univ_eq_prod_range (fun i => ((i + 1 : ℕ) : R)) n]
      norm_cast
      exact congrArg (fun k : ℕ => (k : R)) (Finset.prod_range_add_one_eq_factorial n)
    simp only [Matrix.submatrix_apply, Fin.val_castSucc, Fin.val_succ]
    rw [hprod, hsuper, pow_succ, Nat.factorial_succ]
    push_cast
    ring


end Matrix
