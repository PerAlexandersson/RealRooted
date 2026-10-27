/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import RealRooted.Mathlib.Algebra.LinearRecurrence.Annihilator
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Linear recurrences for arithmetic subsequences

This file proves the Cayley--Hamilton construction of a recurrence for every
arithmetic subsequence of a finite-dimensional matrix orbit: if `v (n + 1) = A *ᵥ v n`, then
every coordinate of `m ↦ v (p * m + c)` satisfies the recurrence given by `charpoly (A ^ p)`.
-/

@[expose] public section

open Finset Polynomial
open scoped Matrix

noncomputable section

namespace LinearRecurrence

variable {R : Type*} [CommRing R]

/-- The recurrence encoded by the characteristic polynomial of a square matrix. -/
def ofMatrix {k : ℕ} (A : Matrix (Fin k) (Fin k) R) : LinearRecurrence R :=
  ⟨k, fun i ↦ -A.charpoly.coeff i⟩

/-- Iterating a one-step matrix state transition advances the state by a matrix power. -/
theorem state_add_eq_pow_mulVec {k : ℕ} {A : Matrix (Fin k) (Fin k) R}
    {v : ℕ → Fin k → R} (hv : ∀ n, v (n + 1) = A *ᵥ v n) (n t : ℕ) :
    v (n + t) = A ^ t *ᵥ v n := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.add_succ, hv, ih, Matrix.mulVec_mulVec, pow_succ']

private theorem aeval_forwardShift_apply_eq_mulVec {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (v : ℕ → Fin k → R)
    (hv : ∀ n, v (n + 1) = A *ᵥ v n) (j : Fin k) (q : R[X]) (m : ℕ) :
    Polynomial.aeval forwardShift q (fun n ↦ v n j) m =
      (Polynomial.aeval A q *ᵥ v m) j := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
      simp only [map_add, LinearMap.add_apply, Pi.add_apply, hq, hr,
        Matrix.add_mulVec]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
      simp only [Module.End.mul_apply, Module.algebraMap_end_apply,
        Matrix.algebraMap_eq_diagonal, Pi.smul_apply, smul_eq_mul]
      rw [LinearRecurrence.forwardShift_pow_apply,
        state_add_eq_pow_mulVec hv m n]
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
      simp

/-- Every coordinate of a matrix orbit satisfies the recurrence encoded by the
matrix characteristic polynomial. -/
theorem ofMatrix_isSolution {k : ℕ} (A : Matrix (Fin k) (Fin k) R)
    (v : ℕ → Fin k → R) (hv : ∀ n, v (n + 1) = A *ᵥ v n) (j : Fin k) :
    (ofMatrix A).IsSolution fun n ↦ v n j := by
  rw [isSolution_iff_aeval_charPoly_eq_zero]
  have hchar : (ofMatrix A).charPoly = A.charpoly := by
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Subsingleton.elim _ _
    let _ := hR
    change Polynomial.monomial k 1 -
      ∑ i : Fin k, Polynomial.monomial i (-A.charpoly.coeff i) = A.charpoly
    ext n
    simp only [coeff_sub, coeff_monomial, finsetSum_coeff]
    rcases lt_trichotomy n k with hn | hn | hn
    · have hsum : (∑ i : Fin k, if (i : ℕ) = n then -A.charpoly.coeff i else 0) =
          -A.charpoly.coeff n := by
        rw [Finset.sum_eq_single ⟨n, hn⟩]
        · simp
        · intro b _ hb
          split_ifs with hbn
          · exact (hb (Fin.ext hbn)).elim
          · rfl
        · simp
      rw [hsum]
      rw [ite_eq_right (ne_of_gt hn), zero_sub, neg_neg]
    · subst n
      have hsum : (∑ i : Fin k, if (i : ℕ) = k then -A.charpoly.coeff i else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp [i.isLt.ne]
      rw [hsum, sub_zero]
      rw [ite_eq_left rfl]
      have hlead := A.charpoly_monic.coeff_natDegree
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hlead
      exact hlead.symm
    · have hcoeff : A.charpoly.coeff n = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using hn
      have hsum : (∑ i : Fin k, if (i : ℕ) = n then -A.charpoly.coeff i else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp [ne_of_lt (i.isLt.trans hn)]
      rw [hsum, hcoeff]
      rw [ite_eq_right (ne_of_lt hn), sub_zero]
  rw [hchar]
  ext m
  rw [aeval_forwardShift_apply_eq_mulVec A v hv j A.charpoly m,
    Matrix.aeval_self_charpoly]
  simp

/-- A `p`-step arithmetic subsequence of a matrix orbit satisfies the
characteristic recurrence of `A ^ p`, independently of its offset. -/
theorem ofMatrix_pow_isSolution_subsequence {k : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (v : ℕ → Fin k → R)
    (hv : ∀ n, v (n + 1) = A *ᵥ v n) (p c : ℕ) (j : Fin k) :
    (ofMatrix (A ^ p)).IsSolution fun m ↦ v (p * m + c) j := by
  apply ofMatrix_isSolution (A ^ p) (fun m ↦ v (p * m + c))
  intro m
  rw [show p * (m + 1) + c = (p * m + c) + p by ring]
  exact state_add_eq_pow_mulVec hv (p * m + c) p

end LinearRecurrence
