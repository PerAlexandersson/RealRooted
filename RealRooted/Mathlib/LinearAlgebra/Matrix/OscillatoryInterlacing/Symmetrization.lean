/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Basic.Real.Star
import Mathlib.Algebra.Order.Star.Real
public import RealRooted.Mathlib.LinearAlgebra.Matrix.GantmacherKrein
import RealRooted.Mathlib.LinearAlgebra.Matrix.Oscillatory
import RealRooted.Mathlib.LinearAlgebra.Matrix.Charpoly.Submatrix
public import Mathlib.Data.Fin.Rev
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Transvection
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
public import Mathlib.Analysis.Real.Sqrt
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Charpoly
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Lemmas
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg
import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Border

/-!
# Tridiagonal symmetrization and continuants

Diagonal conjugation and geometric-mean Hermitian models, continuant
recurrences, and finite-index reversal.
-/

@[expose] public section

namespace Matrix

open scoped BigOperators

private noncomputable def tridiagonalScale {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : Fin (N + 1) → ℝ :=
  fun i ↦ Nat.rec (motive := fun k ↦ k < N + 1 → ℝ)
    (fun _ ↦ 1)
    (fun k previous hk ↦
      let j : Fin N := ⟨k, by lia⟩
      previous (by lia) *
        Real.sqrt (T j.succ j.castSucc / T j.castSucc j.succ))
    i.val i.isLt

@[simp] private theorem tridiagonalScale_zero {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    tridiagonalScale T 0 = 1 := rfl

private theorem tridiagonalScale_succ {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (i : Fin N) :
    tridiagonalScale T i.succ = tridiagonalScale T i.castSucc *
      Real.sqrt (T i.succ i.castSucc / T i.castSucc i.succ) := by
  rfl

private theorem tridiagonalScale_pos {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hsuper : ∀ i : Fin N, 0 < T i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < T i.succ i.castSucc) :
    ∀ i, 0 < tridiagonalScale T i := by
  intro i
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
      rw [tridiagonalScale_succ]
      exact mul_pos ih (Real.sqrt_pos.2 (div_pos (hsub i) (hsuper i)))

private noncomputable def symmetrizeTridiagonal {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  let d := tridiagonalScale T
  Matrix.diagonal (fun i ↦ (d i)⁻¹) * T * Matrix.diagonal d

private theorem symmetrizeTridiagonal_apply {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (i j : Fin (N + 1)) :
    symmetrizeTridiagonal T i j =
      (tridiagonalScale T i)⁻¹ * T i j * tridiagonalScale T j := by
  simp [symmetrizeTridiagonal]

private theorem charpoly_diagonal_conjugate {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℝ) (d : n → ℝ) (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal (fun i ↦ (d i)⁻¹) * T * Matrix.diagonal d).charpoly =
      T.charpoly := by
  let D := Matrix.diagonal d
  let Dinv := Matrix.diagonal (fun i ↦ (d i)⁻¹)
  have hcancel : D * Dinv = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hd i]
    · simp [hij]
  calc
    (Matrix.diagonal (fun i ↦ (d i)⁻¹) * T * Matrix.diagonal d).charpoly =
        (Dinv * T * D).charpoly := rfl
    _ = (D * (Dinv * T)).charpoly := Matrix.charpoly_mul_comm _ _
    _ = ((D * Dinv) * T).charpoly := by rw [Matrix.mul_assoc]
    _ = T.charpoly := by rw [hcancel, Matrix.one_mul]

private theorem symmetrizeTridiagonal_charpoly {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hd : ∀ i, tridiagonalScale T i ≠ 0) :
    (symmetrizeTridiagonal T).charpoly = T.charpoly :=
  charpoly_diagonal_conjugate T (tridiagonalScale T) hd

private theorem symmetrizeTridiagonal_trailing_charpoly {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hd : ∀ i, tridiagonalScale T i ≠ 0) :
    ((symmetrizeTridiagonal T).submatrix Fin.succ Fin.succ).charpoly =
      (T.submatrix Fin.succ Fin.succ).charpoly := by
  let d : Fin N → ℝ := fun i ↦ tridiagonalScale T i.succ
  let D := Matrix.diagonal d
  let Dinv := Matrix.diagonal (fun i ↦ (d i)⁻¹)
  have hmatrix : (symmetrizeTridiagonal T).submatrix Fin.succ Fin.succ =
      Dinv * T.submatrix Fin.succ Fin.succ * D := by
    ext i j
    simp [D, Dinv, d, symmetrizeTridiagonal_apply]
  rw [hmatrix]
  exact charpoly_diagonal_conjugate _ d fun i ↦ hd i.succ

private theorem symmetrizeTridiagonal_adjacent {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hsuper : ∀ i : Fin N, 0 < T i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < T i.succ i.castSucc) (i : Fin N) :
    symmetrizeTridiagonal T i.castSucc i.succ =
      symmetrizeTridiagonal T i.succ i.castSucc := by
  have hdpos := tridiagonalScale_pos T hsuper hsub i.castSucc
  have hratio : 0 < T i.succ i.castSucc / T i.castSucc i.succ :=
    div_pos (hsub i) (hsuper i)
  have hsqrt : 0 < Real.sqrt
      (T i.succ i.castSucc / T i.castSucc i.succ) :=
    Real.sqrt_pos.2 hratio
  have hsquare : Real.sqrt
      (T i.succ i.castSucc / T i.castSucc i.succ) ^ 2 =
        T i.succ i.castSucc / T i.castSucc i.succ :=
    Real.sq_sqrt hratio.le
  rw [symmetrizeTridiagonal_apply, symmetrizeTridiagonal_apply,
    tridiagonalScale_succ]
  field_simp [hdpos.ne', hsqrt.ne', (hsuper i).ne']
  rw [hsquare]
  field_simp [(hsuper i).ne']

private theorem symmetrizeTridiagonal_isHermitian {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hlower : ∀ r k, k.val + 1 < r.val → T r k = 0)
    (hupper : ∀ i j, i.val + 1 < j.val → T i j = 0)
    (hsuper : ∀ i : Fin N, 0 < T i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < T i.succ i.castSucc) :
    (symmetrizeTridiagonal T).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial]
  rcases lt_trichotomy i j with hij | rfl | hji
  · by_cases hadj : i.val + 1 = j.val
    · let k : Fin N := ⟨i.val, by have := j.isLt; lia⟩
      have hi : k.castSucc = i := Fin.ext rfl
      have hj : k.succ = j := Fin.ext hadj
      rw [← hi, ← hj]
      exact (symmetrizeTridiagonal_adjacent T hsuper hsub k).symm
    · have hgap : i.val + 1 < j.val := by lia
      rw [symmetrizeTridiagonal_apply, symmetrizeTridiagonal_apply,
        hupper i j hgap, hlower j i hgap]
      ring
  · rfl
  · by_cases hadj : j.val + 1 = i.val
    · let k : Fin N := ⟨j.val, by have := i.isLt; lia⟩
      have hj : k.castSucc = j := Fin.ext rfl
      have hi : k.succ = i := Fin.ext hadj
      rw [← hi, ← hj]
      exact symmetrizeTridiagonal_adjacent T hsuper hsub k
    · have hgap : j.val + 1 < i.val := by lia
      rw [symmetrizeTridiagonal_apply, symmetrizeTridiagonal_apply,
        hupper j i hgap, hlower i j hgap]
      ring

/-! ### Geometric-mean symmetrization -/

/-- Replace each off-diagonal pair of a real matrix by the square root of its
product. The diagonal is unchanged. This is useful when the paired products
are nonnegative but one of the two entries may vanish, so diagonal similarity
cannot be used to symmetrize the matrix. -/
noncomputable def geometricSymmetrization {n : Type*} [DecidableEq n]
    (A : Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j ↦ if i = j then A i i else Real.sqrt (A i j * A j i)

@[simp] theorem geometricSymmetrization_apply_self {n : Type*}
    [DecidableEq n] (A : Matrix n n ℝ) (i : n) :
    geometricSymmetrization A i i = A i i := by
  simp [geometricSymmetrization]

theorem geometricSymmetrization_apply_of_ne {n : Type*} [DecidableEq n]
    (A : Matrix n n ℝ) {i j : n} (hij : i ≠ j) :
    geometricSymmetrization A i j = Real.sqrt (A i j * A j i) := by
  simp [geometricSymmetrization, hij]

/-- Geometric-mean symmetrization is Hermitian over the reals. -/
theorem geometricSymmetrization_isHermitian {n : Type*} [DecidableEq n]
    (A : Matrix n n ℝ) : (geometricSymmetrization A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial]
  by_cases hij : i = j
  · subst j
    rfl
  · simp [geometricSymmetrization, hij, Ne.symm hij, mul_comm]

/-- Taking a submatrix along an injective index map commutes with
geometric-mean symmetrization. -/
theorem geometricSymmetrization_submatrix {m n : Type*}
    [DecidableEq m] [DecidableEq n] (A : Matrix n n ℝ)
    (e : m → n) (he : Function.Injective e) :
    (geometricSymmetrization A).submatrix e e =
      geometricSymmetrization (A.submatrix e e) := by
  ext i j
  simp [geometricSymmetrization, he.eq_iff]

/-- Taking the trailing principal submatrix commutes with geometric-mean
symmetrization. -/
theorem geometricSymmetrization_submatrix_succ {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    (geometricSymmetrization T).submatrix Fin.succ Fin.succ =
      geometricSymmetrization (T.submatrix Fin.succ Fin.succ) :=
  geometricSymmetrization_submatrix T Fin.succ (Fin.succ_injective N)

/-- Geometric-mean symmetrization preserves the full and trailing
characteristic polynomials of a tridiagonal matrix whose paired adjacent
entries have nonnegative product. -/
theorem geometricSymmetrization_charpoly_eq_and_trailing {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hlower : ∀ r k, k.val + 1 < r.val → T r k = 0)
    (hupper : ∀ i j, i.val + 1 < j.val → T i j = 0)
    (hprod : ∀ i : Fin N,
      0 ≤ T i.castSucc i.succ * T i.succ i.castSucc) :
    (geometricSymmetrization T).charpoly = T.charpoly ∧
      ((geometricSymmetrization T).submatrix Fin.succ Fin.succ).charpoly =
        (T.submatrix Fin.succ Fin.succ).charpoly := by
  induction N with
  | zero =>
      have hmatrix : geometricSymmetrization T = T := by
        ext i j
        have hij : i = j := by rw [Fin.eq_zero i, Fin.eq_zero j]
        subst j
        simp
      simp [hmatrix]
  | succ N ih =>
      let U := T.submatrix Fin.succ Fin.succ
      have hUlower : ∀ r k, k.val + 1 < r.val → U r k = 0 :=
        fun r k hrk => hlower r.succ k.succ (by simpa [U] using hrk)
      have hUupper : ∀ i j, i.val + 1 < j.val → U i j = 0 :=
        fun i j hij => hupper i.succ j.succ (by simpa [U] using hij)
      have hUprod : ∀ i : Fin N,
          0 ≤ U i.castSucc i.succ * U i.succ i.castSucc := by
        intro i
        simpa [U, Matrix.submatrix] using hprod i.succ
      have htail := ih U hUlower hUupper hUprod
      have hgeomLower : ∀ r k, k.val + 1 < r.val →
          geometricSymmetrization T r k = 0 := by
        intro r k hrk
        rw [geometricSymmetrization_apply_of_ne T (by lia),
          hlower r k hrk, zero_mul, Real.sqrt_zero]
      have hgeomUpper : ∀ i j, i.val + 1 < j.val →
          geometricSymmetrization T i j = 0 := by
        intro i j hij
        rw [geometricSymmetrization_apply_of_ne T (by lia),
          hupper i j hij, zero_mul, Real.sqrt_zero]
      have hadj : geometricSymmetrization T 0 1 *
          geometricSymmetrization T 1 0 = T 0 1 * T 1 0 := by
        have hprod0 : 0 ≤ T 0 1 * T 1 0 := by
          simpa using hprod 0
        rw [geometricSymmetrization_apply_of_ne T zero_ne_one,
          geometricSymmetrization_apply_of_ne T one_ne_zero]
        rw [mul_comm (T 1 0) (T 0 1)]
        exact Real.mul_self_sqrt hprod0
      have htailGeom := geometricSymmetrization_submatrix_succ T
      constructor
      · rw [charpoly_tridiagonal_rec _ hgeomLower hgeomUpper,
          charpoly_tridiagonal_rec T hlower hupper,
          geometricSymmetrization_apply_self, hadj, htailGeom,
          htail.1, htail.2]
      · rw [htailGeom]
        exact htail.1

/-- A real tridiagonal matrix with nonnegative paired adjacent products has a
Hermitian model with the same full and trailing characteristic polynomials. -/
theorem exists_hermitianModel_of_tridiagonal_of_nonneg_product {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hlower : ∀ r k, k.val + 1 < r.val → T r k = 0)
    (hupper : ∀ i j, i.val + 1 < j.val → T i j = 0)
    (hprod : ∀ i : Fin N,
      0 ≤ T i.castSucc i.succ * T i.succ i.castSucc) :
    ∃ S : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
      S.IsHermitian ∧ S.charpoly = T.charpoly ∧
        (S.submatrix Fin.succ Fin.succ).charpoly =
          (T.submatrix Fin.succ Fin.succ).charpoly :=
  ⟨geometricSymmetrization T,
    geometricSymmetrization_isHermitian T,
    geometricSymmetrization_charpoly_eq_and_trailing T hlower hupper hprod⟩

private theorem charpoly_tridiagonal_no_common_root {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hlower : ∀ r k, k.val + 1 < r.val → T r k = 0)
    (hupper : ∀ i j, i.val + 1 < j.val → T i j = 0)
    (hsuper : ∀ i : Fin N, 0 < T i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < T i.succ i.castSucc) :
    ∀ x : ℝ, ¬(T.charpoly.IsRoot x ∧
      (T.submatrix Fin.succ Fin.succ).charpoly.IsRoot x) := by
  induction N with
  | zero =>
      intro x hroots
      have hzero := hroots.2.eq_zero
      simp [Matrix.charpoly, Matrix.charmatrix] at hzero
  | succ N ih =>
      intro x hroots
      let B := T.submatrix Fin.succ Fin.succ
      have hBlower : ∀ r k, k.val + 1 < r.val → B r k = 0 :=
        fun r k hrk => hlower r.succ k.succ (by simpa [B] using hrk)
      have hBupper : ∀ i j, i.val + 1 < j.val → B i j = 0 :=
        fun i j hij => hupper i.succ j.succ (by simpa [B] using hij)
      have hBsuper : ∀ i : Fin N, 0 < B i.castSucc i.succ := by
        intro i
        simpa [B, Matrix.submatrix] using hsuper i.succ
      have hBsub : ∀ i : Fin N, 0 < B i.succ i.castSucc := by
        intro i
        simpa [B, Matrix.submatrix] using hsub i.succ
      have hrec := congrArg (Polynomial.eval x)
        (charpoly_tridiagonal_rec T hlower hupper)
      have hprod : (T 0 1 * T 1 0) *
          Polynomial.eval x
            ((T.submatrix Fin.succ Fin.succ).submatrix
              Fin.succ Fin.succ).charpoly = 0 := by
        simp only [Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_X, Polynomial.eval_C, hroots.1.eq_zero,
          hroots.2.eq_zero] at hrec
        linarith
      have hcoeff : T 0 1 * T 1 0 ≠ 0 :=
        mul_ne_zero (hsuper 0).ne' (hsub 0).ne'
      have htailRoot :
          ((T.submatrix Fin.succ Fin.succ).submatrix
            Fin.succ Fin.succ).charpoly.IsRoot x :=
        Polynomial.IsRoot.def.2 ((mul_eq_zero.mp hprod).resolve_left hcoeff)
      exact ih B hBlower hBupper hBsuper hBsub x ⟨hroots.2, htailRoot⟩

/-- A real tridiagonal matrix with positive adjacent off-diagonal entries has
a Hermitian diagonal-similarity model with the same full and trailing
characteristic polynomials. Its consecutive trailing characteristic
polynomials have no common root. -/
theorem exists_hermitianModel_of_tridiagonal {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hlower : ∀ r k, k.val + 1 < r.val → T r k = 0)
    (hupper : ∀ i j, i.val + 1 < j.val → T i j = 0)
    (hsuper : ∀ i : Fin N, 0 < T i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < T i.succ i.castSucc) :
    ∃ S : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
      S.IsHermitian ∧
        S.charpoly = T.charpoly ∧
        (S.submatrix Fin.succ Fin.succ).charpoly =
          (T.submatrix Fin.succ Fin.succ).charpoly ∧
        ∀ x : ℝ, ¬(T.charpoly.IsRoot x ∧
          (T.submatrix Fin.succ Fin.succ).charpoly.IsRoot x) := by
  let S := symmetrizeTridiagonal T
  have hdpos := tridiagonalScale_pos T hsuper hsub
  have hdne : ∀ i, tridiagonalScale T i ≠ 0 := fun i ↦ (hdpos i).ne'
  exact ⟨S,
    symmetrizeTridiagonal_isHermitian T hlower hupper hsuper hsub,
    symmetrizeTridiagonal_charpoly T hdne,
    symmetrizeTridiagonal_trailing_charpoly T hdne,
    charpoly_tridiagonal_no_common_root T hlower hupper hsuper hsub⟩

/-- Reversing both indices sends the trailing principal submatrix to the
reversal of the leading principal submatrix. -/
theorem reindex_finRev_submatrix_succ {R : Type*} {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    (Matrix.reindex Fin.revPerm Fin.revPerm A).submatrix Fin.succ Fin.succ =
      Matrix.reindex Fin.revPerm Fin.revPerm
        (A.submatrix Fin.castSucc Fin.castSucc) := by
  ext i j
  simp [Matrix.submatrix, Matrix.reindex_apply, Fin.rev_succ]

/-- The trailing principal characteristic polynomial after reversing both
indices is the leading principal characteristic polynomial of the original
matrix. -/
theorem charpoly_reindex_finRev_submatrix_succ {R : Type*} [CommRing R]
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    ((Matrix.reindex Fin.revPerm Fin.revPerm A).submatrix
      Fin.succ Fin.succ).charpoly =
        (A.submatrix Fin.castSucc Fin.castSucc).charpoly := by
  rw [reindex_finRev_submatrix_succ]
  exact Matrix.charpoly_reindex Fin.revPerm _

end Matrix
