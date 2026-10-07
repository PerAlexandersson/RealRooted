module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Rank-one updates: determinant and characteristic polynomial

* `Matrix.det_add_vecMulVec`: the matrix determinant lemma
  `det (A + u vᵀ) = det A + vᵀ adj(A) u` over any commutative ring (no invertibility needed).
* `Matrix.charpoly_add_vecMulVec`: its characteristic-polynomial form, and the diagonal case.
* `Matrix.IsHermitian.charpoly_add_vecMulVec_self'`: the secular equation for a real symmetric
  `A` and `A + v vᵀ`, `χ_{A+vvᵀ} = χ_A - ∑ wᵢ² ∏_{j≠i} (X - λⱼ)` with `w` the coordinates of `v`
  in an eigenbasis of `A` (the starting point of Weyl's rank-one interlacing).
-/

public section

open Polynomial

namespace Matrix

variable {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]

/-- The matrix determinant lemma, when `A` has an invertible determinant. -/
theorem det_add_vecMulVec_of_isUnit {A : Matrix n n R} (hA : IsUnit A.det) (u v : n → R) :
    (A + vecMulVec u v).det = A.det + v ⬝ᵥ (A.adjugate *ᵥ u) := by
  have h : A + vecMulVec u v = A * (1 + vecMulVec (A⁻¹ *ᵥ u) v) := by
    rw [mul_add, mul_one, mul_vecMulVec, mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec]
  rw [h, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, inv_def,
    smul_mulVec, dotProduct_smul, smul_eq_mul, mul_add, mul_one, ← mul_assoc,
    Ring.mul_inverse_cancel _ hA, one_mul]

/-- Both sides of the matrix determinant lemma commute with ring homomorphisms. -/
private lemma map_det_add_vecMulVec_sub (f : R →+* S) (A : Matrix n n R) (u v : n → R) :
    f ((A + vecMulVec u v).det - A.det - v ⬝ᵥ (A.adjugate *ᵥ u)) =
      (f.mapMatrix A + vecMulVec (f ∘ u) (f ∘ v)).det - (f.mapMatrix A).det -
        (f ∘ v) ⬝ᵥ ((f.mapMatrix A).adjugate *ᵥ (f ∘ u)) := by
  have hmv : f ∘ (A.adjugate *ᵥ u) = (f.mapMatrix A).adjugate *ᵥ (f ∘ u) := by
    have h := f.map_adjugate A
    simp only [RingHom.mapMatrix_apply] at h
    ext i
    simp [RingHom.map_mulVec, h]
  have hvv : f.mapMatrix (A + vecMulVec u v) = f.mapMatrix A + vecMulVec (f ∘ u) (f ∘ v) := by
    ext i j
    simp [vecMulVec_apply]
  rw [map_sub, map_sub, RingHom.map_det, RingHom.map_det, RingHom.map_dotProduct, hmv, hvv]

/-- The **matrix determinant lemma** in adjugate form, over an arbitrary commutative ring:
`det (A + u vᵀ) = det A + vᵀ (adj A) u`. -/
theorem det_add_vecMulVec (A : Matrix n n R) (u v : n → R) :
    (A + vecMulVec u v).det = A.det + v ⬝ᵥ (A.adjugate *ᵥ u) := by
  -- Pass to the generic matrix `X • 1 + A` over `R[X]`, whose determinant is monic.
  set M : Matrix n n R[X] := charmatrix (-A)
  set L := Localization.Away (-A).charpoly
  have hinj : Function.Injective (algebraMap R[X] L) :=
    IsLocalization.injective L
      (Submonoid.powers_le.mpr (charpoly_monic (-A)).mem_nonZeroDivisors)
  have hunit : IsUnit ((algebraMap R[X] L).mapMatrix M).det := by
    rw [← RingHom.map_det]
    exact IsLocalization.Away.algebraMap_isUnit (-A).charpoly
  have hM : (M + vecMulVec (C ∘ u) (C ∘ v)).det - M.det -
      (C ∘ v) ⬝ᵥ (M.adjugate *ᵥ (C ∘ u)) = 0 := by
    apply hinj
    rw [map_det_add_vecMulVec_sub, map_zero, det_add_vecMulVec_of_isUnit hunit]
    simp
  have heval : (evalRingHom 0).mapMatrix M = A := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [M]
    · simp [M, hij]
  have h0 := congrArg (evalRingHom (0 : R)) hM
  rw [map_det_add_vecMulVec_sub, heval, map_zero] at h0
  have hu : (evalRingHom (0 : R)) ∘ (C ∘ u) = u := by
    ext i
    simp
  have hv : (evalRingHom (0 : R)) ∘ (C ∘ v) = v := by
    ext i
    simp
  rw [hu, hv] at h0
  rw [← sub_eq_zero, ← sub_sub]
  exact h0

/-- The characteristic polynomial of a rank-one update `A + u vᵀ`. -/
theorem charpoly_add_vecMulVec (A : Matrix n n R) (u v : n → R) :
    (A + vecMulVec u v).charpoly =
      A.charpoly - (C ∘ v) ⬝ᵥ ((charmatrix A).adjugate *ᵥ (C ∘ u)) := by
  have h : charmatrix (A + vecMulVec u v) = charmatrix A + vecMulVec (-(C ∘ u)) (C ∘ v) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [vecMulVec_apply]
      ring
    · simp [vecMulVec_apply, hij]
      ring
  rw [charpoly, h, det_add_vecMulVec, mulVec_neg, dotProduct_neg, ← sub_eq_add_neg]
  rfl

/-- The characteristic polynomial of a rank-one update `diagonal d + u vᵀ`: the secular
equation `∏ i, (X - d i) - ∑ i, u i v i ∏ j ≠ i, (X - d j)`. -/
theorem charpoly_diagonal_add_vecMulVec (d u v : n → R) :
    (diagonal d + vecMulVec u v).charpoly =
      ∏ i, (X - C (d i)) - ∑ i, C (u i * v i) * ∏ j ∈ Finset.univ.erase i, (X - C (d j)) := by
  rw [charpoly_add_vecMulVec, charpoly_diagonal, charmatrix_diagonal, adjugate_diagonal]
  congr 1
  simp only [dotProduct, mulVec_diagonal, Function.comp_apply, map_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Secular equation** for a rank-one update of a real symmetric matrix.  Let
`λ = hA.eigenvalues` and let `w = Uᵀ v` be the coordinates of `v` in the orthonormal
eigenbasis `U = hA.eigenvectorUnitary`.  Then
`charpoly (A + v vᵀ) = ∏ i, (X - λ i) - ∑ i, (w i)² ∏ j ≠ i, (X - λ j)`. -/
theorem IsHermitian.charpoly_add_vecMulVec_self {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (v : n → ℝ) :
    (A + vecMulVec v v).charpoly =
      ∏ i, (X - C (hA.eigenvalues i)) -
        ∑ i, C (((star (hA.eigenvectorUnitary : Matrix n n ℝ)) *ᵥ v) i ^ 2) *
          ∏ j ∈ Finset.univ.erase i, (X - C (hA.eigenvalues j)) := by
  set U : Matrix n n ℝ := ↑hA.eigenvectorUnitary
  set w := star U *ᵥ v
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hA' : A = U * diagonal hA.eigenvalues * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp]
  have hw : U *ᵥ w = v := by
    rw [mulVec_mulVec, hU', one_mulVec]
  have hst : star U = Uᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hv : vecMulVec v v = U * vecMulVec w w * star U := by
    rw [mul_vecMulVec, vecMulVec_mul, hw, hst, vecMul_transpose, hw]
  have hsum : A + vecMulVec v v = U * (diagonal hA.eigenvalues + vecMulVec w w) * star U := by
    rw [mul_add, add_mul, ← hA', ← hv]
  rw [hsum, charpoly_mul_comm, ← mul_assoc, hU, one_mul,
    charpoly_diagonal_add_vecMulVec]
  simp_rw [← sq]

/-- **Secular equation**, with the characteristic polynomial of `A` on the right-hand side. -/
theorem IsHermitian.charpoly_add_vecMulVec_self' {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (v : n → ℝ) :
    (A + vecMulVec v v).charpoly =
      A.charpoly -
        ∑ i, C (((star (hA.eigenvectorUnitary : Matrix n n ℝ)) *ᵥ v) i ^ 2) *
          ∏ j ∈ Finset.univ.erase i, (X - C (hA.eigenvalues j)) := by
  rw [hA.charpoly_add_vecMulVec_self, hA.charpoly_eq]
  rfl

end Matrix
