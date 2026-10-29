/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import RealRooted.Mathlib.LinearAlgebra.Matrix.Charpoly.TraceSq
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Entry degrees of polynomial matrices and trace-form symmetry

* `Matrix.natDegree_charpoly_coeff_le_iff_entry_le_of_isSymm`: for a symmetric real polynomial
  matrix, the coefficient-degree bounds of the characteristic polynomial are equivalent to the
  entrywise degree bound (the converse of `Matrix.natDegree_entry_le_of_isSymm_charpoly`).
* `Algebra.leftMulMatrix_isSymm_of_smul_traceForm_toMatrix_eq_one`: multiplication matrices are
  symmetric in a basis orthonormal for a scaled trace form.
* `PowerBasis.charpoly_leftMulMatrix`: multiplication by a power-basis generator has its minimal
  polynomial as characteristic polynomial in any basis.

These are steps B1 and D1 of the determinantal-representation plan in RealRooted issue #954.
-/

public section

open Polynomial

namespace Matrix

private theorem natDegree_det_le_of_entry_le {R n : Type*} [CommRing R]
    [Fintype n] [DecidableEq n] (M : Matrix n n R[X]) (k : ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ k) : M.det.natDegree ≤ Fintype.card n * k := by
  rw [det_apply]
  refine (natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro σ
  calc
    natDegree (Equiv.Perm.sign σ • ∏ i : n, M (σ i) i) ≤
        natDegree (∏ i : n, M (σ i) i) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
      · rw [hσ, one_smul]
      · rw [hσ, Units.neg_smul, one_smul, natDegree_neg]
    _ ≤ ∑ i : n, natDegree (M (σ i) i) :=
      natDegree_prod_le (Finset.univ : Finset n) fun i : n ↦ M (σ i) i
    _ ≤ Finset.univ.card • k := Finset.sum_le_card_nsmul _ _ k fun i _ ↦ hM (σ i) i
    _ = Fintype.card n * k := by simp

/-- Entrywise degree bounds imply the natural bounds on all coefficients of the characteristic
polynomial.  This is the converse direction of Hanselka's degree criterion used in item B1 of
[RealRooted issue #954](https://github.com/PerAlexandersson/RealRooted/issues/954). -/
theorem natDegree_charpoly_coeff_le_of_entry {R : Type*} [CommRing R] {d k : ℕ}
    (M : Matrix (Fin d) (Fin d) R[X]) (hM : ∀ i l, (M i l).natDegree ≤ k) :
    ∀ j < d, (M.charpoly.coeff j).natDegree ≤ k * (d - j) := by
  intro j hj
  have hcoeff := M.charpoly_coeff_eq_sum_minors (d - j) (by simp)
  rw [Fintype.card_fin, show d - (d - j) = j by lia] at hcoeff
  rw [hcoeff]
  have hsign : natDegree ((-1 : R[X]) ^ (d - j)) ≤ 0 := by
    simpa using natDegree_pow_le_of_le (p := (-1 : R[X])) (m := 0) (d - j)
      (by rw [natDegree_neg, natDegree_one])
  have hsum : natDegree (∑ s ∈ Finset.univ.powersetCard (d - j),
      (M.submatrix (Subtype.val : s → Fin d) (Subtype.val : s → Fin d)).det) ≤
      k * (d - j) := by
    refine natDegree_sum_le_of_forall_le _ _ ?_
    intro s hs
    have hcard : Fintype.card s = d - j := by
      simpa using (Finset.mem_powersetCard.mp hs).2
    refine (natDegree_det_le_of_entry_le _ k ?_).trans_eq ?_
    · intro i l
      exact hM i l
    · rw [hcard, mul_comm]
  calc
    natDegree ((-1) ^ (d - j) * ∑ s ∈ Finset.univ.powersetCard (d - j),
        (M.submatrix (Subtype.val : s → Fin d) (Subtype.val : s → Fin d)).det) ≤
        natDegree ((-1 : R[X]) ^ (d - j)) +
          natDegree (∑ s ∈ Finset.univ.powersetCard (d - j),
            (M.submatrix (Subtype.val : s → Fin d) (Subtype.val : s → Fin d)).det) :=
      natDegree_mul_le
    _ ≤ 0 + k * (d - j) := Nat.add_le_add hsign hsum
    _ = k * (d - j) := by simp

/-- For a symmetric matrix of real polynomials, entrywise degree at most `k` is equivalent to
degree at most `k (d - j)` for coefficient `j` of the characteristic polynomial.  This is item B1
of [RealRooted issue #954](https://github.com/PerAlexandersson/RealRooted/issues/954). -/
theorem natDegree_charpoly_coeff_le_iff_entry_le_of_isSymm {d k : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ[X]) (hM : M.IsSymm) :
    (∀ j < d, (M.charpoly.coeff j).natDegree ≤ k * (d - j)) ↔
      ∀ i l, (M i l).natDegree ≤ k := by
  constructor
  · exact M.natDegree_entry_le_of_isSymm_charpoly hM
  · exact M.natDegree_charpoly_coeff_le_of_entry

end Matrix

namespace LinearMap.BilinForm

/-- The matrix of a self-adjoint endomorphism is symmetric in a basis in which the bilinear form
has identity Gram matrix.  This is the general linear-algebra bridge used in item D1 of
[RealRooted issue #954](https://github.com/PerAlexandersson/RealRooted/issues/954). -/
theorem isSymm_toMatrix_of_isSelfAdjoint {R M n : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Fintype n] [DecidableEq n]
    (B : LinearMap.BilinForm R M) (b : Module.Basis n R M) (f : Module.End R M)
    (hB : B.toMatrix b = 1) (hf : B.IsSelfAdjoint f) :
    (LinearMap.toMatrix b b f).IsSymm := by
  have hpair : Matrix.IsAdjointPair (B.toMatrix b) (B.toMatrix b)
      (LinearMap.toMatrix b b f) (LinearMap.toMatrix b b f) := by
    rw [← isAdjointPair_toLinearMap₂ b b]
    simpa only [LinearMap.BilinForm.toMatrix, Matrix.toLinearMap₂_toMatrix₂,
      Matrix.toLin_toMatrix, LinearMap.IsSelfAdjoint] using hf
  rw [hB, Matrix.IsAdjointPair, mul_one, one_mul] at hpair
  exact hpair

end LinearMap.BilinForm

namespace Algebra

/-- Multiplication is self-adjoint for every scalar multiple of the trace form.  For the pairing
in Hanselka's trace-form construction, take the scalar to be the inverse of `c`. -/
theorem smul_traceForm_lmul_isSelfAdjoint {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (r : R) (a : S) :
    (r • traceForm R S).IsSelfAdjoint (lmul R S a) := by
  intro x y
  change r * trace R S ((a * x) * y) = r * trace R S (x * (a * y))
  congr 1
  ac_rfl

/-- In a basis orthonormal for a scaled trace form, the matrix of multiplication by any element
is symmetric.  This is the matrix-symmetry step in Hanselka's trace-form construction for item D1
of [RealRooted issue #954](https://github.com/PerAlexandersson/RealRooted/issues/954). -/
theorem leftMulMatrix_isSymm_of_smul_traceForm_toMatrix_eq_one
    {R S n : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Fintype n] [DecidableEq n] (b : Module.Basis n R S) (r : R)
    (h : (r • traceForm R S).toMatrix b = 1) (a : S) :
    (leftMulMatrix b a).IsSymm := by
  rw [leftMulMatrix_apply]
  exact LinearMap.BilinForm.isSymm_toMatrix_of_isSelfAdjoint
    (r • traceForm R S) b (lmul R S a) h (smul_traceForm_lmul_isSelfAdjoint r a)

end Algebra

namespace PowerBasis

/-- The matrix of multiplication by the generator has the generator's minimal polynomial as its
characteristic polynomial in any basis, not only the power basis.  This is the characteristic-
polynomial step in item D1 of
[RealRooted issue #954](https://github.com/PerAlexandersson/RealRooted/issues/954). -/
theorem charpoly_leftMulMatrix {R S n : Type*} [CommRing R] [Ring S] [Algebra R S]
    [Fintype n] [DecidableEq n] (pb : PowerBasis R S) (b : Module.Basis n R S) :
    (Algebra.leftMulMatrix b pb.gen).charpoly = minpoly R pb.gen := by
  let _ : Module.Free R S := Module.Free.of_basis b
  let _ : Module.Finite R S := Module.Finite.of_basis b
  calc
    (Algebra.leftMulMatrix b pb.gen).charpoly = (Algebra.lmul R S pb.gen).charpoly := by
      simpa only [Algebra.leftMulMatrix_apply] using
        LinearMap.charpoly_toMatrix (Algebra.lmul R S pb.gen) b
    _ = (Algebra.leftMulMatrix pb.basis pb.gen).charpoly := by
      simpa only [Algebra.leftMulMatrix_apply] using
        (LinearMap.charpoly_toMatrix (Algebra.lmul R S pb.gen) pb.basis).symm
    _ = minpoly R pb.gen := _root_.charpoly_leftMulMatrix pb

end PowerBasis
