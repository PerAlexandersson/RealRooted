import RealRooted.CauchyInterlacing.Submatrix
import RealRooted.Mathlib.Algebra.Polynomial.DividedDifference
import RealRooted.Mathlib.LinearAlgebra.Matrix.Charpoly.Submatrix
import RealRooted.Mathlib.LinearAlgebra.Matrix.AdjugateExpansion

/-!
# Finite spectral-product positivity

This file assembles the finite ingredients of the Micchelli--Willoughby
spectral-product argument.  The characteristic polynomial and characteristic
adjugate are first expressed using the checked ordered-eigenvalue API.  The
remaining entrywise argument is organized around divided differences and
principal-submatrix path expansions.
-/

open Matrix Polynomial

namespace RealRooted

namespace Matrix

/-- A diagonal entry of the characteristic adjugate is the characteristic
polynomial of the principal submatrix obtained by deleting that index.  This
is the length-zero-path case of the path/cofactor expansion. -/
theorem adjugate_charmatrix_apply_self {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (i : Fin (N + 1)) :
    adjugate (charmatrix A) i i =
      (A.submatrix i.succAbove i.succAbove).charpoly := by
  rw [adjugate_fin_succ_eq_det_submatrix]
  rw [charmatrix_submatrix_self A i.succAbove i.succAbove_right_injective]
  simp only [Matrix.charpoly]
  rw [show (-1 : ℝ[X]) ^ ((i : ℕ) + (i : ℕ)) = 1 by
    rw [← two_mul, Even.neg_one_pow (even_two_mul (i : ℕ))]]
  simp

/-- Take a scalar divided difference entrywise in a matrix of polynomials. -/
noncomputable def polynomialDividedDifference {m n : Type*}
    (k : ℕ) (v : Fin (k + 1) → ℝ) (P : Matrix m n ℝ[X]) : Matrix m n ℝ :=
  fun i j => Polynomial.dividedDifference k v (P i j)

@[simp]
theorem polynomialDividedDifference_apply {m n : Type*}
    (k : ℕ) (v : Fin (k + 1) → ℝ) (P : Matrix m n ℝ[X]) (i : m) (j : n) :
    polynomialDividedDifference k v P i j =
      Polynomial.dividedDifference k v (P i j) :=
  rfl

@[simp]
theorem polynomialDividedDifference_zero {m n : Type*}
    (k : ℕ) (v : Fin (k + 1) → ℝ) :
    polynomialDividedDifference k v (0 : Matrix m n ℝ[X]) = 0 := by
  ext i j
  simp [polynomialDividedDifference]

theorem polynomialDividedDifference_add {m n : Type*}
    (k : ℕ) (v : Fin (k + 1) → ℝ) (P Q : Matrix m n ℝ[X]) :
    polynomialDividedDifference k v (P + Q) =
      polynomialDividedDifference k v P + polynomialDividedDifference k v Q := by
  ext i j
  exact Polynomial.dividedDifference_add k v (P i j) (Q i j)

/-- A constant matrix can be pulled through an entrywise divided difference
on the left. -/
theorem polynomialDividedDifference_map_mul {m n p : Type*}
    [Fintype n] (k : ℕ) (v : Fin (k + 1) → ℝ)
    (B : Matrix m n ℝ) (P : Matrix n p ℝ[X]) :
    polynomialDividedDifference k v (B.map C * P) =
      B * polynomialDividedDifference k v P := by
  classical
  ext i j
  simp only [polynomialDividedDifference_apply, Matrix.mul_apply, Matrix.map_apply]
  rw [Polynomial.dividedDifference_finset_sum]
  apply Finset.sum_congr rfl
  intro x _
  simpa only [Polynomial.smul_eq_C_mul] using
    Polynomial.dividedDifference_smul k v (B i x) (P x j)

/-- Matrix form of the Newton quotient. -/
noncomputable def evalQuotientMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (roots : List ℝ) : Matrix n n ℝ[X] :=
  matPolyEquiv.symm (evalQuotient A roots)

@[simp]
theorem matPolyEquiv_evalQuotientMatrix {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (roots : List ℝ) :
    matPolyEquiv (evalQuotientMatrix A roots) = evalQuotient A roots :=
  AlgEquiv.apply_symm_apply _ _

@[simp]
theorem evalQuotientMatrix_nil {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : evalQuotientMatrix A [] = 0 := by
  apply matPolyEquiv.injective
  simp [evalQuotientMatrix, evalQuotient]

theorem evalQuotientMatrix_cons {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (r : ℝ) (roots : List ℝ) :
    evalQuotientMatrix A (r :: roots) =
      rootsProduct roots • (1 : Matrix n n ℝ[X]) +
        (A - r • 1).map C * evalQuotientMatrix A roots := by
  apply matPolyEquiv.injective
  simp only [evalQuotientMatrix, AlgEquiv.apply_symm_apply, evalQuotient, map_add,
    map_mul, matPolyEquiv_map_C, matPolyEquiv_smul_one]
  simp [Algebra.algebraMap_eq_smul_one]

private theorem rootsProduct_eq_fin_prod (roots : List ℝ) :
    rootsProduct roots = ∏ i : Fin roots.length, (X - C (roots.get i)) := by
  calc
    rootsProduct roots = (roots.map fun r => X - C r).prod := rootsProduct_eq_map_prod roots
    _ = ((List.ofFn roots.get).map fun r => X - C r).prod := by rw [List.ofFn_get]
    _ = (List.ofFn fun i : Fin roots.length => X - C (roots.get i)).prod := by
      rw [List.map_ofFn]
      rfl
    _ = ∏ i : Fin roots.length, (X - C (roots.get i)) := List.prod_ofFn

private theorem dividedDifference_rootsProduct_eq_zero_of_length_lt
    (k : ℕ) (v : Fin (k + 1) → ℝ) (hv : Function.Injective v)
    (roots : List ℝ) (hroots : roots.length < k) :
    Polynomial.dividedDifference k v (rootsProduct roots) = 0 := by
  rw [rootsProduct_eq_fin_prod]
  exact Polynomial.dividedDifference_prod_X_sub_C_eq_zero_of_lt
    (fun i : Fin roots.length => roots.get i) v hv hroots

private theorem dividedDifference_rootsProduct_eq_one_of_length_eq
    (k : ℕ) (v : Fin (k + 1) → ℝ) (hv : Function.Injective v)
    (roots : List ℝ) (hroots : roots.length = k) :
    Polynomial.dividedDifference k v (rootsProduct roots) = 1 := by
  subst k
  rw [rootsProduct_eq_fin_prod]
  exact Polynomial.dividedDifference_prod_X_sub_C_eq_one _ _ hv

private theorem eval_rootsProduct_eq_zero_of_mem (x : ℝ) :
    ∀ {roots : List ℝ}, x ∈ roots → (rootsProduct roots).eval x = 0 := by
  intro roots hx
  induction roots with
  | nil => simp at hx
  | cons r roots ih =>
      rw [rootsProduct, eval_mul]
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · rw [ih hx, mul_zero]

private theorem polynomialDividedDifference_rootsProduct_smul_one
    {n : Type*} [DecidableEq n]
    (k : ℕ) (v : Fin (k + 1) → ℝ) (roots : List ℝ) :
    polynomialDividedDifference k v
        (rootsProduct roots • (1 : Matrix n n ℝ[X])) =
      Polynomial.dividedDifference k v (rootsProduct roots) • 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [polynomialDividedDifference]
  · simp [polynomialDividedDifference, hij]

/-- A Newton quotient with at most `k` roots has vanishing divided difference
of order `k`. -/
theorem polynomialDividedDifference_evalQuotientMatrix_eq_zero_of_length_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (k : ℕ) (v : Fin (k + 1) → ℝ) (hv : Function.Injective v)
    (A : Matrix n n ℝ) (roots : List ℝ) (hroots : roots.length ≤ k) :
    polynomialDividedDifference k v (evalQuotientMatrix A roots) = 0 := by
  induction roots with
  | nil => simp
  | cons r roots ih =>
      rw [evalQuotientMatrix_cons, polynomialDividedDifference_add,
        polynomialDividedDifference_rootsProduct_smul_one,
        polynomialDividedDifference_map_mul]
      rw [dividedDifference_rootsProduct_eq_zero_of_length_lt k v hv roots (by simpa using hroots)]
      rw [ih (Nat.le_trans (Nat.le_succ roots.length) hroots)]
      simp

/-- The top divided difference of the Newton quotient at the same ordered
nodes is the identity matrix. -/
theorem polynomialDividedDifference_evalQuotientMatrix_ofFn
    {n : Type*} [Fintype n] [DecidableEq n]
    (k : ℕ) (v : Fin (k + 1) → ℝ) (hv : Function.Injective v)
    (A : Matrix n n ℝ) :
    polynomialDividedDifference k v
        (evalQuotientMatrix A (List.ofFn v)) = 1 := by
  rw [List.ofFn_succ, evalQuotientMatrix_cons, polynomialDividedDifference_add,
    polynomialDividedDifference_rootsProduct_smul_one,
    polynomialDividedDifference_map_mul]
  rw [dividedDifference_rootsProduct_eq_one_of_length_eq k v hv _ (by simp)]
  rw [polynomialDividedDifference_evalQuotientMatrix_eq_zero_of_length_le
    k v hv A _ (by simp)]
  simp

/-- Dividing the Newton quotient at a terminal block of nodes returns the
matrix polynomial belonging to the preceding roots. -/
theorem polynomialDividedDifference_evalQuotientMatrix_append_ofFn
    {n : Type*} [Fintype n] [DecidableEq n]
    (k : ℕ) (v : Fin (k + 1) → ℝ) (hv : Function.Injective v)
    (A : Matrix n n ℝ) (initialRoots : List ℝ) :
    polynomialDividedDifference k v
        (evalQuotientMatrix A (initialRoots ++ List.ofFn v)) =
      aeval A (rootsProduct initialRoots) := by
  induction initialRoots with
  | nil =>
      simpa [rootsProduct] using
        polynomialDividedDifference_evalQuotientMatrix_ofFn k v hv A
  | cons r initialRoots ih =>
      rw [List.cons_append, evalQuotientMatrix_cons,
        polynomialDividedDifference_add,
        polynomialDividedDifference_rootsProduct_smul_one,
        polynomialDividedDifference_map_mul]
      have hzero : Polynomial.dividedDifference k v
          (rootsProduct (initialRoots ++ List.ofFn v)) = 0 := by
        apply Polynomial.dividedDifference_eq_zero_of_eval_eq_zero
        intro i
        apply eval_rootsProduct_eq_zero_of_mem
        apply List.mem_append.mpr
        exact Or.inr (List.mem_ofFn.mpr ⟨i, rfl⟩)
      rw [hzero, ih]
      simp only [zero_smul, zero_add, rootsProduct, aeval_mul, aeval_sub,
        aeval_X, aeval_C]
      simp [Algebra.algebraMap_eq_smul_one]

theorem aeval_rootsProduct {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (roots : List ℝ) :
    aeval A (rootsProduct roots) =
      (roots.map fun r => A - r • 1).prod := by
  induction roots with
  | nil => simp [rootsProduct]
  | cons r roots ih =>
      rw [rootsProduct, aeval_mul, ih]
      simp [Algebra.algebraMap_eq_smul_one]

/-- Algebraic identification of the adjugate tail divided difference with the
preceding ordered spectral product. -/
theorem polynomialDividedDifference_adjugate_charmatrix
    {n : Type*} [Fintype n] [DecidableEq n]
    (k : ℕ) (v : Fin (k + 1) → ℝ) (hv : Function.Injective v)
    (A : Matrix n n ℝ) (initialRoots : List ℝ)
    (hchar : A.charpoly = rootsProduct (initialRoots ++ List.ofFn v)) :
    polynomialDividedDifference k v (adjugate (charmatrix A)) =
      (initialRoots.map fun r => A - r • 1).prod := by
  have hadj : adjugate (charmatrix A) =
      evalQuotientMatrix A (initialRoots ++ List.ofFn v) := by
    apply matPolyEquiv.injective
    rw [matPolyEquiv_adjugate_charmatrix_eq_evalQuotient A _ hchar]
    exact (matPolyEquiv_evalQuotientMatrix A _).symm
  rw [hadj]
  rw [polynomialDividedDifference_evalQuotientMatrix_append_ofFn k v hv A initialRoots,
    aeval_rootsProduct]

end Matrix

/-- The characteristic polynomial of a real symmetric matrix is the ordered
product of its decreasing eigenvalues. -/
theorem charpoly_eq_rootsProduct_sortedEigenvalues {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    A.charpoly = rootsProduct (List.ofFn fun k : Fin N => sortedEigenvalues A hA k) := by
  have hroots :
      (↑(List.ofFn fun k : Fin N => sortedEigenvalues A hA k) : Multiset ℝ) =
        A.charpoly.roots := by
    rw [sortedEigenvalues_charpoly_roots A hA, ← Fin.univ_val_map]
    rfl
  have hsplits : A.charpoly.Splits := hA.splits_charpoly
  rw [hsplits.eq_prod_roots_of_monic A.charpoly_monic, ← hroots]
  exact (rootsProduct_eq_map_prod _).symm

/-- The characteristic adjugate of a real symmetric matrix is its finite
Newton quotient expanded along the ordered eigenvalues. -/
theorem matPolyEquiv_adjugate_charmatrix_eq_sortedEigenvalueQuotient {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    matPolyEquiv (adjugate (charmatrix A)) =
      evalQuotient A (List.ofFn fun k : Fin N => sortedEigenvalues A hA k) :=
  matPolyEquiv_adjugate_charmatrix_eq_evalQuotient A _
    (charpoly_eq_rootsProduct_sortedEigenvalues A hA)

/-- Matrix-of-polynomials form of the checked characteristic-adjugate Newton
expansion. -/
theorem adjugate_charmatrix_eq_sortedEigenvalueQuotient {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    adjugate (charmatrix A) =
      Matrix.evalQuotientMatrix A
        (List.ofFn fun k : Fin N => sortedEigenvalues A hA k) := by
  apply matPolyEquiv.injective
  rw [matPolyEquiv_adjugate_charmatrix_eq_sortedEigenvalueQuotient]
  exact (Matrix.matPolyEquiv_evalQuotientMatrix A _).symm

end RealRooted
