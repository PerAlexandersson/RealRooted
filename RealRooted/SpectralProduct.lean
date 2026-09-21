import RealRooted.CauchyInterlacing.Submatrix
import RealRooted.Mathlib.Algebra.Polynomial.DividedDifference
import RealRooted.Mathlib.LinearAlgebra.Matrix.Charpoly.Submatrix
import RealRooted.Mathlib.LinearAlgebra.Matrix.AdjugateExpansion
import RealRooted.Mathlib.LinearAlgebra.Matrix.AdjugatePath

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

/-- Recursive simple-path positivity for a characteristic adjugate.  It is
enough that every diagonal leaf reached after any sequence of principal
deletions has nonnegative divided difference.  The off-diagonal recursion
deletes its initial vertex, so its iterates enumerate only simple paths. -/
theorem dividedDifference_adjugate_charmatrix_apply_nonneg_of_principal :
    ∀ {N r : ℕ} (v : Fin (r + 1) → ℝ)
      (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
      (∀ i j, 0 ≤ A i j) →
      (∀ {d : ℕ} (f : Fin (d + 1) → Fin (N + 1)),
        Function.Injective f → ∀ i : Fin (d + 1),
          0 ≤ Polynomial.dividedDifference r v
            ((A.submatrix f f).submatrix i.succAbove i.succAbove).charpoly) →
      ∀ i j,
        0 ≤ Polynomial.dividedDifference r v
          (adjugate A.charmatrix i j) := by
  intro N
  induction N with
  | zero =>
      intro r v A _ hprincipal i j
      have hi : i = 0 := Fin.eq_zero i
      have hj : j = 0 := Fin.eq_zero j
      subst i
      subst j
      rw [adjugate_charmatrix_apply_self]
      simpa [Function.comp_def] using
        hprincipal (fun x => x) Function.injective_id (0 : Fin 1)
  | succ N ih =>
      intro r v A hA hprincipal i j
      by_cases hij : i = j
      · subst j
        rw [adjugate_charmatrix_apply_self]
        simpa [Function.comp_def] using
          hprincipal (fun x => x) Function.injective_id i
      · obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
        rw [← hj']
        rw [adjugate_charmatrix_apply_succAbove]
        rw [Polynomial.dividedDifference_finset_sum]
        apply Finset.sum_nonneg
        intro k _
        rw [← Polynomial.smul_eq_C_mul,
          Polynomial.dividedDifference_smul]
        apply mul_nonneg (hA i (i.succAbove k))
        apply ih v (A.submatrix i.succAbove i.succAbove)
        · intro a b
          exact hA _ _
        · intro d f hf a
          let g : Fin (d + 1) → Fin (N + 2) := i.succAbove ∘ f
          have hg : Function.Injective g := i.succAbove_right_injective.comp hf
          have hleaf := hprincipal g hg a
          simpa only [g, Matrix.submatrix_submatrix, Function.comp_assoc] using hleaf

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

/-- Eigenvalues of a Hermitian matrix in increasing order. -/
noncomputable def increasingEigenvalues {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) : Fin N → ℝ :=
  fun k => sortedEigenvalues A hA k.rev

theorem increasingEigenvalues_monotone {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    Monotone (increasingEigenvalues A hA) := by
  intro i j hij
  exact sortedEigenvalues_antitone A hA (Fin.rev_le_rev.2 hij)

/-- A simple spectrum, expressed as strict decrease of the existing sorted
eigenvalues, gives strict increase in the reversed indexing. -/
theorem increasingEigenvalues_strictMono {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian)
    (hsimple : StrictAnti (sortedEigenvalues A hA)) :
    StrictMono (increasingEigenvalues A hA) := by
  intro i j hij
  exact hsimple (Fin.rev_strictAnti hij)

/-- Increasing-order form of the arbitrary principal-submatrix eigenvalue
bound: deleting `N - d` coordinates shifts the comparison by that amount. -/
theorem increasingEigenvalues_submatrix_le {d N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian)
    (f : Fin d → Fin N) (hf : Function.Injective f) (k : Fin d) :
    increasingEigenvalues (A.submatrix f f) (hA.submatrix f) k ≤
      increasingEigenvalues A hA
        ⟨N - d + (k : ℕ), by
          have hdN : d ≤ N := by
            simpa using Fintype.card_le_of_injective f hf
          lia⟩ := by
  have hdN : d ≤ N := by
    simpa using Fintype.card_le_of_injective f hf
  have h := sortedEigenvalues_submatrix_le A hA f hf k.rev
  have hidx : Fin.castLE hdN k.rev =
      (⟨N - d + (k : ℕ), by lia⟩ : Fin N).rev := by
    ext
    simp
    lia
  simpa [increasingEigenvalues, hidx] using h

/-- The terminal block of an increasing `Fin (N+1)`-tuple beginning at `k`.
Its length is `N - k + 1`. -/
noncomputable def spectralTailNodes {N : ℕ} (μ : Fin (N + 1) → ℝ)
    (k : Fin (N + 1)) : Fin (N - (k : ℕ) + 1) → ℝ :=
  fun i => μ ⟨(k : ℕ) + (i : ℕ), by lia⟩

/-- The initial block strictly before `k` in a `Fin (N+1)`-tuple. -/
noncomputable def spectralInitialRoots {N : ℕ} (μ : Fin (N + 1) → ℝ)
    (k : Fin (N + 1)) : List ℝ :=
  List.ofFn fun i : Fin (k : ℕ) => μ ⟨i, i.isLt.trans k.isLt⟩

theorem spectralInitialRoots_append_tail {N : ℕ}
    (μ : Fin (N + 1) → ℝ) (k : Fin (N + 1)) :
    spectralInitialRoots μ k ++ List.ofFn (spectralTailNodes μ k) =
      List.ofFn μ := by
  have hsize : (k : ℕ) + (N - (k : ℕ) + 1) = N + 1 := by lia
  let a : Fin (k : ℕ) → ℝ :=
    fun i => μ ⟨i, i.isLt.trans k.isLt⟩
  let b : Fin (N - (k : ℕ) + 1) → ℝ := spectralTailNodes μ k
  have hfun : Fin.append a b = μ ∘ Fin.cast hsize := by
    funext x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) x
    · simp only [Fin.append_left, Function.comp_apply, a]
      congr 1
    · simp only [Fin.append_right, Function.comp_apply, b, spectralTailNodes]
      congr 1
  calc
    spectralInitialRoots μ k ++ List.ofFn (spectralTailNodes μ k) =
        List.ofFn (Fin.append a b) := by
          rw [List.ofFn_fin_append]
          rfl
    _ = List.ofFn (μ ∘ Fin.cast hsize) := congrArg List.ofFn hfun
    _ = List.ofFn μ := by
      simpa [Function.comp_def] using
        (List.ofFn_congr hsize (μ ∘ Fin.cast hsize))

theorem spectralTailNodes_strictMono {N : ℕ} {μ : Fin (N + 1) → ℝ}
    (hμ : StrictMono μ) (k : Fin (N + 1)) :
    StrictMono (spectralTailNodes μ k) := by
  intro i j hij
  apply hμ
  change (k : ℕ) + (i : ℕ) < (k : ℕ) + (j : ℕ)
  lia

/-- The characteristic polynomial factored using increasing eigenvalue order. -/
theorem charpoly_eq_rootsProduct_increasingEigenvalues {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) :
    A.charpoly = rootsProduct
      (List.ofFn fun k : Fin N => increasingEigenvalues A hA k) := by
  have hroots :
      (↑(List.ofFn fun k : Fin N => increasingEigenvalues A hA k) : Multiset ℝ) =
        A.charpoly.roots := by
    rw [sortedEigenvalues_charpoly_roots A hA, ← Fin.univ_val_map]
    conv_rhs =>
      rw [← Finset.map_univ_equiv (Fin.revPerm (n := N)), Finset.map_val,
        Multiset.map_map]
    rfl
  have hsplits : A.charpoly.Splits := hA.splits_charpoly
  rw [hsplits.eq_prod_roots_of_monic A.charpoly_monic, ← hroots]
  exact (rootsProduct_eq_map_prod _).symm

/-- Every principal-submatrix characteristic polynomial has nonnegative
divided difference on a terminal block of a simple full spectrum.  This is the
scalar leaf estimate in the simple-path expansion. -/
theorem dividedDifference_principalSubmatrix_charpoly_nonneg {N d : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hA : A.IsHermitian)
    (hsimple : StrictAnti (sortedEigenvalues A hA))
    (k : Fin (N + 1)) (f : Fin d → Fin (N + 1))
    (hf : Function.Injective f) :
    0 ≤ Polynomial.dividedDifference (N - (k : ℕ))
      (spectralTailNodes (increasingEigenvalues A hA) k)
      (A.submatrix f f).charpoly := by
  let B := A.submatrix f f
  let hB : B.IsHermitian := hA.submatrix f
  let ν := increasingEigenvalues B hB
  let v := spectralTailNodes (increasingEigenvalues A hA) k
  let r := N - (k : ℕ)
  have hv : StrictMono v :=
    spectralTailNodes_strictMono (increasingEigenvalues_strictMono A hA hsimple) k
  have hchar : B.charpoly = rootsProduct (List.ofFn ν) :=
    charpoly_eq_rootsProduct_increasingEigenvalues B hB
  rw [show A.submatrix f f = B from rfl, hchar, rootsProduct_eq_map_prod,
    List.map_ofFn, List.prod_ofFn]
  change 0 ≤ Polynomial.dividedDifference r v (∏ i, (X - C (ν i)))
  rcases lt_trichotomy d r with hdr | hdr | hdr
  · rw [Polynomial.dividedDifference_prod_X_sub_C_eq_zero_of_lt ν v hv.injective hdr]
  · subst d
    rw [Polynomial.dividedDifference_prod_X_sub_C_eq_one ν v hv.injective]
    norm_num
  · let b := d - r - 1
    have hcard : d = b + r + 1 := by
      dsimp only [b]
      lia
    apply Polynomial.dividedDifference_prod_fin_X_sub_C_nonneg_of_card
      r b ν v hcard (increasingEigenvalues_monotone B hB) hv
    intro i
    have hroot : b + (i : ℕ) < d := by
      rw [hcard]
      lia
    have hbound := increasingEigenvalues_submatrix_le A hA f hf
      (⟨b + (i : ℕ), hroot⟩ : Fin d)
    have hdN : d ≤ N + 1 := by
      simpa using Fintype.card_le_of_injective f hf
    have hkN : (k : ℕ) ≤ N := Nat.le_of_lt_succ k.isLt
    have hindex :
        (⟨N + 1 - d + (b + (i : ℕ)), by
          lia⟩ : Fin (N + 1)) =
          ⟨(k : ℕ) + (i : ℕ), by lia⟩ := by
      ext
      dsimp only [b, r]
      lia
    simpa only [ν, v, spectralTailNodes, hindex] using hbound

/-- Entrywise nonnegativity of the terminal divided difference of the
characteristic adjugate.  The proof combines the recursive simple-path
expansion with the principal-submatrix leaf estimate above. -/
theorem polynomialDividedDifference_adjugate_charmatrix_nonneg {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hA : A.IsHermitian)
    (hentry : ∀ i j, 0 ≤ A i j)
    (hsimple : StrictAnti (sortedEigenvalues A hA))
    (k : Fin (N + 1)) :
    ∀ i j, 0 ≤ Matrix.polynomialDividedDifference (N - (k : ℕ))
      (spectralTailNodes (increasingEigenvalues A hA) k)
      (adjugate A.charmatrix) i j := by
  intro i j
  change 0 ≤ Polynomial.dividedDifference (N - (k : ℕ))
    (spectralTailNodes (increasingEigenvalues A hA) k)
    (adjugate A.charmatrix i j)
  apply Matrix.dividedDifference_adjugate_charmatrix_apply_nonneg_of_principal
    (A := A) _ hentry
  intro d f hf a
  let g : Fin d → Fin (N + 1) := f ∘ a.succAbove
  have hg : Function.Injective g := hf.comp a.succAbove_right_injective
  have hleaf := dividedDifference_principalSubmatrix_charpoly_nonneg
    A hA hsimple k g hg
  simpa only [g, Matrix.submatrix_submatrix, Function.comp_assoc] using hleaf

/-- The terminal adjugate divided difference is exactly the product of the
preceding increasing-eigenvalue factors. -/
theorem polynomialDividedDifference_adjugate_charmatrix_eq_spectralProduct
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsHermitian) (hsimple : StrictAnti (sortedEigenvalues A hA))
    (k : Fin (N + 1)) :
    Matrix.polynomialDividedDifference (N - (k : ℕ))
      (spectralTailNodes (increasingEigenvalues A hA) k)
      (adjugate A.charmatrix) =
        (spectralInitialRoots (increasingEigenvalues A hA) k |>.map
          fun r => A - r • 1).prod := by
  apply Matrix.polynomialDividedDifference_adjugate_charmatrix
  · exact (spectralTailNodes_strictMono
      (increasingEigenvalues_strictMono A hA hsimple) k).injective
  · rw [spectralInitialRoots_append_tail]
    exact charpoly_eq_rootsProduct_increasingEigenvalues A hA

/-- Finite Micchelli--Willoughby spectral-product positivity.  For a symmetric
entrywise nonnegative matrix with simple spectrum, every entry of the product
of the factors preceding `k` in increasing eigenvalue order is nonnegative.
The case `k = 0` is included and gives the identity matrix. -/
theorem spectralProduct_entrywise_nonneg {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hA : A.IsHermitian)
    (hentry : ∀ i j, 0 ≤ A i j)
    (hsimple : StrictAnti (sortedEigenvalues A hA))
    (k : Fin (N + 1)) :
    ∀ i j, 0 ≤
      ((spectralInitialRoots (increasingEigenvalues A hA) k |>.map
        fun r => A - r • 1).prod) i j := by
  intro i j
  rw [← polynomialDividedDifference_adjugate_charmatrix_eq_spectralProduct
    A hA hsimple k]
  exact polynomialDividedDifference_adjugate_charmatrix_nonneg
    A hA hentry hsimple k i j

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
