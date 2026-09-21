import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Boolean orbits of squarefree monomials

This file supplies the algebraic finite-set monomial API used to factor
Boolean orbits under disjoint variable transpositions.
-/

open scoped BigOperators

namespace MvPolynomial

/-- The squarefree monomial supported on a finite set of variables. -/
noncomputable def finsetMonomial {σ R : Type*} [CommSemiring R] (A : Finset σ) :
    MvPolynomial σ R :=
  ∏ z ∈ A, X z

@[simp] theorem finsetMonomial_empty {σ R : Type*} [CommSemiring R] :
    finsetMonomial (∅ : Finset σ) = (1 : MvPolynomial σ R) := by
  simp [finsetMonomial]

@[simp] theorem finsetMonomial_insert {σ R : Type*} [CommSemiring R]
    [DecidableEq σ]
    {A : Finset σ} {z : σ} (hz : z ∉ A) :
    finsetMonomial (insert z A) =
      (X z : MvPolynomial σ R) * finsetMonomial A := by
  simp [finsetMonomial, hz]

/-- Injectively renaming a squarefree finite-set monomial maps its support. -/
theorem rename_finsetMonomial {σ τ R : Type*} [CommSemiring R]
    (f : σ → τ) (hf : Function.Injective f) (A : Finset σ) :
    rename f (finsetMonomial A : MvPolynomial σ R) =
      finsetMonomial (A.map ⟨f, hf⟩) := by
  simp [finsetMonomial, map_prod, rename_X]

/-- The support obtained by swapping two variables. -/
def swapFinset {σ : Type*} [DecidableEq σ]
    (x y : σ) (A : Finset σ) : Finset σ :=
  A.map (Equiv.swap x y).toEmbedding

/-- Renaming a finite-set monomial by a transposition swaps its support. -/
theorem rename_swap_finsetMonomial {σ R : Type*} [CommSemiring R]
    [DecidableEq σ]
    (x y : σ) (A : Finset σ) :
    rename (Equiv.swap x y) (finsetMonomial A : MvPolynomial σ R) =
      finsetMonomial (swapFinset x y A) := by
  exact rename_finsetMonomial (Equiv.swap x y) (Equiv.swap x y).injective A

/-- A swap fixes a support containing neither endpoint. -/
theorem swapFinset_eq_self_of_not_mem {σ : Type*} [DecidableEq σ]
    (A : Finset σ) (x y : σ) (hx : x ∉ A) (hy : y ∉ A) :
    swapFinset x y A = A := by
  ext z
  simp only [swapFinset, Finset.mem_map_equiv, Equiv.symm_swap]
  by_cases hzx : z = x
  · subst z
    simp [hx, hy]
  · by_cases hzy : z = y
    · subst z
      simp [hx, hy]
    · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]

/-- A swap fixes a support containing both endpoints. -/
theorem swapFinset_eq_self_of_mem {σ : Type*} [DecidableEq σ]
    (A : Finset σ) (x y : σ) (hx : x ∈ A) (hy : y ∈ A) :
    swapFinset x y A = A := by
  ext z
  simp only [swapFinset, Finset.mem_map_equiv, Equiv.symm_swap]
  by_cases hzx : z = x
  · subst z
    simp [hx, hy]
  · by_cases hzy : z = y
    · subst z
      simp [hx, hy]
    · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]

/-- If a support contains only the left endpoint, swapping replaces it by the
right endpoint. -/
theorem swapFinset_eq_insert_erase_of_mem_not_mem
    {σ : Type*} [DecidableEq σ] (A : Finset σ) (x y : σ)
    (hxy : x ≠ y) (hx : x ∈ A) (hy : y ∉ A) :
    swapFinset x y A = insert y (A.erase x) := by
  ext z
  simp only [swapFinset, Finset.mem_map_equiv, Equiv.symm_swap,
    Finset.mem_insert, Finset.mem_erase]
  by_cases hzx : z = x
  · subst z
    simp [hxy, hx, hy]
  · by_cases hzy : z = y
    · subst z
      simp [hx, hy]
    · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
      simp [hzx, hzy]

/-- If a support contains only the right endpoint, swapping replaces it by
the left endpoint. -/
theorem swapFinset_eq_insert_erase_of_not_mem_mem
    {σ : Type*} [DecidableEq σ] (A : Finset σ) (x y : σ)
    (hxy : x ≠ y) (hx : x ∉ A) (hy : y ∈ A) :
    swapFinset x y A = insert x (A.erase y) := by
  simpa [swapFinset, Equiv.swap_comm] using
    swapFinset_eq_insert_erase_of_mem_not_mem A y x hxy.symm hy hx

/-- Add a polynomial to the result of swapping two variables. -/
noncomputable def swapSum {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    (x y : σ) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  P + rename (Equiv.swap x y) P

/-- A support fixed by a swap contributes a scalar factor two to its orbit. -/
theorem swapSum_finsetMonomial_eq_two_mul_of_swapFinset_eq
    {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    (A : Finset σ) (x y : σ) (hA : swapFinset x y A = A) :
    swapSum x y (finsetMonomial A : MvPolynomial σ R) =
      2 * finsetMonomial A := by
  rw [swapSum, rename_swap_finsetMonomial, hA]
  exact (two_mul (finsetMonomial A : MvPolynomial σ R)).symm

/-- When exactly the left endpoint occurs, the two-element swap orbit has a
linear factor `X x + X y`. -/
theorem swapSum_finsetMonomial_eq_X_add_X_mul_of_mem_not_mem
    {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    (A : Finset σ) (x y : σ) (hxy : x ≠ y)
    (hx : x ∈ A) (hy : y ∉ A) :
    swapSum x y (finsetMonomial A : MvPolynomial σ R) =
      (X x + X y) * finsetMonomial (A.erase x) := by
  have hxErase : x ∉ A.erase x := by simp
  have hyErase : y ∉ A.erase x := fun hyMem => hy (Finset.mem_of_mem_erase hyMem)
  have hbase : (finsetMonomial A : MvPolynomial σ R) =
      X x * finsetMonomial (A.erase x) := by
    rw [← finsetMonomial_insert hxErase, Finset.insert_erase hx]
  rw [swapSum, rename_swap_finsetMonomial,
    swapFinset_eq_insert_erase_of_mem_not_mem A x y hxy hx hy,
    finsetMonomial_insert hyErase, hbase, add_mul]

/-- The corresponding factorization when exactly the right endpoint occurs. -/
theorem swapSum_finsetMonomial_eq_X_add_X_mul_of_not_mem_mem
    {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    (A : Finset σ) (x y : σ) (hxy : x ≠ y)
    (hx : x ∉ A) (hy : y ∈ A) :
    swapSum x y (finsetMonomial A : MvPolynomial σ R) =
      (X x + X y) * finsetMonomial (A.erase y) := by
  rw [show swapSum x y (finsetMonomial A : MvPolynomial σ R) =
      swapSum y x (finsetMonomial A) by simp [swapSum, Equiv.swap_comm]]
  simpa [add_comm] using
    swapSum_finsetMonomial_eq_X_add_X_mul_of_mem_not_mem
      A y x hxy.symm hy hx

/-- The factor contributed by one nondegenerate Boolean variable swap. -/
noncomputable def swapKernel {σ R : Type*} [CommSemiring R]
    [DecidableEq σ] (x y : σ) (A : Finset σ) : MvPolynomial σ R :=
  if x ∈ A then
    if y ∈ A then 2 * (X x * X y) else X x + X y
  else if y ∈ A then X x + X y else 2

/-- When neither endpoint occurs, the swap orbit contributes only a scalar
factor two. -/
theorem swapSum_finsetMonomial_of_not_mem_not_mem
    {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    (A : Finset σ) (x y : σ) (hx : x ∉ A) (hy : y ∉ A) :
    swapSum x y (finsetMonomial A : MvPolynomial σ R) =
      2 * finsetMonomial (A \ {x, y}) := by
  have hdiff : A \ ({x, y} : Finset σ) = A := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact And.left
    · intro hz
      exact ⟨hz, by rintro (rfl | rfl) <;> contradiction⟩
  rw [hdiff]
  exact swapSum_finsetMonomial_eq_two_mul_of_swapFinset_eq A x y
    (swapFinset_eq_self_of_not_mem A x y hx hy)

/-- When both distinct endpoints occur, the swap orbit contributes both
variables and a scalar factor two. -/
theorem swapSum_finsetMonomial_of_mem_mem
    {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    (A : Finset σ) (x y : σ) (hxy : x ≠ y)
    (hx : x ∈ A) (hy : y ∈ A) :
    swapSum x y (finsetMonomial A : MvPolynomial σ R) =
      2 * (finsetMonomial (A \ {x, y}) * (X x * X y)) := by
  let B : Finset σ := A \ {x, y}
  have hxB : x ∉ B := by simp [B]
  have hyB : y ∉ B := by simp [B]
  have hxInsert : x ∉ insert y B := by simp [hxy, hxB]
  have hA : A = insert x (insert y B) := by
    ext z
    simp only [B, Finset.mem_insert, Finset.mem_sdiff,
      Finset.mem_singleton]
    constructor
    · intro hz
      by_cases hzx : z = x
      · exact Or.inl hzx
      · by_cases hzy : z = y
        · exact Or.inr (Or.inl hzy)
        · exact Or.inr (Or.inr ⟨hz, by simp [hzx, hzy]⟩)
    · rintro (rfl | rfl | ⟨hz, _⟩)
      · exact hx
      · exact hy
      · exact hz
  have hmonomial : (finsetMonomial A : MvPolynomial σ R) =
      X x * (X y * finsetMonomial B) := by
    rw [hA, finsetMonomial_insert hxInsert, finsetMonomial_insert hyB]
  rw [swapSum_finsetMonomial_eq_two_mul_of_swapFinset_eq A x y
    (swapFinset_eq_self_of_mem A x y hx hy), hmonomial]
  simp only [B, mul_assoc, mul_left_comm, mul_comm]

/-- When only the left endpoint occurs, the remaining support factors from
the linear swap kernel. -/
theorem swapSum_finsetMonomial_of_mem_not_mem
    {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    (A : Finset σ) (x y : σ) (hxy : x ≠ y)
    (hx : x ∈ A) (hy : y ∉ A) :
    swapSum x y (finsetMonomial A : MvPolynomial σ R) =
      finsetMonomial (A \ {x, y}) * (X x + X y) := by
  have herase : A.erase x = A \ ({x, y} : Finset σ) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hzx, hzA⟩
      exact ⟨hzA, by
        rintro (rfl | rfl)
        · exact hzx rfl
        · exact hy hzA⟩
    · rintro ⟨hzA, hz⟩
      exact ⟨fun hzx => hz (Or.inl hzx), hzA⟩
  rw [swapSum_finsetMonomial_eq_X_add_X_mul_of_mem_not_mem
    A x y hxy hx hy, herase, mul_comm]

/-- The analogous factorization when only the right endpoint occurs. -/
theorem swapSum_finsetMonomial_of_not_mem_mem
    {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    (A : Finset σ) (x y : σ) (hxy : x ≠ y)
    (hx : x ∉ A) (hy : y ∈ A) :
    swapSum x y (finsetMonomial A : MvPolynomial σ R) =
      finsetMonomial (A \ {x, y}) * (X x + X y) := by
  rw [show A \ ({x, y} : Finset σ) = A \ ({y, x} : Finset σ) by
    simp [Finset.pair_comm]]
  simpa [swapSum, Equiv.swap_comm, add_comm] using
    swapSum_finsetMonomial_of_mem_not_mem A y x hxy.symm hy hx

/-- A squarefree monomial plus its renaming by a nondegenerate swap factors
through the untouched support and the corresponding swap kernel. -/
theorem swapSum_finsetMonomial
    {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    (A : Finset σ) (x y : σ) (hxy : x ≠ y) :
    swapSum x y (finsetMonomial A : MvPolynomial σ R) =
      finsetMonomial (A \ {x, y}) * swapKernel x y A := by
  by_cases hx : x ∈ A
  · by_cases hy : y ∈ A
    · rw [swapSum_finsetMonomial_of_mem_mem A x y hxy hx hy,
        swapKernel, ite_eq_left hx, ite_eq_left hy]
      simp only [mul_assoc, mul_left_comm, mul_comm]
    · rw [swapSum_finsetMonomial_of_mem_not_mem A x y hxy hx hy,
        swapKernel, ite_eq_left hx, ite_eq_right hy]
  · by_cases hy : y ∈ A
    · rw [swapSum_finsetMonomial_of_not_mem_mem A x y hxy hx hy,
        swapKernel, ite_eq_right hx, ite_eq_left hy]
    · rw [swapSum_finsetMonomial_of_not_mem_not_mem A x y hx hy,
        swapKernel, ite_eq_right hx, ite_eq_right hy]
      simp only [mul_comm]

end MvPolynomial
