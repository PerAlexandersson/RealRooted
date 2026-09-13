import RealRooted.BrandenLeite.ChainPolynomial.Algebra
import RealRooted.BrandenLeite.KernelRow
import RealRooted.BrandenLeite.SourceBorder

/-!
# Kernel rows of finite source borders

We identify the chain polynomials of a finite source-border matrix with a
regularized kernel construction.  The regularization removes the diagonal of
the lower-right block entrywise, avoiding subtraction and division.
-/

open Polynomial BigOperators

namespace Matrix

noncomputable section

/-- Extend a finite square matrix by zero to a matrix indexed by natural
numbers. -/
def toLowerTriangularMatrix {R : Type*} [Zero R] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) R) : RealRooted.LowerTriangularMatrix R :=
  fun i j =>
    if hi : i < N then
      if hj : j < N then A ⟨i, hi⟩ ⟨j, hj⟩ else 0
    else 0

@[simp]
theorem toLowerTriangularMatrix_apply_of_lt
    {R : Type*} [Zero R] {N i j : ℕ}
    (A : Matrix (Fin N) (Fin N) R) (hi : i < N) (hj : j < N) :
    toLowerTriangularMatrix A i j = A ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [toLowerTriangularMatrix, hi, hj]

/-- Regard an index strictly below `i` as an index of the same ambient finite
type as `i`. -/
def castBelow {N : ℕ} (i : Fin (N + 1)) (j : Fin i.val) : Fin (N + 1) :=
  ⟨j.val, j.isLt.trans i.isLt⟩

@[simp]
theorem castBelow_val {N : ℕ} (i : Fin (N + 1)) (j : Fin i.val) :
    (castBelow i j).val = j.val :=
  rfl

/-- Summing a strict-lower row over the ambient finite type is the same as
summing over the indices strictly below the row. -/
theorem sum_strictLowerPart_mul_eq_sum_below
    {R S : Type*} [Zero R] [Semiring S]
    {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (c : R → S) (hc : c 0 = 0) (f : Fin (N + 1) → S)
    (i : Fin (N + 1)) :
    (∑ j : Fin (N + 1), c (strictLowerPart A i j) * f j) =
      ∑ j : Fin i.val,
        c (A i (castBelow i j)) * f (castBelow i j) := by
  calc
    (∑ j : Fin (N + 1), c (strictLowerPart A i j) * f j) =
        ∑ j ∈ Finset.Iio i, c (strictLowerPart A i j) * f j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hji : ¬j < i := by simpa using hj
      simp [strictLowerPart, hji, hc]
    _ = ∑ j : Fin i.val,
        c (A i (castBelow i j)) * f (castBelow i j) := by
      symm
      apply Finset.sum_bij (fun j _ => castBelow i j)
      · intro j _
        exact Finset.mem_Iio.mpr (Fin.mk_lt_mk.mpr j.isLt)
      · intro a _ b _ hab
        exact Fin.ext (congrArg (fun x : Fin (N + 1) => x.val) hab)
      · intro j hj
        have hji : j < i := Finset.mem_Iio.mp hj
        refine ⟨⟨j.val, Fin.mk_lt_mk.mp hji⟩, Finset.mem_univ _, ?_⟩
        exact Fin.ext rfl
      · intro j _
        have hji : castBelow i j < i := Fin.mk_lt_mk.mpr j.isLt
        simp [strictLowerPart, hji]

end


end Matrix

namespace RealRooted.BrandenLeite

noncomputable section

/-- The regularized finite kernel row.  Removing the diagonal makes the
transition nilpotent even when `G * H` has nonzero constant diagonal. -/
def regularizedKernelRow {R : Type*} [CommSemiring R] {N : ℕ}
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i : Fin (N + 1)) : R[X] :=
  let L := Matrix.strictLowerPart (G * H)
  ∑ q ∈ Finset.range (N + 1), C ((L ^ q * G) i 0) * X ^ q

/-- Coefficients of a regularized kernel row at every natural index. -/
theorem coeff_regularizedKernelRow
    {R : Type*} [CommSemiring R] {N : ℕ}
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i : Fin (N + 1)) (q : ℕ) :
    (regularizedKernelRow G H i).coeff q =
      if q < N + 1 then
        ((Matrix.strictLowerPart (G * H)) ^ q * G) i 0
      else 0 := by
  rw [regularizedKernelRow, Polynomial.finsetSum_coeff]
  by_cases hq : q ∈ Finset.range (N + 1)
  · rw [Finset.sum_eq_single q]
    · simp [Finset.mem_range.mp hq]
    · intro j hj hjq
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hjq]
    · exact fun hnot => (hnot hq).elim
  · have hNq : ¬q < N + 1 := by simpa using hq
    rw [if_neg hNq]
    apply Finset.sum_eq_zero
    intro j hj
    have hjq : j ≠ q := by
      intro heq
      subst j
      exact hq hj
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hjq]

/-- Regularized kernel rows satisfy the finite resolvent recurrence. -/
theorem regularizedKernelRow_eq
    {R : Type*} [CommSemiring R] {N : ℕ}
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i : Fin (N + 1)) :
    regularizedKernelRow G H i = C (G i 0) +
      X * ∑ j : Fin (N + 1),
        C (Matrix.strictLowerPart (G * H) i j) *
          regularizedKernelRow G H j := by
  let L := Matrix.strictLowerPart (G * H)
  ext q
  cases q with
  | zero => simp [coeff_regularizedKernelRow]
  | succ q =>
      rw [coeff_regularizedKernelRow]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C,
        if_neg (Nat.succ_ne_zero q), zero_add, Polynomial.coeff_X_mul,
        Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
      by_cases hq : q < N + 1
      · simp only [coeff_regularizedKernelRow, if_pos hq]
        have hsum :
            (∑ j : Fin (N + 1), L i j * (L ^ q * G) j 0) =
              (L ^ (q + 1) * G) i 0 := by
          rw [pow_succ', Matrix.mul_assoc, Matrix.mul_apply]
        rw [show Matrix.strictLowerPart (G * H) = L from rfl, hsum]
        by_cases hsucc : q + 1 < N + 1
        · rw [if_pos hsucc]
        · rw [if_neg hsucc]
          have hqeq : q + 1 = N + 1 := by lia
          rw [hqeq, Matrix.pow_card_eq_zero_of_strictLower L]
          · simp
          · intro a b hab
            exact Matrix.strictLowerPart_apply_eq_zero_of_le _
              (Fin.mk_le_mk.mpr hab)
      · have hsucc : ¬q + 1 < N + 1 := by lia
        simp [hsucc, coeff_regularizedKernelRow, hq]

/-- A lower `G` gives the sharp degree bound for its regularized row. -/
theorem natDegree_regularizedKernelRow_le_row
    {R : Type*} [CommSemiring R] {N : ℕ}
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (hG : ∀ i j, i < j → G i j = 0)
    (i : Fin (N + 1)) :
    (regularizedKernelRow G H i).natDegree ≤ i.val := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro q hiq
  rw [coeff_regularizedKernelRow]
  split
  next _ =>
    apply Matrix.pow_mul_apply_eq_zero_of_lt_add_of_strictLower_lower
      (Matrix.strictLowerPart (G * H)) G
    · intro a b hab
      exact Matrix.strictLowerPart_apply_eq_zero_of_le _
        (Fin.mk_le_mk.mpr hab)
    · exact hG
    · simpa using hiq
  next _ => rfl

/-- If the lower product has zero diagonal, regularization changes nothing and
the row is the kernel row from `KernelRow`. -/
theorem regularizedKernelRow_eq_kernelRow_of_diagonal_zero
    {R : Type*} [CommSemiring R] {N : ℕ}
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (hG : ∀ i j, i < j → G i j = 0)
    (hH : ∀ i j, i < j → H i j = 0)
    (hdiag : ∀ i, (G * H) i i = 0)
    (i : Fin (N + 1)) :
    regularizedKernelRow G H i = kernelRow G H i := by
  ext q
  rw [coeff_regularizedKernelRow, coeff_kernelRow]
  split
  next _ =>
    rw [Matrix.strictLowerPart_eq_self_of_lower_diagonal_zero]
    · exact congrFun₂ (Matrix.mul_pow_mul_eq_mul_mul_pow G H q) i 0
    · intro a b hab
      exact Matrix.mul_apply_eq_zero_of_lt_of_upper_zero G H hG hH hab
    · exact hdiag
  next _ => rfl

/-! ## Literal source-border chain polynomials -/

/-- The finite source-border matrix, extended by zero to the natural-number
indexing used by `chainPolynomial`. -/
def sourceBorderLowerTriangularMatrix
    {R : Type*} [Semiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    LowerTriangularMatrix R :=
  Matrix.toLowerTriangularMatrix (sourceBorder δ G H)

/-- The polynomial left after removing the common leading `X` from a positive
source-border chain row. -/
def sourceBorderReducedChain
    {R : Type*} [CommSemiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i : Fin (N + 1)) : R[X] :=
  ∑ k : Fin (i.val + 1),
    C (sourceBorderLowerTriangularMatrix δ G H (i.val + 1) k.val) *
      chainPolynomial (sourceBorderLowerTriangularMatrix δ G H) k.val

/-- Removing the leading `X` is exact, including at the first positive row. -/
theorem chainPolynomial_sourceBorder_eq_X_mul_reduced
    {R : Type*} [CommSemiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i : Fin (N + 1)) :
    chainPolynomial (sourceBorderLowerTriangularMatrix δ G H) (i.val + 1) =
      X * sourceBorderReducedChain δ G H i := by
  rw [chainPolynomial_succ]
  rfl

/-- The reduced source-border rows satisfy the same strict-lower recurrence as
the regularized kernel rows. -/
theorem sourceBorderReducedChain_eq
    {R : Type*} [CommSemiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i : Fin (N + 1)) :
    sourceBorderReducedChain δ G H i = C (G i 0) +
      X * ∑ j : Fin (N + 1),
        C (Matrix.strictLowerPart (G * H) i j) *
          sourceBorderReducedChain δ G H j := by
  rw [sourceBorderReducedChain, Fin.sum_univ_succ]
  have hirow : i.val + 1 < N + 2 := by lia
  rw [show sourceBorderLowerTriangularMatrix δ G H (i.val + 1)
      ((0 : Fin (i.val + 1)).val) =
      G i 0 by
    simp [sourceBorderLowerTriangularMatrix, hirow, sourceBorder,
      Matrix.toLowerTriangularMatrix]]
  simp only [Fin.val_zero, chainPolynomial_zero, mul_one]
  rw [Matrix.sum_strictLowerPart_mul_eq_sum_below _ C (by simp)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  let j' : Fin (N + 1) := Matrix.castBelow i j
  have hjcol : j.val + 1 < N + 2 := by
    have hjlt := j'.isLt
    simp only [j', Matrix.castBelow_val] at hjlt
    lia
  have hentry : sourceBorderLowerTriangularMatrix δ G H (i.val + 1)
      (j.succ.val) = (G * H) i j' := by
    unfold sourceBorderLowerTriangularMatrix Matrix.toLowerTriangularMatrix
    have hjcols : j.succ.val < N + 2 := by simpa using hjcol
    rw [dif_pos hirow, dif_pos hjcols]
    change sourceBorder δ G H ⟨i.val + 1, hirow⟩
      ⟨j.val + 1, hjcol⟩ = (G * H) i j'
    rw [show (⟨i.val + 1, hirow⟩ : Fin (N + 2)) = i.succ by
      exact Fin.ext rfl]
    rw [show (⟨j.val + 1, hjcol⟩ : Fin (N + 2)) = j'.succ by
      exact Fin.ext rfl]
    rfl
  rw [hentry]
  have hchain :
      chainPolynomial (sourceBorderLowerTriangularMatrix δ G H) j.succ.val =
        X * sourceBorderReducedChain δ G H j' := by
    simpa [j'] using
      chainPolynomial_sourceBorder_eq_X_mul_reduced δ G H j'
  rw [hchain]
  simp [j', mul_left_comm]

/-- A strict-lower recurrence has at most one finite row family. -/
theorem eq_regularizedKernelRow_of_recurrence
    {R : Type*} [CommSemiring R] {N : ℕ}
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (P : Fin (N + 1) → R[X])
    (hP : ∀ i, P i = C (G i 0) +
      X * ∑ j : Fin (N + 1),
        C (Matrix.strictLowerPart (G * H) i j) * P j) :
    P = regularizedKernelRow G H := by
  have aux : ∀ n, ∀ i : Fin (N + 1), i.val = n →
      P i = regularizedKernelRow G H i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro i hin
        rw [hP, regularizedKernelRow_eq]
        apply congrArg (C (G i 0) + X * ·)
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j < i
        · have hji' : j.val < n := by
            rw [← hin]
            exact Fin.mk_lt_mk.mp hji
          rw [ih j.val hji' j rfl]
        · rw [Matrix.strictLowerPart_apply_of_not_lt _ hji]
          simp
  funext i
  exact aux i.val i rfl

/-- The reduced literal chain rows are exactly the regularized kernel rows. -/
theorem sourceBorderReducedChain_eq_regularizedKernelRow
    {R : Type*} [CommSemiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    sourceBorderReducedChain δ G H = regularizedKernelRow G H := by
  exact eq_regularizedKernelRow_of_recurrence G H
    (sourceBorderReducedChain δ G H)
    (sourceBorderReducedChain_eq δ G H)

/-- Literal positive source-border chain rows are `X` times the regularized
kernel rows. -/
theorem chainPolynomial_sourceBorder_eq_X_mul_regularizedKernelRow
    {R : Type*} [CommSemiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i : Fin (N + 1)) :
    chainPolynomial (sourceBorderLowerTriangularMatrix δ G H) (i.val + 1) =
      X * regularizedKernelRow G H i := by
  rw [chainPolynomial_sourceBorder_eq_X_mul_reduced,
    congrFun (sourceBorderReducedChain_eq_regularizedKernelRow δ G H) i]

/-- Unrestricted coefficient formula for a reduced literal source-border
chain row. -/
theorem coeff_sourceBorderReducedChain
    {R : Type*} [CommSemiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i : Fin (N + 1)) (q : ℕ) :
    (sourceBorderReducedChain δ G H i).coeff q =
      if q < N + 1 then
        ((Matrix.strictLowerPart (G * H)) ^ q * G) i 0
      else 0 := by
  rw [congrFun (sourceBorderReducedChain_eq_regularizedKernelRow δ G H) i,
    coeff_regularizedKernelRow]

/-- Unrestricted coefficient formula for every positive literal chain row. -/
theorem coeff_chainPolynomial_sourceBorder
    {R : Type*} [CommSemiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i : Fin (N + 1)) (q : ℕ) :
    (chainPolynomial (sourceBorderLowerTriangularMatrix δ G H)
      (i.val + 1)).coeff q =
      if q = 0 then 0
      else if q - 1 < N + 1 then
        ((Matrix.strictLowerPart (G * H)) ^ (q - 1) * G) i 0
      else 0 := by
  rw [chainPolynomial_sourceBorder_eq_X_mul_regularizedKernelRow]
  cases q with
  | zero => simp
  | succ q => simp [coeff_regularizedKernelRow]

/-- The positive chain row indexed by `i + 1` has degree at most `i + 1`
when `G` is lower triangular. -/
theorem natDegree_chainPolynomial_sourceBorder_le
    {R : Type*} [CommSemiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (hG : ∀ i j, i < j → G i j = 0)
    (i : Fin (N + 1)) :
    (chainPolynomial (sourceBorderLowerTriangularMatrix δ G H)
      (i.val + 1)).natDegree ≤ i.val + 1 := by
  rw [chainPolynomial_sourceBorder_eq_X_mul_regularizedKernelRow]
  have hdegree := Polynomial.natDegree_mul_le_of_le
    Polynomial.natDegree_X_le
    (natDegree_regularizedKernelRow_le_row G H hG i)
  simpa [Nat.add_comm] using hdegree

/-- The first positive chain row has exactly the source entry `G[0,0]`. -/
@[simp]
theorem sourceBorderReducedChain_zero
    {R : Type*} [CommSemiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    sourceBorderReducedChain δ G H 0 = C (G 0 0) := by
  rw [congrFun (sourceBorderReducedChain_eq_regularizedKernelRow δ G H) 0,
    regularizedKernelRow_eq]
  simp [Matrix.strictLowerPart]

/-- Exact first positive row of the literal source-border chain. -/
@[simp]
theorem chainPolynomial_sourceBorder_one
    {R : Type*} [CommSemiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    chainPolynomial (sourceBorderLowerTriangularMatrix δ G H) 1 =
      X * C (G 0 0) := by
  simpa using
    chainPolynomial_sourceBorder_eq_X_mul_reduced δ G H
      (0 : Fin (N + 1))

/-- Exact indexing of the last finite source-border chain row. -/
theorem chainPolynomial_sourceBorder_last
    {R : Type*} [CommSemiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    chainPolynomial (sourceBorderLowerTriangularMatrix δ G H) (N + 1) =
      X * regularizedKernelRow G H (Fin.last N) := by
  simpa using
    chainPolynomial_sourceBorder_eq_X_mul_regularizedKernelRow δ G H
      (Fin.last N)

end

end RealRooted.BrandenLeite
