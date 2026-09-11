import RealRooted.PFPolynomial

/-!
# Lower-triangular row-generating functions

This file provides the small matrix API needed for Mao--Wang matrix-product
statements: infinite lower-triangular matrices indexed by `ℕ`, their finite
row products, row-generating polynomials, and the predicate that every row
generating function is a PF polynomial.
-/

open Polynomial BigOperators

namespace RealRooted

noncomputable section

/-- Infinite matrix indexed by `ℕ`, used as a lower-triangular matrix once
paired with `LowerTriangularMatrix.IsLowerTriangular`. -/
abbrev LowerTriangularMatrix (R : Type*) :=
  ℕ → ℕ → R

namespace LowerTriangularMatrix

variable {R : Type*}

/-- Predicate saying that an infinite matrix indexed by `ℕ` is lower
triangular. -/
def IsLowerTriangular [Zero R] (A : LowerTriangularMatrix R) : Prop :=
  ∀ {i j : ℕ}, i < j → A i j = 0

/-- An infinite matrix is lower unitriangular when it is lower triangular and
has diagonal entries equal to one. -/
def IsLowerUnitriangular [Zero R] [One R] (A : LowerTriangularMatrix R) : Prop :=
  IsLowerTriangular A ∧ ∀ n, A n n = 1

namespace IsLowerUnitriangular

theorem lower [Zero R] [One R] {A : LowerTriangularMatrix R}
    (hA : IsLowerUnitriangular A) :
    IsLowerTriangular A :=
  hA.1

theorem diagonal [Zero R] [One R] {A : LowerTriangularMatrix R}
    (hA : IsLowerUnitriangular A) (n : ℕ) : A n n = 1 :=
  hA.2 n

end IsLowerUnitriangular

/-- Identity lower-triangular matrix. -/
def identity [Zero R] [One R] : LowerTriangularMatrix R :=
  fun i j => if i = j then 1 else 0

/-- Finite product formula for lower-triangular matrices. -/
def mul [Semiring R] (A B : LowerTriangularMatrix R) :
    LowerTriangularMatrix R :=
  fun i j => ∑ k ∈ Finset.Icc j i, A i k * B k j

/-- Recursive powers using the lower-triangular finite product. -/
def pow [Semiring R] (A : LowerTriangularMatrix R) :
    ℕ → LowerTriangularMatrix R
  | 0 => identity
  | r + 1 => mul (pow A r) A

/-- Right-associated product of a finite list of lower-triangular matrices. -/
def listProduct [Semiring R] : List (LowerTriangularMatrix R) →
    LowerTriangularMatrix R
  | [] => identity
  | A :: As => mul A (listProduct As)

@[simp] theorem identity_apply [Zero R] [One R] (i j : ℕ) :
    identity (R := R) i j = if i = j then 1 else 0 :=
  rfl

@[simp] theorem mul_apply [Semiring R]
    (A B : LowerTriangularMatrix R) (i j : ℕ) :
    mul A B i j = ∑ k ∈ Finset.Icc j i, A i k * B k j :=
  rfl

@[simp] theorem pow_zero [Semiring R] (A : LowerTriangularMatrix R) :
    pow A 0 = identity :=
  rfl

@[simp] theorem pow_succ [Semiring R] (A : LowerTriangularMatrix R) (r : ℕ) :
    pow A (r + 1) = mul (pow A r) A :=
  rfl

@[simp] theorem listProduct_nil [Semiring R] :
    listProduct ([] : List (LowerTriangularMatrix R)) = identity :=
  rfl

@[simp] theorem listProduct_cons [Semiring R]
    (A : LowerTriangularMatrix R) (As : List (LowerTriangularMatrix R)) :
    listProduct (A :: As) = mul A (listProduct As) :=
  rfl

protected theorem IsLowerTriangular.identity [Semiring R] :
    IsLowerTriangular (identity (R := R)) := by
  intro i j hij
  simp [identity, ne_of_lt hij]

theorem IsLowerTriangular.mul [Semiring R] {A B : LowerTriangularMatrix R}
    (hA : IsLowerTriangular A) (_hB : IsLowerTriangular B) :
    IsLowerTriangular (mul A B) := by
  intro i j hij
  rw [mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  have hjk : j ≤ k := (Finset.mem_Icc.mp hk).1
  have hik : i < k := lt_of_lt_of_le hij hjk
  rw [hA hik, zero_mul]

protected theorem IsLowerUnitriangular.identity [Semiring R] :
    IsLowerUnitriangular (identity (R := R)) := by
  constructor
  · exact IsLowerTriangular.identity
  · intro n
    simp [identity]

theorem IsLowerUnitriangular.mul [Semiring R] {A B : LowerTriangularMatrix R}
    (hA : IsLowerUnitriangular A) (hB : IsLowerUnitriangular B) :
    IsLowerUnitriangular (mul A B) := by
  constructor
  · exact IsLowerTriangular.mul hA.1 hB.1
  · intro n
    simp [mul_apply, hA.diagonal n, hB.diagonal n]

theorem IsLowerUnitriangular.pow [Semiring R] {A : LowerTriangularMatrix R}
    (hA : IsLowerUnitriangular A) (r : ℕ) :
    IsLowerUnitriangular (pow A r) := by
  induction r with
  | zero => exact IsLowerUnitriangular.identity
  | succ r ih => exact ih.mul hA

theorem IsLowerUnitriangular.listProduct [Semiring R]
    {As : List (LowerTriangularMatrix R)}
    (hAs : ∀ A ∈ As, IsLowerUnitriangular A) :
    IsLowerUnitriangular (listProduct As) := by
  induction As with
  | nil => exact IsLowerUnitriangular.identity
  | cons A As ih =>
      apply IsLowerUnitriangular.mul
      · exact hAs A (by simp)
      · apply ih
        intro B hB
        exact hAs B (by simp [hB])

theorem IsLowerTriangular.pow [Semiring R] {A : LowerTriangularMatrix R}
    (hA : IsLowerTriangular A) (r : ℕ) :
    IsLowerTriangular (pow A r) := by
  induction r with
  | zero =>
      exact IsLowerTriangular.identity
  | succ r ih =>
      exact IsLowerTriangular.mul ih hA

theorem mul_identity_of_isLowerTriangular [Semiring R]
    {A : LowerTriangularMatrix R} (hA : IsLowerTriangular A) :
    mul A identity = A := by
  funext i j
  rcases le_or_gt j i with hji | hij
  · rw [mul_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      simp [identity, hkj]
    · intro hj
      exact (hj (Finset.mem_Icc.mpr ⟨le_rfl, hji⟩)).elim
  · rw [hA hij]
    rw [mul_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hjk : j ≤ k := (Finset.mem_Icc.mp hk).1
    have hki : k ≤ i := (Finset.mem_Icc.mp hk).2
    exact (not_lt_of_ge hki (lt_of_lt_of_le hij hjk)).elim

theorem identity_mul_of_isLowerTriangular [Semiring R]
    {A : LowerTriangularMatrix R} (hA : IsLowerTriangular A) :
    mul identity A = A := by
  funext i j
  rcases le_or_gt j i with hji | hij
  · rw [mul_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k hk hki
      simp [identity, Ne.symm hki]
    · intro hi
      exact (hi (Finset.mem_Icc.mpr ⟨hji, le_rfl⟩)).elim
  · rw [hA hij]
    rw [mul_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hjk : j ≤ k := (Finset.mem_Icc.mp hk).1
    have hki : k ≤ i := (Finset.mem_Icc.mp hk).2
    exact (not_lt_of_ge hki (lt_of_lt_of_le hij hjk)).elim

theorem pow_one_of_isLowerTriangular [Semiring R]
    {A : LowerTriangularMatrix R} (hA : IsLowerTriangular A) :
    pow A 1 = A := by
  simpa using identity_mul_of_isLowerTriangular hA

theorem IsLowerTriangular.listProduct [Semiring R]
    {As : List (LowerTriangularMatrix R)}
    (hAs : ∀ A ∈ As, IsLowerTriangular A) :
    IsLowerTriangular (listProduct As) := by
  induction As with
  | nil =>
      exact IsLowerTriangular.identity
  | cons A As ih =>
      have hA : IsLowerTriangular A := hAs A (by simp)
      have htail : ∀ B ∈ As, IsLowerTriangular B := by
        intro B hB
        exact hAs B (by simp [hB])
      intro i j hij
      exact IsLowerTriangular.mul hA (ih htail) hij

theorem listProduct_singleton_of_isLowerTriangular [Semiring R]
    {A : LowerTriangularMatrix R} (hA : IsLowerTriangular A) :
    listProduct [A] = A := by
  simpa using mul_identity_of_isLowerTriangular hA

theorem mul_assoc [Semiring R] (A B C : LowerTriangularMatrix R) :
    mul (mul A B) C = mul A (mul B C) := by
  funext i j
  simp only [mul_apply]
  calc
    (∑ k ∈ Finset.Icc j i, (∑ l ∈ Finset.Icc k i, A i l * B l k) * C k j)
        = ∑ k ∈ Finset.Ico j (i + 1),
            ∑ l ∈ Finset.Ico k (i + 1), (A i l * B l k) * C k j := by
      rw [← Finset.Ico_add_one_right_eq_Icc j i]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.sum_mul]
      rw [← Finset.Ico_add_one_right_eq_Icc k i]
    _ = ∑ l ∈ Finset.Ico j (i + 1),
            ∑ k ∈ Finset.Ico j (l + 1), (A i l * B l k) * C k j := by
      rw [Finset.sum_Ico_Ico_comm]
    _ = ∑ l ∈ Finset.Icc j i, A i l * ∑ k ∈ Finset.Icc j l, B l k * C k j := by
      rw [← Finset.Ico_add_one_right_eq_Icc j i]
      apply Finset.sum_congr rfl
      intro l _hl
      rw [Finset.mul_sum]
      rw [← Finset.Ico_add_one_right_eq_Icc j l]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [_root_.mul_assoc]

/-- Row-generating polynomial of row `i`, truncated at the diagonal. -/
def rowPolynomial [Semiring R] (A : LowerTriangularMatrix R) (i : ℕ) : R[X] :=
  ∑ j ∈ Finset.range (i + 1), C (A i j) * X ^ j

/-- Splitting a unit-diagonal row sum into its entries strictly before the
diagonal and its final term.  The target sequence is polynomial-valued so this
can be shared by row-generating and recursively defined polynomial families. -/
theorem sum_C_mul_range_succ_eq_fin_sum_add [Semiring R]
    (A : LowerTriangularMatrix R) {n : ℕ} (hdiag : A (n + 1) (n + 1) = 1)
    (p : ℕ → R[X]) :
    (∑ k ∈ Finset.range (n + 2), C (A (n + 1) k) * p k) =
      (∑ k : Fin (n + 1), C (A (n + 1) k) * p k) + p (n + 1) := by
  rw [show n + 2 = (n + 1) + 1 by lia, Finset.sum_range_succ]
  rw [← Fin.sum_univ_eq_sum_range (fun k => C (A (n + 1) k) * p k) (n + 1)]
  simp [hdiag]

theorem coeff_rowPolynomial_of_le [Semiring R] (A : LowerTriangularMatrix R) {i j : ℕ}
    (hij : j ≤ i) :
    (rowPolynomial A i).coeff j = A i j := by
  rw [rowPolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    rw [coeff_C_mul, coeff_X_pow, if_neg hbj.symm, mul_zero]
  · intro hj
    exact (hj (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hij))).elim

theorem coeff_rowPolynomial_of_gt [Semiring R] (A : LowerTriangularMatrix R) {i j : ℕ}
    (hij : i < j) :
    (rowPolynomial A i).coeff j = 0 := by
  rw [rowPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro b hb
  rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
  intro hbj
  have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  exact (not_le_of_gt hij) (hbj ▸ hbi)

/-- Coefficients of a row polynomial recover every entry of a lower-triangular
matrix, including the zero entries above the diagonal. -/
theorem coeff_rowPolynomial [Semiring R] {A : LowerTriangularMatrix R}
    (hA : IsLowerTriangular A) (i j : ℕ) :
    (rowPolynomial A i).coeff j = A i j := by
  by_cases hji : j ≤ i
  · exact coeff_rowPolynomial_of_le A hji
  · have hij : i < j := Nat.lt_of_not_ge hji
    rw [coeff_rowPolynomial_of_gt A hij, hA hij]

theorem natDegree_rowPolynomial_le [Semiring R] (A : LowerTriangularMatrix R) (i : ℕ) :
    (rowPolynomial A i).natDegree ≤ i := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  exact coeff_rowPolynomial_of_gt A hj

theorem coeff_rowPolynomial_mul_of_le
    [Semiring R] (A B : LowerTriangularMatrix R) {i j : ℕ} (hij : j ≤ i) :
    (rowPolynomial (mul A B) i).coeff j =
      ∑ k ∈ Finset.Icc j i, A i k * B k j := by
  rw [coeff_rowPolynomial_of_le _ hij, mul_apply]

@[simp] theorem rowPolynomial_mul_identity
    [Semiring R] (A : LowerTriangularMatrix R) (i : ℕ) :
    rowPolynomial (mul A identity) i = rowPolynomial A i := by
  ext j
  by_cases hji : j ≤ i
  · rw [coeff_rowPolynomial_mul_of_le A identity hji,
      coeff_rowPolynomial_of_le A hji]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _hk hkj
      simp [identity, hkj]
    · intro hj
      exact (hj (Finset.mem_Icc.mpr ⟨le_rfl, hji⟩)).elim
  · have hij : i < j := Nat.lt_of_not_ge hji
    rw [coeff_rowPolynomial_of_gt _ hij, coeff_rowPolynomial_of_gt _ hij]

/-- Every row-generating polynomial of a lower-triangular matrix is PF. -/
def RowGeneratingFunctionsPF (A : LowerTriangularMatrix ℝ) : Prop :=
  ∀ i : ℕ, IsPFPolynomial (rowPolynomial A i)

theorem RowGeneratingFunctionsPF.row {A : LowerTriangularMatrix ℝ}
    (hA : RowGeneratingFunctionsPF A) (i : ℕ) :
    IsPFPolynomial (rowPolynomial A i) :=
  hA i

@[simp] theorem RowGeneratingFunctionsPF.mul_identity
    {A : LowerTriangularMatrix ℝ} (hA : RowGeneratingFunctionsPF A) :
    RowGeneratingFunctionsPF (mul A identity) := by
  intro i
  rw [rowPolynomial_mul_identity]
  exact hA.row i

/-- One-step right multiplication preservation for row-generating PF
polynomials. -/
def RightPreservesRowGeneratingFunctionsPF
    (B : LowerTriangularMatrix ℝ) : Prop :=
  ∀ M : LowerTriangularMatrix ℝ,
    RowGeneratingFunctionsPF M →
      RowGeneratingFunctionsPF (mul M B)

/-- Matrix-product preservation shape needed for Mao--Wang Theorem 1.3. -/
def RightPowersPreserveRowGeneratingFunctionsPF
    (B : LowerTriangularMatrix ℝ) : Prop :=
  ∀ (M : LowerTriangularMatrix ℝ) (r : ℕ),
    RowGeneratingFunctionsPF M →
      RowGeneratingFunctionsPF (mul M (pow B r))

theorem RightPreservesRowGeneratingFunctionsPF.identity :
    RightPreservesRowGeneratingFunctionsPF identity := by
  intro M hM
  simpa using hM.mul_identity

theorem RightPreservesRowGeneratingFunctionsPF.trans
    {B C : LowerTriangularMatrix ℝ}
    (hB : RightPreservesRowGeneratingFunctionsPF B)
    (hC : RightPreservesRowGeneratingFunctionsPF C) :
    RightPreservesRowGeneratingFunctionsPF (mul B C) := by
  intro M hM
  have hBC := hC (mul M B) (hB M hM)
  simpa [mul_assoc] using hBC

theorem RightPreservesRowGeneratingFunctionsPF.listProduct
    {Bs : List (LowerTriangularMatrix ℝ)}
    (hBs : ∀ B ∈ Bs, RightPreservesRowGeneratingFunctionsPF B) :
    RightPreservesRowGeneratingFunctionsPF (listProduct Bs) := by
  induction Bs with
  | nil =>
      simpa using RightPreservesRowGeneratingFunctionsPF.identity
  | cons B Bs ih =>
      have hB : RightPreservesRowGeneratingFunctionsPF B := hBs B (by simp)
      have htail : ∀ C ∈ Bs, RightPreservesRowGeneratingFunctionsPF C := by
        intro C hC
        exact hBs C (by simp [hC])
      simpa using hB.trans (ih htail)

theorem RightPreservesRowGeneratingFunctionsPF.rightPowers
    {B : LowerTriangularMatrix ℝ}
    (hB : RightPreservesRowGeneratingFunctionsPF B) :
    RightPowersPreserveRowGeneratingFunctionsPF B := by
  intro M r hM
  induction r with
  | zero =>
      simpa using hM.mul_identity
  | succ r ih =>
      have hstep := hB (mul M (pow B r)) ih
      simpa [pow_succ, mul_assoc] using hstep

end LowerTriangularMatrix

end

end RealRooted
