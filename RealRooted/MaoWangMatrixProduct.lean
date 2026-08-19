import RealRooted.LowerTriangularMatrix
import RealRooted.NarayanaTransformation

/-!
# Mao--Wang matrix-product interfaces

This file connects the lower-triangular row-generating-function API to the
basis transforms used in Mao--Wang, *The Narayana transformation*, Theorem 1.3.
The bridge is intentionally thin: a basis `P n` gives the coefficient matrix
with entry `[X^j] P i`, and right multiplication by that matrix sends each row
generating polynomial to `basisTransform P` of the original row.
-/

open Polynomial BigOperators

namespace RealRooted

noncomputable section

namespace LowerTriangularMatrix

/-- Coefficient matrix for a polynomial basis transform.  The `(i,j)` entry is
the coefficient of `X^j` in the image of `X^i`. -/
def basisCoefficientMatrix (P : ℕ → ℝ[X]) : LowerTriangularMatrix ℝ :=
  fun i j => (P i).coeff j

@[simp] theorem basisCoefficientMatrix_apply
    (P : ℕ → ℝ[X]) (i j : ℕ) :
    basisCoefficientMatrix P i j = (P i).coeff j :=
  rfl

theorem basisCoefficientMatrix_isLowerTriangular {P : ℕ → ℝ[X]}
    (hP : ∀ i, (P i).natDegree ≤ i) :
    IsLowerTriangular (basisCoefficientMatrix P) := by
  intro i j hij
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hP i) hij)

@[simp] theorem rowPolynomial_basisCoefficientMatrix {P : ℕ → ℝ[X]}
    (hP : ∀ i, (P i).natDegree ≤ i) (i : ℕ) :
    rowPolynomial (basisCoefficientMatrix P) i = P i := by
  ext j
  by_cases hji : j ≤ i
  · rw [coeff_rowPolynomial_of_le _ hji]
    simp [basisCoefficientMatrix]
  · have hij : i < j := Nat.lt_of_not_ge hji
    rw [coeff_rowPolynomial_of_gt _ hij]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hP i) hij)).symm

/-- Expanding the basis transform of a row polynomial over the row's finite
support. -/
theorem basisTransform_rowPolynomial
    (P : ℕ → ℝ[X]) (M : LowerTriangularMatrix ℝ) (i : ℕ) :
    basisTransform P (rowPolynomial M i) =
      ∑ k ∈ Finset.range (i + 1), C (M i k) * P k := by
  classical
  unfold rowPolynomial
  let s := Finset.range (i + 1)
  change basisTransform P (∑ k ∈ s, C (M i k) * X ^ k) =
    ∑ k ∈ s, C (M i k) * P k
  refine Finset.induction_on s ?zero ?insert
  · simp
  · intro k s hks hs
    simp only [Finset.sum_insert hks, basisTransform_add, hs]
    rw [show C (M i k) * X ^ k = (M i k) • X ^ k by
      simp [Polynomial.C_mul']]
    rw [basisTransform_smul, basisTransform_X_pow]

theorem coeff_basisTransform_rowPolynomial
    (P : ℕ → ℝ[X]) (M : LowerTriangularMatrix ℝ) (i j : ℕ) :
    (basisTransform P (rowPolynomial M i)).coeff j =
      ∑ k ∈ Finset.range (i + 1), M i k * (P k).coeff j := by
  rw [basisTransform_rowPolynomial]
  simp [Polynomial.coeff_C_mul]

/-- Right multiplication by the coefficient matrix of a degree-compatible basis
is the same as applying the corresponding basis transform to each row. -/
theorem rowPolynomial_mul_basisCoefficientMatrix {P : ℕ → ℝ[X]}
    (hP : ∀ i, (P i).natDegree ≤ i)
    (M : LowerTriangularMatrix ℝ) (i : ℕ) :
    rowPolynomial (mul M (basisCoefficientMatrix P)) i =
      basisTransform P (rowPolynomial M i) := by
  ext j
  by_cases hji : j ≤ i
  · rw [coeff_rowPolynomial_mul_of_le M (basisCoefficientMatrix P) hji,
      coeff_basisTransform_rowPolynomial]
    have hsubset : Finset.Icc j i ⊆ Finset.range (i + 1) := by
      intro k hk
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_Icc.mp hk).2)
    rw [← Finset.sum_subset hsubset]
    · simp [basisCoefficientMatrix]
    · intro k hkrange hkIcc
      have hki : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkrange)
      have hkj : k < j := by exact lt_of_not_ge fun hjk => hkIcc (Finset.mem_Icc.mpr ⟨hjk, hki⟩)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hP k) hkj),
        mul_zero]
  · have hij : i < j := Nat.lt_of_not_ge hji
    rw [coeff_rowPolynomial_of_gt _ hij, coeff_basisTransform_rowPolynomial]
    symm
    apply Finset.sum_eq_zero
    intro k hkrange
    have hki : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkrange)
    have hkj : k < j := lt_of_le_of_lt hki hij
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hP k) hkj),
      mul_zero]

theorem RowGeneratingFunctionsPF.mul_basisCoefficientMatrix {P : ℕ → ℝ[X]}
    {M : LowerTriangularMatrix ℝ} (hM : RowGeneratingFunctionsPF M)
    (hPdegree : ∀ i, (P i).natDegree ≤ i)
    (hPpres : ∀ p : ℝ[X], IsPFPolynomial p → IsPFPolynomial (basisTransform P p)) :
    RowGeneratingFunctionsPF (mul M (basisCoefficientMatrix P)) := by
  intro i
  rw [rowPolynomial_mul_basisCoefficientMatrix hPdegree]
  exact hPpres (rowPolynomial M i) (hM.row i)

/-- Affine-substitution basis `X^n ↦ (a * X + d)^n`. -/
def affineBasisPolynomial (a d : ℝ) (n : ℕ) : ℝ[X] :=
  (C a * X + C d) ^ n

theorem natDegree_affineBasisPolynomial_le (a d : ℝ) (n : ℕ) :
    (affineBasisPolynomial a d n).natDegree ≤ n := by
  unfold affineBasisPolynomial
  calc
    ((C a * X + C d : ℝ[X]) ^ n).natDegree
        ≤ n * (C a * X + C d : ℝ[X]).natDegree :=
      Polynomial.natDegree_pow_le
    _ ≤ n * 1 := by
      exact Nat.mul_le_mul_left n (by
        calc
          (C a * X + C d : ℝ[X]).natDegree
              ≤ max (C a * X).natDegree (C d).natDegree :=
            Polynomial.natDegree_add_le _ _
          _ ≤ max 1 0 := by
            apply max_le_max
            · by_cases ha0 : a = 0
              · simp [ha0]
              · rw [Polynomial.natDegree_C_mul ha0]
                simp
            · simp
          _ = 1 := by simp)
    _ = n := by simp

theorem basisTransform_affineBasisPolynomial
    (a d : ℝ) (p : ℝ[X]) :
    basisTransform (affineBasisPolynomial a d) p = p.comp (C a * X + C d) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [basisTransform_add, hp, hq]
  | monomial n c =>
      rw [basisTransform_monomial]
      unfold affineBasisPolynomial
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp [Polynomial.comp]

/-- Coefficient matrix for the affine substitution `f(x) ↦ f(a * x + d)`. -/
def affineSubstitutionMatrix (a d : ℝ) : LowerTriangularMatrix ℝ :=
  basisCoefficientMatrix (affineBasisPolynomial a d)

theorem affineSubstitutionMatrix_isLowerTriangular (a d : ℝ) :
    IsLowerTriangular (affineSubstitutionMatrix a d) :=
  basisCoefficientMatrix_isLowerTriangular (natDegree_affineBasisPolynomial_le a d)

@[simp] theorem rowPolynomial_affineSubstitutionMatrix (a d : ℝ) (n : ℕ) :
    rowPolynomial (affineSubstitutionMatrix a d) n = affineBasisPolynomial a d n := by
  simpa [affineSubstitutionMatrix] using
    rowPolynomial_basisCoefficientMatrix (natDegree_affineBasisPolynomial_le a d) n

theorem rowPolynomial_mul_affineSubstitutionMatrix
    (a d : ℝ) (M : LowerTriangularMatrix ℝ) (i : ℕ) :
    rowPolynomial (mul M (affineSubstitutionMatrix a d)) i =
      (rowPolynomial M i).comp (C a * X + C d) := by
  simp [affineSubstitutionMatrix,
    rowPolynomial_mul_basisCoefficientMatrix (natDegree_affineBasisPolynomial_le a d),
    basisTransform_affineBasisPolynomial]

theorem RowGeneratingFunctionsPF.mul_affineSubstitutionMatrix
    {M : LowerTriangularMatrix ℝ} (hM : RowGeneratingFunctionsPF M)
    {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) :
    RowGeneratingFunctionsPF (mul M (affineSubstitutionMatrix a d)) := by
  intro i
  rw [rowPolynomial_mul_affineSubstitutionMatrix]
  exact (hM.row i).comp_C_mul_X_add_C ha hd

theorem affineSubstitutionMatrix_rightPreservesRowGeneratingFunctionsPF
    {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) :
    RightPreservesRowGeneratingFunctionsPF (affineSubstitutionMatrix a d) := by
  intro M hM
  exact hM.mul_affineSubstitutionMatrix ha hd

theorem affineSubstitutionMatrix_rightPowersPreserveRowGeneratingFunctionsPF
    {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) :
    RightPowersPreserveRowGeneratingFunctionsPF (affineSubstitutionMatrix a d) :=
  (affineSubstitutionMatrix_rightPreservesRowGeneratingFunctionsPF ha hd).rightPowers

/-- The falling-factorial basis has degree at most its index. -/
theorem natDegree_fallingFactorialPolynomial_le (n : ℕ) :
    (fallingFactorialPolynomial n).natDegree ≤ n := by
  rw [fallingFactorialPolynomial]
  calc
    (∏ i ∈ Finset.range n, (X - C (i : ℝ))).natDegree
        ≤ ∑ i ∈ Finset.range n, (X - C (i : ℝ)).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i ∈ Finset.range n, 1 := by
      apply Finset.sum_le_sum
      intro i _hi
      have hsub : (X - C (i : ℝ) : ℝ[X]) = X + C (-(i : ℝ)) := by simp [sub_eq_add_neg]
      rw [hsub]
      exact le_of_eq (Polynomial.natDegree_X_add_C (-(i : ℝ)))
    _ = n := by simp

/-- The generalized rising-factorial basis has degree at most its index. -/
theorem natDegree_risingFactorialPolynomial_le (μ : ℝ) (n : ℕ) :
    (risingFactorialPolynomial μ n).natDegree ≤ n := by
  rw [risingFactorialPolynomial]
  calc
    (∏ i ∈ Finset.range n, (X + C ((i : ℝ) * μ))).natDegree
        ≤ ∑ i ∈ Finset.range n, (X + C ((i : ℝ) * μ)).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i ∈ Finset.range n, 1 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact le_of_eq (Polynomial.natDegree_X_add_C ((i : ℝ) * μ))
    _ = n := by simp

/-- The Touchard basis has degree at most its index. -/
theorem natDegree_touchard_le (n : ℕ) :
    (touchard n).natDegree ≤ n := by
  induction n with
  | zero => simp [touchard]
  | succ n ih =>
      rw [touchard_succ]
      calc
        (X * touchard n + X * (touchard n).derivative).natDegree
            ≤ max (X * touchard n).natDegree (X * (touchard n).derivative).natDegree :=
          Polynomial.natDegree_add_le _ _
        _ ≤ max (n + 1) (n + 1) := by
          apply max_le_max
          · calc
              (X * touchard n).natDegree ≤ X.natDegree + (touchard n).natDegree :=
                Polynomial.natDegree_mul_le
              _ ≤ 1 + n := by
                rw [Polynomial.natDegree_X]
                exact Nat.add_le_add_left ih 1
              _ = n + 1 := by lia
          · calc
              (X * (touchard n).derivative).natDegree ≤
                  X.natDegree + (touchard n).derivative.natDegree :=
                Polynomial.natDegree_mul_le
              _ ≤ 1 + (touchard n).natDegree := by
                have hder :
                    (touchard n).derivative.natDegree ≤ (touchard n).natDegree :=
                  by rw [(touchard n).natDegree_derivative]; exact Nat.sub_le _ _
                rw [Polynomial.natDegree_X]
                exact Nat.add_le_add_left hder 1
              _ ≤ 1 + n := Nat.add_le_add_left ih 1
              _ = n + 1 := by lia
        _ = n + 1 := by simp

/-- Coefficient matrix for the falling-factorial basis. -/
def fallingFactorialMatrix : LowerTriangularMatrix ℝ :=
  basisCoefficientMatrix fallingFactorialPolynomial

theorem fallingFactorialMatrix_isLowerTriangular :
    IsLowerTriangular fallingFactorialMatrix :=
  basisCoefficientMatrix_isLowerTriangular natDegree_fallingFactorialPolynomial_le

@[simp] theorem rowPolynomial_fallingFactorialMatrix (n : ℕ) :
    rowPolynomial fallingFactorialMatrix n = fallingFactorialPolynomial n := by
  simpa [fallingFactorialMatrix] using
    rowPolynomial_basisCoefficientMatrix natDegree_fallingFactorialPolynomial_le n

theorem rowPolynomial_mul_fallingFactorialMatrix
    (M : LowerTriangularMatrix ℝ) (i : ℕ) :
    rowPolynomial (mul M fallingFactorialMatrix) i =
      basisTransform fallingFactorialPolynomial (rowPolynomial M i) := by
  simpa [fallingFactorialMatrix] using
    rowPolynomial_mul_basisCoefficientMatrix
      (P := fallingFactorialPolynomial) natDegree_fallingFactorialPolynomial_le M i

/-- Coefficient matrix for the Touchard basis, equivalently the Stirling
matrix acting on row-generating polynomials. -/
noncomputable def touchardMatrix : LowerTriangularMatrix ℝ :=
  basisCoefficientMatrix touchard

theorem touchardMatrix_isLowerTriangular :
    IsLowerTriangular touchardMatrix :=
  basisCoefficientMatrix_isLowerTriangular natDegree_touchard_le

@[simp] theorem rowPolynomial_touchardMatrix (n : ℕ) :
    rowPolynomial touchardMatrix n = touchard n := by
  simpa [touchardMatrix] using
    rowPolynomial_basisCoefficientMatrix natDegree_touchard_le n

theorem rowPolynomial_mul_touchardMatrix
    (M : LowerTriangularMatrix ℝ) (i : ℕ) :
    rowPolynomial (mul M touchardMatrix) i =
      basisTransform touchard (rowPolynomial M i) := by
  simpa [touchardMatrix] using
    rowPolynomial_mul_basisCoefficientMatrix (P := touchard) natDegree_touchard_le M i

theorem RowGeneratingFunctionsPF.mul_touchardMatrix
    {M : LowerTriangularMatrix ℝ} (hM : RowGeneratingFunctionsPF M) :
    RowGeneratingFunctionsPF (mul M touchardMatrix) := by
  intro i
  rw [rowPolynomial_mul_touchardMatrix]
  exact touchardTransformPreservesPF (hM.row i)

theorem touchardMatrix_rightPreservesRowGeneratingFunctionsPF :
    RightPreservesRowGeneratingFunctionsPF touchardMatrix := by
  intro M hM
  exact hM.mul_touchardMatrix

theorem touchardMatrix_rightPowersPreserveRowGeneratingFunctionsPF :
    RightPowersPreserveRowGeneratingFunctionsPF touchardMatrix :=
  touchardMatrix_rightPreservesRowGeneratingFunctionsPF.rightPowers

/-- Coefficient matrix for the generalized rising-factorial basis. -/
def risingFactorialMatrix (μ : ℝ) : LowerTriangularMatrix ℝ :=
  basisCoefficientMatrix (risingFactorialPolynomial μ)

theorem risingFactorialMatrix_isLowerTriangular (μ : ℝ) :
    IsLowerTriangular (risingFactorialMatrix μ) :=
  basisCoefficientMatrix_isLowerTriangular (natDegree_risingFactorialPolynomial_le μ)

@[simp] theorem rowPolynomial_risingFactorialMatrix (μ : ℝ) (n : ℕ) :
    rowPolynomial (risingFactorialMatrix μ) n = risingFactorialPolynomial μ n := by
  simpa [risingFactorialMatrix] using
    rowPolynomial_basisCoefficientMatrix (natDegree_risingFactorialPolynomial_le μ) n

theorem rowPolynomial_mul_risingFactorialMatrix
    (μ : ℝ) (M : LowerTriangularMatrix ℝ) (i : ℕ) :
    rowPolynomial (mul M (risingFactorialMatrix μ)) i =
      basisTransform (risingFactorialPolynomial μ) (rowPolynomial M i) := by
  simpa [risingFactorialMatrix] using
    rowPolynomial_mul_basisCoefficientMatrix
      (P := risingFactorialPolynomial μ) (natDegree_risingFactorialPolynomial_le μ) M i

theorem RowGeneratingFunctionsPF.mul_risingFactorialMatrix
    {M : LowerTriangularMatrix ℝ} (hM : RowGeneratingFunctionsPF M)
    {μ : ℝ} (hμ : 0 < μ) :
    RowGeneratingFunctionsPF (mul M (risingFactorialMatrix μ)) := by
  intro i
  rw [rowPolynomial_mul_risingFactorialMatrix]
  exact generalizedRisingFactorialPreservesPF hμ (hM.row i)

theorem risingFactorialMatrix_rightPreservesRowGeneratingFunctionsPF
    {μ : ℝ} (hμ : 0 < μ) :
    RightPreservesRowGeneratingFunctionsPF (risingFactorialMatrix μ) := by
  intro M hM
  exact hM.mul_risingFactorialMatrix hμ

theorem risingFactorialMatrix_rightPowersPreserveRowGeneratingFunctionsPF
    {μ : ℝ} (hμ : 0 < μ) :
    RightPowersPreserveRowGeneratingFunctionsPF (risingFactorialMatrix μ) :=
  (risingFactorialMatrix_rightPreservesRowGeneratingFunctionsPF hμ).rightPowers

/-- Mao--Wang's Narayana coefficient matrix, whose row `n` generates
`N_{n,m}`. -/
def narayanaMatrix (m : ℕ) : LowerTriangularMatrix ℝ :=
  basisCoefficientMatrix (narayanaPolynomial m)

theorem narayanaMatrix_isLowerTriangular (m : ℕ) :
    IsLowerTriangular (narayanaMatrix m) :=
  basisCoefficientMatrix_isLowerTriangular (natDegree_narayanaPolynomial_le m)

@[simp] theorem rowPolynomial_narayanaMatrix (m n : ℕ) :
    rowPolynomial (narayanaMatrix m) n = narayanaPolynomial m n := by
  simpa [narayanaMatrix] using
    rowPolynomial_basisCoefficientMatrix (natDegree_narayanaPolynomial_le m) n

theorem rowPolynomial_mul_narayanaMatrix
    (m : ℕ) (M : LowerTriangularMatrix ℝ) (i : ℕ) :
    rowPolynomial (mul M (narayanaMatrix m)) i =
      narayanaTransform m (rowPolynomial M i) := by
  simpa [narayanaMatrix, narayanaTransform] using
    rowPolynomial_mul_basisCoefficientMatrix
      (P := narayanaPolynomial m) (natDegree_narayanaPolynomial_le m) M i

theorem RowGeneratingFunctionsPF.mul_narayanaMatrix
    {M : LowerTriangularMatrix ℝ} (hM : RowGeneratingFunctionsPF M) (m : ℕ) :
    RowGeneratingFunctionsPF (mul M (narayanaMatrix m)) := by
  intro i
  rw [rowPolynomial_mul_narayanaMatrix]
  exact narayanaTransformPreservesPF m (hM.row i)

theorem narayanaMatrix_rightPreservesRowGeneratingFunctionsPF (m : ℕ) :
    RightPreservesRowGeneratingFunctionsPF (narayanaMatrix m) := by
  intro M hM
  exact hM.mul_narayanaMatrix m

theorem narayanaMatrix_rightPowersPreserveRowGeneratingFunctionsPF (m : ℕ) :
    RightPowersPreserveRowGeneratingFunctionsPF (narayanaMatrix m) :=
  (narayanaMatrix_rightPreservesRowGeneratingFunctionsPF m).rightPowers

/-- The one-step lower-triangular matrix factors covered by Mao--Wang's
matrix-product criterion.  The falling-factorial coefficient matrix is kept
separate because Brenti's theorem is used in the inverse direction; the
Stirling second-kind branch is represented here by `touchardMatrix`. -/
inductive MaoWangAdmissibleMatrix : LowerTriangularMatrix ℝ → Prop
  | affine {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) :
      MaoWangAdmissibleMatrix (affineSubstitutionMatrix a d)
  | touchard : MaoWangAdmissibleMatrix touchardMatrix
  | rising {μ : ℝ} (hμ : 0 < μ) :
      MaoWangAdmissibleMatrix (risingFactorialMatrix μ)
  | narayana (m : ℕ) :
      MaoWangAdmissibleMatrix (narayanaMatrix m)

theorem MaoWangAdmissibleMatrix.isLowerTriangular
    {B : LowerTriangularMatrix ℝ} (hB : MaoWangAdmissibleMatrix B) :
    IsLowerTriangular B := by
  cases hB with
  | affine ha hd =>
      exact affineSubstitutionMatrix_isLowerTriangular _ _
  | touchard =>
      exact touchardMatrix_isLowerTriangular
  | rising hμ =>
      exact risingFactorialMatrix_isLowerTriangular _
  | narayana m =>
      exact narayanaMatrix_isLowerTriangular m

theorem MaoWangAdmissibleMatrix.rightPreservesRowGeneratingFunctionsPF
    {B : LowerTriangularMatrix ℝ} (hB : MaoWangAdmissibleMatrix B) :
    RightPreservesRowGeneratingFunctionsPF B := by
  cases hB with
  | affine ha hd =>
      exact affineSubstitutionMatrix_rightPreservesRowGeneratingFunctionsPF ha hd
  | touchard =>
      exact touchardMatrix_rightPreservesRowGeneratingFunctionsPF
  | rising hμ =>
      exact risingFactorialMatrix_rightPreservesRowGeneratingFunctionsPF hμ
  | narayana m =>
      exact narayanaMatrix_rightPreservesRowGeneratingFunctionsPF m

theorem MaoWangAdmissibleMatrix.rightPowersPreserveRowGeneratingFunctionsPF
    {B : LowerTriangularMatrix ℝ} (hB : MaoWangAdmissibleMatrix B) :
    RightPowersPreserveRowGeneratingFunctionsPF B :=
  hB.rightPreservesRowGeneratingFunctionsPF.rightPowers

theorem maoWangAdmissibleMatrix_listProduct_isLowerTriangular
    {Bs : List (LowerTriangularMatrix ℝ)}
    (hBs : ∀ B ∈ Bs, MaoWangAdmissibleMatrix B) :
    IsLowerTriangular (listProduct Bs) :=
  IsLowerTriangular.listProduct fun B hB => (hBs B hB).isLowerTriangular

theorem maoWangAdmissibleMatrix_listProduct_rightPreservesRowGeneratingFunctionsPF
    {Bs : List (LowerTriangularMatrix ℝ)}
    (hBs : ∀ B ∈ Bs, MaoWangAdmissibleMatrix B) :
    RightPreservesRowGeneratingFunctionsPF (listProduct Bs) :=
  RightPreservesRowGeneratingFunctionsPF.listProduct fun B hB =>
    (hBs B hB).rightPreservesRowGeneratingFunctionsPF

/-- Mao--Wang matrix-product criterion for right powers of an admissible
one-step factor. -/
abbrev maoWangMatrixProductRowGeneratingFunctionsPFStatement : Prop :=
  ∀ {M B : LowerTriangularMatrix ℝ},
    MaoWangAdmissibleMatrix B →
      ∀ r : ℕ,
        RowGeneratingFunctionsPF M →
          RowGeneratingFunctionsPF (mul M (pow B r))

/-- Mao--Wang matrix-product criterion for a finite product of admissible
one-step factors. -/
abbrev maoWangMatrixListProductRowGeneratingFunctionsPFStatement : Prop :=
  ∀ {M : LowerTriangularMatrix ℝ} {Bs : List (LowerTriangularMatrix ℝ)},
    (∀ B ∈ Bs, MaoWangAdmissibleMatrix B) →
      RowGeneratingFunctionsPF M →
        RowGeneratingFunctionsPF (mul M (listProduct Bs))

theorem maoWang_matrixProduct_rowGeneratingFunctions_pf :
    maoWangMatrixProductRowGeneratingFunctionsPFStatement := by
  intro M B hB r hM
  exact hB.rightPowersPreserveRowGeneratingFunctionsPF M r hM

theorem maoWang_matrixListProduct_rowGeneratingFunctions_pf :
    maoWangMatrixListProductRowGeneratingFunctionsPFStatement := by
  intro M Bs hBs hM
  exact maoWangAdmissibleMatrix_listProduct_rightPreservesRowGeneratingFunctionsPF hBs M hM

/-- Every row-generating polynomial has only real nonpositive roots, allowing
the zero polynomial. -/
def RowGeneratingFunctionsHaveOnlyNonposRoots
    (A : LowerTriangularMatrix ℝ) : Prop :=
  ∀ i : ℕ, HasOnlyNonposRoots (rowPolynomial A i)

theorem RowGeneratingFunctionsPF.hasOnlyNonposRoots
    {A : LowerTriangularMatrix ℝ} (hA : RowGeneratingFunctionsPF A) :
    RowGeneratingFunctionsHaveOnlyNonposRoots A := by
  intro i
  exact (hA.row i).hasOnlyNonposRoots

/-- Mao--Wang matrix-product criterion in the paper-facing root-location
form, for right powers of an admissible one-step factor. -/
abbrev maoWangMatrixProductRowGeneratingFunctionsNonposRootsStatement : Prop :=
  ∀ {M B : LowerTriangularMatrix ℝ},
    MaoWangAdmissibleMatrix B →
      ∀ r : ℕ,
        RowGeneratingFunctionsPF M →
          RowGeneratingFunctionsHaveOnlyNonposRoots (mul M (pow B r))

/-- Mao--Wang matrix-product criterion in the paper-facing root-location
form, for finite products of admissible one-step factors. -/
abbrev maoWangMatrixListProductRowGeneratingFunctionsNonposRootsStatement :
    Prop :=
  ∀ {M : LowerTriangularMatrix ℝ} {Bs : List (LowerTriangularMatrix ℝ)},
    (∀ B ∈ Bs, MaoWangAdmissibleMatrix B) →
      RowGeneratingFunctionsPF M →
        RowGeneratingFunctionsHaveOnlyNonposRoots (mul M (listProduct Bs))

theorem maoWang_matrixProduct_rowGeneratingFunctions_nonposRoots :
    maoWangMatrixProductRowGeneratingFunctionsNonposRootsStatement := by
  intro M B hB r hM
  exact (maoWang_matrixProduct_rowGeneratingFunctions_pf hB r hM).hasOnlyNonposRoots

theorem maoWang_matrixListProduct_rowGeneratingFunctions_nonposRoots :
    maoWangMatrixListProductRowGeneratingFunctionsNonposRootsStatement := by
  intro M Bs hBs hM
  exact (maoWang_matrixListProduct_rowGeneratingFunctions_pf hBs hM).hasOnlyNonposRoots

/-- Rowwise Brenti inverse statement for the falling-factorial coefficient
matrix. -/
abbrev fallingFactorialMatrixReflectsRowGeneratingFunctionsNonposRootsStatement :
    Prop :=
  ∀ {M : LowerTriangularMatrix ℝ},
    RowGeneratingFunctionsHaveOnlyNonposRoots (mul M fallingFactorialMatrix) →
      RowGeneratingFunctionsHaveOnlyNonposRoots M

theorem RowGeneratingFunctionsHaveOnlyNonposRoots.of_mul_fallingFactorialMatrix
    {M : LowerTriangularMatrix ℝ}
    (hM : RowGeneratingFunctionsHaveOnlyNonposRoots (mul M fallingFactorialMatrix)) :
    RowGeneratingFunctionsHaveOnlyNonposRoots M := by
  intro i
  have hrow := hM i
  rw [rowPolynomial_mul_fallingFactorialMatrix] at hrow
  exact brentiFallingFactorial hrow

theorem fallingFactorialMatrix_reflectsRowGeneratingFunctionsNonposRoots :
    fallingFactorialMatrixReflectsRowGeneratingFunctionsNonposRootsStatement := by
  intro M hM
  exact hM.of_mul_fallingFactorialMatrix

end LowerTriangularMatrix

end

end RealRooted
