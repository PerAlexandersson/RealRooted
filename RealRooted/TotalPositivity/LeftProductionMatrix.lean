module

import RealRooted.AissenSchoenbergWhitney
public import RealRooted.LowerTriangularMatrix
public import RealRooted.ToeplitzFin
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.DiagonalTail
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Border
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.FinTruncation
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul

/-!
# Left production matrices

We formalize the finite-matrix part of Chen--Fu--Ruan's theorem on left production
matrices.  Their factorization writes a lower-triangular array as a product of shifted
copies of its left production matrix.  The key identity identifies every finite Toeplitz
truncation of a row with the transpose of a submatrix of such a product.

Reference: X. Chen, L. Fu, and J. Ruan, *A unified planar network
approach to total positivity of combinatorial matrices and real-rootedness of
polynomials*, Theorems 1.3 and 1.4, arXiv:2512.08369.
-/

@[expose] public section

open Matrix Polynomial

noncomputable section

namespace RealRooted

/-- The entrywise recursion equivalent to the left-production factorization
`A = Q · diag(I₁, Q) · diag(I₂, Q) · ⋯`.

The interval in the recursion is empty when `n < k`; the final clause records that the
resulting array is lower triangular. -/
def IsLeftProductionArray (q a : ℕ → ℕ → ℝ) : Prop :=
  (∀ n, a n 0 = q n 0) ∧
    (∀ n k, a (n + 1) (k + 1) =
      ∑ j ∈ Finset.Icc k n, q (n + 1) (j + 1) * a j k) ∧
    LowerTriangularMatrix.IsLowerTriangular a

/-- The leading principal truncation of an infinite matrix. -/
def leadingTruncation (q : ℕ → ℕ → ℝ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.submatrix (Matrix.of fun i j => q i j) Fin.val Fin.val

/-- Every finite leading principal truncation of `q` is totally nonnegative. -/
def HasTotallyNonnegativeLeadingTruncations (q : ℕ → ℕ → ℝ) : Prop :=
  ∀ N, (leadingTruncation q N).IsTotallyNonneg

namespace IsLeftProductionArray

variable {q a : ℕ → ℕ → ℝ}

/-- The zeroth-column clause of a left-production recursion. -/
theorem zero (h : IsLeftProductionArray q a) (n : ℕ) : a n 0 = q n 0 :=
  h.1 n

/-- The successor-column clause of a left-production recursion. -/
theorem succ (h : IsLeftProductionArray q a) (n k : ℕ) :
    a (n + 1) (k + 1) =
      ∑ j ∈ Finset.Icc k n, q (n + 1) (j + 1) * a j k :=
  h.2.1 n k

/-- A left-production array is lower triangular. -/
theorem lower (h : IsLeftProductionArray q a) :
    LowerTriangularMatrix.IsLowerTriangular a :=
  h.2.2

end IsLeftProductionArray

namespace LeftProductionMatrix

/-- Adjoin an identity block before an infinite matrix. -/
def prefixIdentity (A : Matrix ℕ ℕ ℝ) (s : ℕ) : Matrix ℕ ℕ ℝ :=
  fun i j =>
    if _hi : i < s then
      if i = j then 1 else 0
    else if _hj : j < s then 0 else A (i - s) (j - s)

/-- An identity prefix of length zero does not change a matrix. -/
@[simp]
theorem prefixIdentity_zero (A : Matrix ℕ ℕ ℝ) : prefixIdentity A 0 = A := by
  ext i j
  simp [prefixIdentity]

/-- Entries in the identity prefix agree with the identity matrix. -/
@[simp]
theorem prefixIdentity_apply_lt (A : Matrix ℕ ℕ ℝ) {s i j : ℕ} (hi : i < s) :
    prefixIdentity A s i j = if i = j then 1 else 0 := by
  simp [prefixIdentity, hi]

/-- Entries crossing from the matrix block to the identity prefix vanish. -/
@[simp]
theorem prefixIdentity_apply_cross (A : Matrix ℕ ℕ ℝ) {s i j : ℕ}
    (hi : s ≤ i) (hj : j < s) :
    prefixIdentity A s i j = 0 := by
  simp [prefixIdentity, not_lt.mpr hi, hj]

/-- Entries after the identity prefix are shifted entries of the original matrix. -/
@[simp]
theorem prefixIdentity_apply_ge (A : Matrix ℕ ℕ ℝ) {s i j : ℕ}
    (hi : s ≤ i) (hj : s ≤ j) :
    prefixIdentity A s i j = A (i - s) (j - s) := by
  simp [prefixIdentity, not_lt.mpr hi, not_lt.mpr hj]

/-- Every finite truncation remains totally nonnegative after adjoining an identity
prefix. -/
theorem prefixIdentity_fin_isTotallyNonneg {A : Matrix ℕ ℕ ℝ}
    (hA : A.IsTotallyNonneg) (s N : ℕ) :
    ((prefixIdentity A s).submatrix (fun i : Fin N => i.val)
      (fun j : Fin N => j.val)).IsTotallyNonneg := by
  induction N generalizing s with
  | zero =>
      have heq : (prefixIdentity A s).submatrix
          (fun i : Fin 0 => i.val) (fun j : Fin 0 => j.val) =
          (1 : Matrix (Fin 0) (Fin 0) ℝ) := Subsingleton.elim _ _
      rw [heq]
      exact Matrix.IsTotallyNonneg.one
  | succ N ih =>
      cases s with
      | zero =>
          simpa using hA.submatrix Fin.val_strictMono Fin.val_strictMono
      | succ s =>
          let B := (prefixIdentity A (s + 1)).submatrix
            (fun i : Fin (N + 1) => i.val) (fun j : Fin (N + 1) => j.val)
          apply Matrix.IsTotallyNonneg.of_zero_border B
          · intro j
            simp [B, prefixIdentity]
          · intro i
            simp [B, prefixIdentity]
          · simp [B, prefixIdentity]
          · have htrail : B.submatrix Fin.succ Fin.succ =
                (prefixIdentity A s).submatrix
                  (fun i : Fin N => i.val) (fun j : Fin N => j.val) := by
              ext i j
              simp [B, prefixIdentity]
            rw [htrail]
            exact ih s

/-- The shifted block `diag(I_s, Q_n, I, I, ...)` used in a left-production
product. -/
def factor (q : ℕ → ℕ → ℝ) (n s : ℕ) : LowerTriangularMatrix ℝ :=
  prefixIdentity
    (Matrix.diagonalTail 1 (leadingTruncation q n)) s

/-- Entries in the active block of a shifted production factor come from `q`. -/
@[simp]
theorem factor_apply_active (q : ℕ → ℕ → ℝ) (n s i j : ℕ)
    (hi₀ : s ≤ i) (hi₁ : i ≤ s + n) (hj₀ : s ≤ j) (hj₁ : j ≤ s + n) :
    factor q n s i j = q (i - s) (j - s) := by
  rw [factor, prefixIdentity_apply_ge _ hi₀ hj₀]
  rw [Matrix.diagonalTail_apply_of_lt 1 _ (by lia) (by lia)]
  rfl

/-- Entries after the active block agree with the identity matrix. -/
@[simp]
theorem factor_apply_tail (q : ℕ → ℕ → ℝ) (n s i j : ℕ)
    (hi : s + n < i) :
    factor q n s i j = if i = j then 1 else 0 := by
  by_cases hj : j < s
  · have hij : i ≠ j := by lia
    simp [factor, prefixIdentity, hj, hij]
  · rw [factor, prefixIdentity_apply_ge _ (by lia) (not_lt.mp hj)]
    have htail : ¬i - s < n + 1 := by lia
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonalTail, htail]
    · have hsub : i - s ≠ j - s := by
        intro h
        apply hij
        lia
      simp [Matrix.diagonalTail, htail, hij, hsub]

/-- Rows before the active block agree with the identity matrix. -/
@[simp]
theorem factor_apply_prefix (q : ℕ → ℕ → ℝ) (n s i j : ℕ)
    (hi : i < s) :
    factor q n s i j = if i = j then 1 else 0 := by
  exact prefixIdentity_apply_lt _ hi

/-- Columns before the active block agree with the identity matrix. -/
@[simp]
theorem factor_apply_before (q : ℕ → ℕ → ℝ) (n s i j : ℕ)
    (hj : j < s) :
    factor q n s i j = if i = j then 1 else 0 := by
  by_cases hi : i < s
  · exact factor_apply_prefix q n s i j hi
  · have hij : i ≠ j := by lia
    simp [factor, prefixIdentity, hi, hj, hij]

/-- Entries crossing from the active block to its identity tail vanish. -/
@[simp]
theorem factor_apply_active_tail (q : ℕ → ℕ → ℝ) (n s i j : ℕ)
    (hi₀ : s ≤ i) (hi₁ : i ≤ s + n) (hj : s + n < j) :
    factor q n s i j = 0 := by
  rw [factor, prefixIdentity_apply_ge _ hi₀ (by lia)]
  have hactive : i - s < n + 1 := by lia
  have htail : ¬j - s < n + 1 := by lia
  simp [Matrix.diagonalTail, hactive, htail]

/-- A shifted production factor is lower triangular when `q` is. -/
theorem factor_isLowerTriangular
    (hq : LowerTriangularMatrix.IsLowerTriangular q) (n s : ℕ) :
    LowerTriangularMatrix.IsLowerTriangular (factor q n s) := by
  intro i j hij
  by_cases hi : i < s
  · simp [factor_apply_prefix q n s i j hi, hij.ne]
  by_cases hj : j < s
  · exact prefixIdentity_apply_cross _ (not_lt.mp hi) hj
  by_cases hin : i ≤ s + n
  · by_cases hjn : j ≤ s + n
    · rw [factor_apply_active q n s i j (not_lt.mp hi) hin (not_lt.mp hj) hjn]
      exact hq (by lia)
    · exact factor_apply_active_tail q n s i j (not_lt.mp hi) hin (not_le.mp hjn)
  · simp [factor_apply_tail q n s i j (not_le.mp hin), hij.ne]

/-- The right-associated product of `len` consecutive shifted copies of `Q_n`,
starting at position `s`. -/
def product (q : ℕ → ℕ → ℝ) (n s : ℕ) : ℕ → LowerTriangularMatrix ℝ
  | 0 => LowerTriangularMatrix.identity
  | len + 1 => LowerTriangularMatrix.mul (factor q n s) (product q n (s + 1) len)

/-- The empty production product is the identity. -/
@[simp]
theorem product_zero (q : ℕ → ℕ → ℝ) (n s : ℕ) :
    product q n s 0 = LowerTriangularMatrix.identity :=
  rfl

/-- A nonempty production product begins with its first shifted factor. -/
@[simp]
theorem product_succ (q : ℕ → ℕ → ℝ) (n s len : ℕ) :
    product q n s (len + 1) =
      LowerTriangularMatrix.mul (factor q n s) (product q n (s + 1) len) :=
  rfl

/-- Production products are lower triangular. -/
theorem product_isLowerTriangular
    (hq : LowerTriangularMatrix.IsLowerTriangular q) (n s len : ℕ) :
    LowerTriangularMatrix.IsLowerTriangular (product q n s len) := by
  induction len generalizing s with
  | zero => exact LowerTriangularMatrix.IsLowerTriangular.identity
  | succ len ih =>
      exact LowerTriangularMatrix.IsLowerTriangular.mul
        (factor_isLowerTriangular hq n s)

/-- Finite leading truncation commutes with the finite multiplication of
lower-triangular matrices. -/
theorem truncation_mul {A B : LowerTriangularMatrix ℝ}
    (hA : LowerTriangularMatrix.IsLowerTriangular A)
    (hB : LowerTriangularMatrix.IsLowerTriangular B) (N : ℕ) :
    Matrix.submatrix (Matrix.of (LowerTriangularMatrix.mul A B)) (Fin.val : Fin N → ℕ)
        (Fin.val : Fin N → ℕ) =
      Matrix.submatrix (Matrix.of A) (Fin.val : Fin N → ℕ) (Fin.val : Fin N → ℕ) *
        Matrix.submatrix (Matrix.of B) (Fin.val : Fin N → ℕ) (Fin.val : Fin N → ℕ) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, LowerTriangularMatrix.mul_apply,
    Matrix.mul_apply]
  change (∑ k ∈ Finset.Icc j.val i.val, A i.val k * B k j.val) =
    ∑ k : Fin N, (fun m : ℕ => A i.val m * B m j.val) k.val
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => A i.val m * B m j.val) N]
  have hsubset : Finset.Icc j.val i.val ⊆ Finset.range N := by
    intro k hk
    exact Finset.mem_range.mpr ((Finset.mem_Icc.mp hk).2.trans_lt i.isLt)
  rw [← Finset.sum_subset hsubset]
  intro k hkRange hkIcc
  by_cases hkj : k < j.val
  · rw [hB hkj, mul_zero]
  · have hik : i.val < k := by
      by_contra hik
      exact hkIcc (Finset.mem_Icc.mpr ⟨not_lt.mp hkj, not_lt.mp hik⟩)
    rw [hA hik, zero_mul]

/-- Every finite truncation of a shifted production factor is totally nonnegative. -/
theorem factor_fin_isTotallyNonneg
    (hq : HasTotallyNonnegativeLeadingTruncations q) (n s N : ℕ) :
    (Matrix.submatrix (Matrix.of (factor q n s)) (Fin.val : Fin N → ℕ)
      (Fin.val : Fin N → ℕ)).IsTotallyNonneg := by
  have htail : (Matrix.diagonalTail 1 (leadingTruncation q n)).IsTotallyNonneg :=
    (hq n).diagonalTail zero_le_one
  exact prefixIdentity_fin_isTotallyNonneg htail s N

/-- Every finite truncation of a left-production product is totally nonnegative. -/
theorem product_fin_isTotallyNonneg
    (hqLower : LowerTriangularMatrix.IsLowerTriangular q)
    (hq : HasTotallyNonnegativeLeadingTruncations q)
    (n s len N : ℕ) :
    (Matrix.submatrix (Matrix.of (product q n s len)) (Fin.val : Fin N → ℕ)
      (Fin.val : Fin N → ℕ)).IsTotallyNonneg := by
  induction len generalizing s with
  | zero =>
      have heq : Matrix.submatrix (Matrix.of (product q n s 0)) (Fin.val : Fin N → ℕ)
          (Fin.val : Fin N → ℕ) =
          (1 : Matrix (Fin N) (Fin N) ℝ) := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.of_apply, product_zero,
          LowerTriangularMatrix.identity_apply, Matrix.one_apply]
        by_cases hij : i = j
        · subst j
          simp
        · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
          simp [hij, hval]
      rw [heq]
      exact Matrix.IsTotallyNonneg.one
  | succ len ih =>
      rw [product_succ, truncation_mul (factor_isLowerTriangular hqLower n s)
        (product_isLowerTriangular hqLower n (s + 1) len)]
      exact (factor_fin_isTotallyNonneg hq n s N).mul (ih (s + 1))

/-- Before its first active position, a production product is the identity. -/
private theorem product_apply_prefix (q : ℕ → ℕ → ℝ) (n s len i j : ℕ)
    (hj : j < s) :
    product q n s len i j = if i = j then 1 else 0 := by
  induction len generalizing s i j with
  | zero => rfl
  | succ len ih =>
      rw [product_succ, LowerTriangularMatrix.mul_apply]
      by_cases hji : j ≤ i
      · rw [Finset.sum_eq_single j]
        · rw [factor_apply_before q n s i j hj,
            ih (s + 1) j j (by lia)]
          simp
        · intro k hk hkj
          rw [ih (s + 1) k j (by lia)]
          simp [hkj]
        · exact fun h => (h (Finset.mem_Icc.mpr ⟨le_rfl, hji⟩)).elim
      · have hempty : Finset.Icc j i = ∅ := Finset.Icc_eq_empty (by lia)
        rw [hempty]
        simp [Nat.ne_of_lt (Nat.lt_of_not_ge hji)]

/-- A production product starting at its active row gives the recursively generated
array entry. -/
private theorem product_apply_from_start
    (ha : IsLeftProductionArray q a) (N n s len j : ℕ) (hnN : n ≤ N)
    (hsj : s ≤ j) (hjlen : j < s + len) :
    product q N s len (n + s) j = a n (j - s) := by
  induction len generalizing n s j with
  | zero => exfalso; lia
  | succ len ih =>
      rw [product_succ, LowerTriangularMatrix.mul_apply]
      by_cases hjs : j = s
      · subst j
        rw [Finset.sum_eq_single s]
        · simp [factor_apply_active q N s (n + s) s (by lia) (by lia),
            product_apply_prefix q N (s + 1) len s s (by lia), ha.zero]
        · intro k hk hks
          rw [product_apply_prefix q N (s + 1) len k s (by lia)]
          simp [hks]
        · simp
      · have hsj' : s + 1 ≤ j := by lia
        have hjlen' : j < s + 1 + len := by lia
        by_cases hjn : j ≤ n + s
        · have hn : 0 < n := by lia
          have hrec := ha.succ (n - 1) (j - s - 1)
          have hnEq : n - 1 + 1 = n := by lia
          have hkEq : j - s - 1 + 1 = j - s := by lia
          rw [hnEq, hkEq] at hrec
          rw [hrec]
          symm
          refine Finset.sum_bij (fun k _ => k + s + 1) ?_ ?_ ?_ ?_
          · intro k hk
            have hkj := Finset.mem_Icc.mp hk
            exact Finset.mem_Icc.mpr ⟨by lia, by lia⟩
          · intro k₁ hk₁ k₂ hk₂ heq
            lia
          · intro k hk
            have hkj := Finset.mem_Icc.mp hk
            refine ⟨k - s - 1, Finset.mem_Icc.mpr ⟨by lia, by lia⟩, by lia⟩
          · intro k hk
            have hkj := Finset.mem_Icc.mp hk
            rw [factor_apply_active q N s (n + s) (k + s + 1)
              (by lia) (by lia) (by lia) (by lia)]
            have htail : product q N (s + 1) len (k + s + 1) j =
                a k (j - s - 1) := by
              simpa [Nat.add_assoc, Nat.sub_sub] using
                ih k (s + 1) j (by lia) (by lia) hjlen'
            rw [htail]
            congr 2 <;> lia
        · have hempty : Finset.Icc j (n + s) = ∅ := Finset.Icc_eq_empty (by lia)
          rw [hempty, Finset.sum_empty]
          exact (ha.lower (by lia)).symm

/-- Entrywise form of Chen--Fu--Ruan's Theorem 1.4. -/
private theorem product_apply_of_isLeftProductionArray
    (ha : IsLeftProductionArray q a) (n s len i j : ℕ)
    (hsi : s ≤ i) (hij : i ≤ j) (hjlen : j < s + len) :
    product q n s len (n + i) j = a n (j - i) := by
  induction len generalizing s i j with
  | zero => exfalso; lia
  | succ len ih =>
      by_cases his : i = s
      · subst i
        exact product_apply_from_start ha n n s (len + 1) j le_rfl hij hjlen
      · have hsi' : s + 1 ≤ i := by lia
        by_cases hjrow : j ≤ n + i
        · rw [product_succ, LowerTriangularMatrix.mul_apply]
          rw [Finset.sum_eq_single (n + i)]
          · rw [factor_apply_tail q n s (n + i) (n + i) (by lia)]
            simp only [ite_true, one_mul]
            exact ih (s + 1) i j hsi' hij (by lia)
          · intro k hk hki
            have hfactor : factor q n s (n + i) k = 0 := by
              rw [factor_apply_tail q n s (n + i) k (by lia)]
              exact ite_eq_right (Ne.symm hki)
            rw [hfactor, zero_mul]
          · intro hnot
            exact False.elim (hnot (Finset.mem_Icc.mpr ⟨hjrow, le_rfl⟩))
        · rw [product_succ, LowerTriangularMatrix.mul_apply]
          have hempty : Finset.Icc j (n + i) = ∅ := Finset.Icc_eq_empty (by lia)
          rw [hempty, Finset.sum_empty]
          exact (ha.lower (by lia)).symm

/-- Entries strictly before the moving source position vanish. -/
private theorem product_apply_eq_zero_of_lt
    (q : ℕ → ℕ → ℝ) (n s len i j : ℕ)
    (hsi : s ≤ i) (hji : j < i) (hilen : i < s + len) :
    product q n s len (n + i) j = 0 := by
  induction len generalizing s i j with
  | zero => exfalso; lia
  | succ len ih =>
      by_cases his : i = s
      · subst i
        simpa [show n + s ≠ j by lia] using
          product_apply_prefix q n s (len + 1) (n + s) j hji
      · have hsi' : s + 1 ≤ i := by lia
        rw [product_succ, LowerTriangularMatrix.mul_apply]
        rw [Finset.sum_eq_single (n + i)]
        · rw [factor_apply_tail q n s (n + i) (n + i) (by lia)]
          simp only [ite_true, one_mul]
          exact ih (s + 1) i j hsi' hji (by lia)
        · intro k hk hki
          have hfactor : factor q n s (n + i) k = 0 := by
            rw [factor_apply_tail q n s (n + i) k (by lia)]
            exact ite_eq_right (Ne.symm hki)
          rw [hfactor, zero_mul]
        · intro hnot
          exact False.elim (hnot (Finset.mem_Icc.mpr ⟨by lia, le_rfl⟩))

/-- The finite product in Theorem 1.4, of order `n + r + 1`. -/
def finiteProduct (q : ℕ → ℕ → ℝ) (n r : ℕ) :
    Matrix (Fin (n + r + 1)) (Fin (n + r + 1)) ℝ :=
  Matrix.submatrix (Matrix.of (product q n 0 (r + 1))) Fin.val Fin.val

/-- The finite product in Theorem 1.4 is totally nonnegative. -/
theorem finiteProduct_isTotallyNonneg
    (hqLower : LowerTriangularMatrix.IsLowerTriangular q)
    (hq : HasTotallyNonnegativeLeadingTruncations q) (n r : ℕ) :
    (finiteProduct q n r).IsTotallyNonneg := by
  exact product_fin_isTotallyNonneg hqLower hq n 0 (r + 1) (n + r + 1)

/-- The leading Toeplitz matrix of row `n`, transposed, is the indicated submatrix of
the finite left-production product.  This is Chen--Fu--Ruan, Theorem 1.4. -/
theorem toeplitzFin_transpose_eq_submatrix_finiteProduct
    (ha : IsLeftProductionArray q a) (n r : ℕ) :
    (toeplitzFin (a n) r).transpose =
      (finiteProduct q n r).submatrix
        (fun i : Fin (r + 1) => ⟨n + i.val, by lia⟩)
        (fun j : Fin (r + 1) => ⟨j.val, by lia⟩) := by
  ext i j
  simp only [Matrix.transpose_apply, toeplitzFin_apply, Matrix.submatrix_apply,
    finiteProduct]
  by_cases hij : i ≤ j
  · rw [ite_eq_left hij]
    exact (product_apply_of_isLeftProductionArray ha n 0 (r + 1) i.val j.val
      (by simp) (Fin.le_def.mp hij) (by lia)).symm
  · rw [ite_eq_right hij]
    have hji : j.val < i.val := by lia
    exact (product_apply_eq_zero_of_lt q n 0 (r + 1) i.val j.val
      (by simp) hji (by lia)).symm

/-- Rows generated by a totally nonnegative left production matrix are
Pólya-frequency sequences. -/
theorem isPolyaFreqSeq_of_isLeftProductionArray
    (ha : IsLeftProductionArray q a)
    (hqLower : LowerTriangularMatrix.IsLowerTriangular q)
    (hq : HasTotallyNonnegativeLeadingTruncations q) (n : ℕ) :
    IsPolyaFreqSeq (a n) := by
  rw [IsPolyaFreqSeq]
  apply Matrix.IsTotallyNonneg.of_fin_truncations _ (fun r => toeplitzFin (a n) r)
  · intro r i j
    rfl
  · intro r
    have hproduct := finiteProduct_isTotallyNonneg hqLower hq n r
    have hsub :
        ((finiteProduct q n r).submatrix
          (fun i : Fin (r + 1) => ⟨n + i.val, by lia⟩)
          (fun j : Fin (r + 1) => ⟨j.val, by lia⟩)).IsTotallyNonneg :=
      hproduct.submatrix (fun _ _ h => by lia) (fun _ _ h => by lia)
    rw [← toeplitzFin_transpose_eq_submatrix_finiteProduct ha n r] at hsub
    simpa using hsub.toRect.transpose.toSquare

/-- The polynomial whose coefficients are row `n` of a left-production array. -/
def rowPolynomial (a : ℕ → ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  LowerTriangularMatrix.rowPolynomial a n

/-- The coefficient of a row polynomial is the corresponding array entry. -/
theorem coeff_rowPolynomial (ha : IsLeftProductionArray q a) (n k : ℕ) :
    (rowPolynomial a n).coeff k = a n k :=
  LowerTriangularMatrix.coeff_rowPolynomial ha.lower n k

/-- Row polynomials generated by a totally nonnegative left production matrix split
and all their roots are nonpositive. -/
theorem rowPolynomial_splits_and_roots_nonpos_of_isLeftProductionArray
    (ha : IsLeftProductionArray q a)
    (hqLower : LowerTriangularMatrix.IsLowerTriangular q)
    (hq : HasTotallyNonnegativeLeadingTruncations q) (n : ℕ) :
    (rowPolynomial a n).Splits ∧
      ∀ r ∈ (rowPolynomial a n).roots, r ≤ 0 := by
  apply aissenSchoenbergWhitneyForward
  have hcoeff : (rowPolynomial a n).coeff = a n := by
    funext k
    exact coeff_rowPolynomial ha n k
  rw [hcoeff]
  exact isPolyaFreqSeq_of_isLeftProductionArray ha hqLower hq n

end LeftProductionMatrix

end RealRooted
