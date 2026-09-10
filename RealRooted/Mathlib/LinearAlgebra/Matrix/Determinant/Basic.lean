module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace Matrix
variable {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]

-- TODO: Replace `det_zero`
@[simp] lemma det_zero' [Nonempty n] : (0 : Matrix n n R).det = 0 := det_zero ‹_›

/-- The Leibniz formula for a determinant, with rows indexed before columns. -/
theorem det_apply_row (M : Matrix n n R) :
    M.det = ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  rfl

/-- The alternating vector of maximal row-deletion minors of a rectangular matrix lies in the
kernel of its transpose. This is the Laplace expansion of the matrix obtained by adjoining a
duplicate of any chosen column. -/
theorem transpose_mulVec_alternating_det_submatrix_succAbove {q : ℕ}
    (B : Matrix (Fin (q + 1)) (Fin q) R) :
    B.transpose.mulVec (fun i => (-1 : R) ^ (i : ℕ) *
      (B.submatrix i.succAbove id).det) = 0 := by
  ext j
  let A : Matrix (Fin (q + 1)) (Fin (q + 1)) R :=
    fun i => Fin.cases (B i j) (B i)
  have hminor (i : Fin (q + 1)) :
      A.submatrix i.succAbove Fin.succ = B.submatrix i.succAbove id := rfl
  have hne : (0 : Fin (q + 1)) ≠ j.succ := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
  have hdet : A.det = 0 := det_zero_of_column_eq hne (by
    intro i
    rfl)
  rw [det_succ_column_zero] at hdet
  simp_rw [hminor] at hdet
  simpa [mulVec, dotProduct, A, mul_comm, mul_left_comm, mul_assoc] using hdet

/-- Expanding a matrix with constant first column after adjacent row subtraction. -/
theorem det_eq_det_adjacentRowDiff_of_firstColumn_eq_one {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hA : ∀ i, A i 0 = 1) :
    A.det =
      (Matrix.of fun (i j : Fin n) =>
        A i.succ j.succ - A i.castSucc j.succ).det := by
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    fun i j => Fin.cases (A 0 j)
      (fun k => A k.succ j - A k.castSucc j) i
  have hdet : A.det = B.det := by
    apply det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1)
    · intro j
      simp [B]
    · intro i j
      simp [B]
  rw [hdet, det_succ_column_zero, Fin.sum_univ_succ]
  have hminor :
      B.submatrix Fin.succ Fin.succ =
        Matrix.of fun (i j : Fin n) =>
          A i.succ j.succ - A i.castSucc j.succ := by
    ext i j
    rfl
  simpa [B, hA] using congrArg Matrix.det hminor

/-- A submatrix with a noninjective column selector has zero determinant. -/
theorem det_submatrix_eq_zero_of_not_injective_right
    {R m κ q : Type*} [CommRing R] [DecidableEq q] [Fintype q]
    (L : Matrix m κ R) (rows : q → m) (f : q → κ)
    (hf : ¬ Function.Injective f) :
    (L.submatrix rows f).det = 0 := by
  obtain ⟨i, j, hfij, hij⟩ := Function.not_injective_iff.mp hf
  apply Matrix.det_zero_of_column_eq hij
  intro k
  simp only [Matrix.submatrix_apply]
  rw [hfij]

/-- Laplace expansion when the last column is zero above its final entry. -/
theorem det_eq_last_apply_mul_det_castSucc_of_above_eq_zero
    {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hzero : ∀ i : Fin n, A i.castSucc (Fin.last n) = 0) :
    A.det = A (Fin.last n) (Fin.last n) *
      (A.submatrix Fin.castSucc Fin.castSucc).det := by
  have hdet := Matrix.det_succ_column A (Fin.last n)
  rw [Fin.sum_univ_succAbove _ (Fin.last n)] at hdet
  simp only [Fin.succAbove_last] at hdet
  have hsum :
      (∑ i : Fin n,
        (-1 : R) ^ ((i.castSucc : Fin (n + 1)) + (Fin.last n : ℕ)) *
          A i.castSucc (Fin.last n) *
            (A.submatrix i.castSucc.succAbove Fin.castSucc).det) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero i]
    ring
  rw [hsum, add_zero] at hdet
  have heven : (-1 : R) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) = 1 := by
    rw [show (Fin.last n : ℕ) + (Fin.last n : ℕ) = n + n by simp,
      ← two_mul n, pow_mul]
    simp
  rw [heven, one_mul] at hdet
  exact hdet

section BorderedDeterminants

variable {R : Type*} [CommRing R]

open scoped BigOperators

/-- Adjoin a final column and a final row to a square matrix. -/
def border {q : ℕ} (A : Matrix (Fin q) (Fin q) R)
    (b x : Fin q → R) (a : R) : Matrix (Fin (q + 1)) (Fin (q + 1)) R :=
  fun i j ↦ Fin.lastCases (motive := fun _ ↦ Fin (q + 1) → R)
    (Fin.snoc x a) (fun k ↦ Fin.snoc (A k) (b k)) i j

omit [CommRing R] in
@[simp] lemma border_castSucc_castSucc {q : ℕ}
    (A : Matrix (Fin q) (Fin q) R) (b x : Fin q → R) (a : R)
    (i j : Fin q) :
    border A b x a i.castSucc j.castSucc = A i j := by
  simp [border]

omit [CommRing R] in
@[simp] lemma border_castSucc_last {q : ℕ}
    (A : Matrix (Fin q) (Fin q) R) (b x : Fin q → R) (a : R)
    (i : Fin q) :
    border A b x a i.castSucc (Fin.last q) = b i := by
  simp [border]

omit [CommRing R] in
@[simp] lemma border_last_castSucc {q : ℕ}
    (A : Matrix (Fin q) (Fin q) R) (b x : Fin q → R) (a : R)
    (j : Fin q) :
    border A b x a (Fin.last q) j.castSucc = x j := by
  simp [border]

omit [CommRing R] in
@[simp] lemma border_last_last {q : ℕ}
    (A : Matrix (Fin q) (Fin q) R) (b x : Fin q → R) (a : R) :
    border A b x a (Fin.last q) (Fin.last q) = a := by
  simp [border]

/-- A bordered determinant when the new row is given in the old row basis. -/
private theorem det_border_of_vecMul_eq {q : ℕ}
    (A : Matrix (Fin q) (Fin q) R) (b x c : Fin q → R) (a : R)
    (hx : c ᵥ* A = x) :
    (border A b x a).det = A.det * (a - dotProduct c b) := by
  let E := border A b 0 1
  let d : Fin (q + 1) → R := Fin.snoc c (a - dotProduct c b)
  have hrow : ∑ k, d k • E k = Fin.snoc x a := by
    funext j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · rw [Fin.sum_univ_castSucc]
      simp [d, E, dotProduct]
    · rw [Fin.sum_univ_castSucc]
      simpa [d, E, Matrix.vecMul, dotProduct] using congrFun hx j
  have hupdate : E.updateRow (Fin.last q) (∑ k, d k • E k) = border A b x a := by
    ext i j
    by_cases hi : i = Fin.last q
    · subst i
      simp [hrow, E, border]
    · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      simp [E, border]
  have hdetE : E.det = A.det := by
    have hminor : E.submatrix Fin.castSucc Fin.castSucc = A := by
      ext i j
      simp [E]
    rw [Matrix.det_succ_row E (Fin.last q), Fin.sum_univ_castSucc]
    simp [E, Fin.succAbove_last, hminor]
  rw [← hupdate, Matrix.det_updateRow_sum, hdetE, smul_eq_mul]
  simp [d]
  ring

/-- Replacing an old row of a bordered matrix by the new coordinate row
extracts the corresponding coefficient of the adjoined row. -/
private theorem det_border_update_old_row {q : ℕ}
    (A : Matrix (Fin q) (Fin q) R) (r0 : Fin q)
    (b y d : Fin q → R) (beta : R) (hy : d ᵥ* A = y) :
    ((border A b y beta).updateRow r0.castSucc
      (Fin.snoc 0 1)).det = -d r0 * A.det := by
  let E := border A b 0 1
  let r : Fin (q + 1) := r0.castSucc
  let z : Fin (q + 1) := Fin.last q
  let sigma : Equiv.Perm (Fin (q + 1)) := Equiv.swap r z
  let coeff : Fin (q + 1) → R :=
    Fin.snoc d (beta - dotProduct d b)
  let H := E.submatrix sigma id
  let f : Fin (q + 1) → R := coeff ∘ sigma
  have hcoeff : ∑ k, coeff k • E k = Fin.snoc y beta := by
    funext j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · rw [Fin.sum_univ_castSucc]
      simp [coeff, E, dotProduct]
    · rw [Fin.sum_univ_castSucc]
      simpa [coeff, E, Matrix.vecMul, dotProduct] using congrFun hy j
  have hrow : ∑ k, f k • H k = Fin.snoc y beta := by
    calc
      ∑ k, f k • H k = ∑ k, coeff (sigma k) • E (sigma k) := by
        rfl
      _ = ∑ k, coeff k • E k :=
        Equiv.sum_comp sigma (fun k ↦ coeff k • E k)
      _ = Fin.snoc y beta := hcoeff
  have hrz : r ≠ z := by
    exact Fin.castSucc_ne_last r0
  have hupdate : H.updateRow z (∑ k, f k • H k) =
      (border A b y beta).updateRow r (Fin.snoc 0 1) := by
    ext i j
    by_cases hi : i = z
    · subst i
      rw [Matrix.updateRow_self, Matrix.updateRow_ne hrz.symm, hrow]
      simp [z, border]
    · by_cases hir : i = r
      · subst i
        rw [Matrix.updateRow_ne hrz, Matrix.updateRow_self]
        simp [H, sigma, E, border, z]
      · have hsigma : sigma i = i := by
          exact Equiv.swap_apply_of_ne_of_ne hir hi
        rw [Matrix.updateRow_ne hi, Matrix.updateRow_ne hir]
        change E (sigma i) j = border A b y beta i j
        rw [hsigma]
        obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        simp [E, border]
  have hdetE : E.det = A.det := by
    simpa [E] using
      det_border_of_vecMul_eq A b (0 : Fin q → R) 0 1 (by simp)
  have hdetH : H.det = -A.det := by
    change (E.submatrix sigma id).det = -A.det
    rw [Matrix.det_permute sigma E, Equiv.Perm.sign_swap hrz, hdetE]
    simp
  rw [← hupdate, Matrix.det_updateRow_sum, smul_eq_mul, hdetH]
  simp [f, coeff, sigma, r, z]

/-- The three-term bordered-minor identity used in Whitney elimination. -/
theorem det_border_plucker {q : ℕ}
    (A : Matrix (Fin q) (Fin q) R) (r0 : Fin q)
    (b x y c d : Fin q → R) (alpha beta : R)
    (hx : c ᵥ* A = x) (hy : d ᵥ* A = y) :
    A.det *
        ((border A b y beta).updateRow r0.castSucc
          (Fin.snoc x alpha)).det =
      (A.updateRow r0 x).det * (border A b y beta).det -
        (A.updateRow r0 y).det * (border A b x alpha).det := by
  let r : Fin (q + 1) := r0.castSucc
  let u : Fin (q + 1) → R := Fin.snoc c 0
  let e : Fin (q + 1) → R := Fin.snoc 0 1
  let By := border A b y beta
  have hlinear : ∑ k, u k • By k = Fin.snoc x (dotProduct c b) := by
    funext j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · rw [Fin.sum_univ_castSucc]
      simp [u, By, dotProduct]
    · rw [Fin.sum_univ_castSucc]
      simpa [u, By, Matrix.vecMul, dotProduct] using congrFun hx j
  have hrow : (∑ k, u k • By k) +
      (alpha - dotProduct c b) • e = Fin.snoc x alpha := by
    rw [hlinear]
    ext j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j <;>
      simp [e]
  have hupdate : By.updateRow r ((∑ k, u k • By k) +
      (alpha - dotProduct c b) • e) =
      By.updateRow r (Fin.snoc x alpha) := by
    rw [hrow]
  have hfirst : (By.updateRow r (∑ k, u k • By k)).det =
      c r0 * By.det := by
    rw [Matrix.det_updateRow_sum, smul_eq_mul]
    simp [u, r]
  have hsecond : (By.updateRow r e).det =
      -d r0 * A.det := by
    exact det_border_update_old_row A r0 b y d beta hy
  have hAx : (A.updateRow r0 x).det = c r0 * A.det := by
    have hsum : ∑ k, c k • A k = x := by
      rw [← Matrix.vecMul_eq_sum]
      exact hx
    rw [← hsum, Matrix.det_updateRow_sum, smul_eq_mul]
  have hAy : (A.updateRow r0 y).det = d r0 * A.det := by
    have hsum : ∑ k, d k • A k = y := by
      rw [← Matrix.vecMul_eq_sum]
      exact hy
    rw [← hsum, Matrix.det_updateRow_sum, smul_eq_mul]
  have hBx := det_border_of_vecMul_eq A b x c alpha hx
  rw [← hupdate, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    hfirst, hsecond, hAx, hAy, hBx]
  ring

end BorderedDeterminants

end Matrix
