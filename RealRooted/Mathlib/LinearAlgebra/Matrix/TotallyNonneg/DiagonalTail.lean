import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Border

/-!
# Positive diagonal tails of finite totally nonnegative matrices

This file extends a finite square matrix to natural-number indices by placing
a fixed scalar on the remaining diagonal and zero elsewhere.  Total
nonnegativity follows from finite isolated-last-coordinate extensions.
-/

namespace Matrix

open scoped BigOperators

/-- Extend a finite square matrix to natural-number indices with a constant
diagonal tail and zero cross terms. -/
def diagonalTail {R : Type*} [Zero R] {N : ℕ} (δ : R)
    (A : Matrix (Fin N) (Fin N) R) : Matrix ℕ ℕ R :=
  fun i j =>
    if hi : i < N then
      if hj : j < N then A ⟨i, hi⟩ ⟨j, hj⟩ else 0
    else if i = j then δ else 0

@[simp]
theorem diagonalTail_apply_of_lt {R : Type*} [Zero R] {N i j : ℕ}
    (δ : R) (A : Matrix (Fin N) (Fin N) R) (hi : i < N) (hj : j < N) :
    diagonalTail δ A i j = A ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [diagonalTail, hi, hj]

@[simp]
theorem diagonalTail_apply_diagonal {R : Type*} [Zero R] {N i : ℕ}
    (δ : R) (A : Matrix (Fin N) (Fin N) R)
    (hdiag : ∀ k, A k k = δ) :
    diagonalTail δ A i i = δ := by
  by_cases hi : i < N
  · simpa [diagonalTail, hi] using hdiag ⟨i, hi⟩
  · simp [diagonalTail, hi]

/-- A diagonal-tail extension is lower triangular when its finite block is. -/
theorem diagonalTail_apply_eq_zero_of_lt
    {R : Type*} [Zero R] {N : ℕ} {δ : R}
    {A : Matrix (Fin N) (Fin N) R}
    (hA : ∀ i j, i < j → A i j = 0) :
    ∀ i j, i < j → diagonalTail δ A i j = 0 := by
  intro i j hij
  by_cases hi : i < N
  · by_cases hj : j < N
    · rw [diagonalTail_apply_of_lt δ A hi hj]
      exact hA ⟨i, hi⟩ ⟨j, hj⟩ (by simpa using hij)
    · simp [diagonalTail, hi, hj]
  · simp [diagonalTail, hi, Nat.ne_of_lt hij]

/-- Every finite principal truncation of a diagonal-tail extension is totally
nonnegative. -/
theorem IsTotallyNonneg.diagonalTail_fin
    {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
    {N : ℕ} {δ : R} {A : Matrix (Fin N) (Fin N) R}
    (hδ : 0 ≤ δ) (hA : A.IsTotallyNonneg) (M : ℕ) :
    ((diagonalTail δ A).submatrix (fun i : Fin M => i.val)
      (fun j : Fin M => j.val)).IsTotallyNonneg := by
  induction M with
  | zero =>
      have heq :
          (diagonalTail δ A).submatrix (fun i : Fin 0 => i.val)
              (fun j : Fin 0 => j.val) =
            (0 : Matrix (Fin 0) (Fin 0) R) := by
        ext i
        exact Fin.elim0 i
      rw [heq]
      intro n rows cols hrows hcols
      have hn : n = 0 := by
        have hcard := Fintype.card_le_of_injective rows hrows.injective
        simpa using Nat.eq_zero_of_le_zero hcard
      subst n
      simp
  | succ M ih =>
      by_cases hMN : M + 1 ≤ N
      · have heq :
            (diagonalTail δ A).submatrix (fun i : Fin (M + 1) => i.val)
                (fun j : Fin (M + 1) => j.val) =
              A.submatrix (Fin.castLE hMN) (Fin.castLE hMN) := by
          ext i j
          have hiN : i.val < N := i.isLt.trans_le hMN
          have hjN : j.val < N := j.isLt.trans_le hMN
          simp only [Matrix.submatrix_apply, diagonalTail, dite_eq_left hiN,
            dite_eq_left hjN]
          rfl
        rw [heq]
        exact hA.submatrix (Fin.strictMono_castLE hMN)
          (Fin.strictMono_castLE hMN)
      · have hNM : N ≤ M := by lia
        have hMnot : ¬M < N := not_lt_of_ge hNM
        let B := (diagonalTail δ A).submatrix
          (fun i : Fin (M + 1) => i.val) (fun j : Fin (M + 1) => j.val)
        apply IsTotallyNonneg.of_zero_last_border B
        · intro j
          have hjM : j.val < M := j.isLt
          simp [B, diagonalTail, hMnot, Nat.ne_of_gt hjM]
        · intro i
          have hiM : i.val < M := i.isLt
          by_cases hiN : i.val < N
          · simp [B, diagonalTail, hiN, hMnot]
          · simp [B, diagonalTail, hiN, Nat.ne_of_lt hiM]
        · simpa [B, diagonalTail, hMnot] using hδ
        · have hlead : B.submatrix Fin.castSucc Fin.castSucc =
              (diagonalTail δ A).submatrix (fun i : Fin M => i.val)
                (fun j : Fin M => j.val) := by
            ext i j
            rfl
          rw [hlead]
          exact ih

/-- A finite totally nonnegative matrix remains totally nonnegative after
adjoining a nonnegative constant diagonal tail. -/
theorem IsTotallyNonneg.diagonalTail
    {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
    {N : ℕ} {δ : R} {A : Matrix (Fin N) (Fin N) R}
    (hδ : 0 ≤ δ) (hA : A.IsTotallyNonneg) :
    (diagonalTail δ A).IsTotallyNonneg := by
  intro n rows cols hrows hcols
  let M := (∑ i, rows i) + (∑ j, cols j) + 1
  let rows' : Fin n → Fin M := fun i =>
    ⟨rows i, by
      have hle : rows i ≤ ∑ k, rows k :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      dsimp [M]
      lia⟩
  let cols' : Fin n → Fin M := fun j =>
    ⟨cols j, by
      have hle : cols j ≤ ∑ k, cols k :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      dsimp [M]
      lia⟩
  have hrows' : StrictMono rows' := fun i j hij => hrows hij
  have hcols' : StrictMono cols' := fun i j hij => hcols hij
  have heq : (Matrix.diagonalTail δ A).submatrix rows cols =
      ((Matrix.diagonalTail δ A).submatrix (fun i : Fin M => i.val)
        (fun j : Fin M => j.val)).submatrix rows' cols' := by
    ext i j
    rfl
  rw [heq]
  exact (hA.diagonalTail_fin hδ M) hrows' hcols'

end Matrix
