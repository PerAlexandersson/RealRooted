import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.SourceBorder

/-!
# The finite Brändén--Leite source border

This file assembles the two finite total-nonnegativity borders into the matrix
used by the regularized two-kernel construction.
-/

namespace RealRooted.BrandenLeite

open Matrix

/-- The finite source-border matrix with blocks
`[δ 0; G e₀, G * H]`. -/
def sourceBorder {R : Type*} [Semiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    Matrix (Fin (N + 2)) (Fin (N + 2)) R :=
  Fin.cases (Fin.cases δ fun _ => 0)
    (fun i => Fin.cases (G i 0) ((G * H) i))

@[simp]
theorem sourceBorder_zero_zero {R : Type*} [Semiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    sourceBorder δ G H 0 0 = δ :=
  rfl

@[simp]
theorem sourceBorder_zero_succ {R : Type*} [Semiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) (j : Fin (N + 1)) :
    sourceBorder δ G H 0 j.succ = 0 :=
  rfl

@[simp]
theorem sourceBorder_succ_zero {R : Type*} [Semiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) (i : Fin (N + 1)) :
    sourceBorder δ G H i.succ 0 = G i 0 :=
  rfl

@[simp]
theorem sourceBorder_succ_succ {R : Type*} [Semiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i j : Fin (N + 1)) :
    sourceBorder δ G H i.succ j.succ = (G * H) i j :=
  rfl

/-- The source border is the product of the isolated-coordinate lift of `G`
and the scalar source step over `H`. -/
theorem sourceBorder_eq_isolateFirstCoordinate_mul_sourceStep
    {R : Type*} [CommSemiring R] {N : ℕ} (δ : R)
    (G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    sourceBorder δ G H = isolateFirstCoordinate G * Matrix.sourceStep δ H := by
  ext i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The finite source border of two totally nonnegative matrices is totally
nonnegative when its leading scalar is nonnegative. -/
theorem sourceBorder_isTotallyNonneg
    {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
    {N : ℕ} {δ : R}
    {G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R}
    (hδ : 0 ≤ δ) (hG : G.IsTotallyNonneg) (hH : H.IsTotallyNonneg) :
    (sourceBorder δ G H).IsTotallyNonneg := by
  rw [sourceBorder_eq_isolateFirstCoordinate_mul_sourceStep]
  exact hG.isolateFirstCoordinate.mul (hH.sourceStep hδ)

/-- The finite source border vanishes strictly above the diagonal when both
input matrices do. -/
theorem sourceBorder_upper_zero
    {R : Type*} [CommSemiring R] {N : ℕ} {δ : R}
    {G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R}
    (hG : ∀ i j, i < j → G i j = 0)
    (hH : ∀ i j, i < j → H i j = 0) :
    ∀ i j, i < j → sourceBorder δ G H i j = 0 := by
  intro i j hij
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact (lt_irrefl _ hij).elim
    · rfl
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · simp at hij
    · exact mul_apply_eq_zero_of_lt_of_upper_zero G H hG hH
        (Fin.succ_lt_succ_iff.mp hij)

/-- Constant diagonals `g` and `η` give the source border the constant
diagonal `g * η`. -/
theorem sourceBorder_diagonal
    {R : Type*} [CommSemiring R] {N : ℕ} {g η : R}
    {G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R}
    (hG : ∀ i j, i < j → G i j = 0)
    (hH : ∀ i j, i < j → H i j = 0)
    (hGdiag : ∀ i, G i i = g) (hHdiag : ∀ i, H i i = η) :
    ∀ i, sourceBorder (g * η) G H i i = g * η := by
  intro i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rfl
  · rw [sourceBorder_succ_succ,
      mul_apply_self_of_upper_zero G H hG hH i, hGdiag i, hHdiag i]

/-- Positive constant-diagonal lower TN matrices have a lower TN source border
with the same constant product diagonal. -/
theorem sourceBorder_certificate
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {N : ℕ} {g η : R}
    {G H : Matrix (Fin (N + 1)) (Fin (N + 1)) R}
    (hg : 0 < g) (hη : 0 < η)
    (hG : G.IsTotallyNonneg) (hH : H.IsTotallyNonneg)
    (hGlower : ∀ i j, i < j → G i j = 0)
    (hHlower : ∀ i j, i < j → H i j = 0)
    (hGdiag : ∀ i, G i i = g) (hHdiag : ∀ i, H i i = η) :
    (sourceBorder (g * η) G H).IsTotallyNonneg ∧
      (∀ i j, i < j → sourceBorder (g * η) G H i j = 0) ∧
      (∀ i, sourceBorder (g * η) G H i i = g * η) := by
  exact ⟨sourceBorder_isTotallyNonneg (mul_nonneg hg.le hη.le) hG hH,
    sourceBorder_upper_zero hGlower hHlower,
    sourceBorder_diagonal hGlower hHlower hGdiag hHdiag⟩

end RealRooted.BrandenLeite
