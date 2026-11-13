module

public import RealRooted.Basic.ProperPosition
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Bidiagonal
public import RealRooted.SimpleRoots
public import RealRooted.TetradiagonalFactorization
import RealRooted.Interlacing.Reversal
import RealRooted.Linear
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
import RealRooted.OscillatoryInterlacing
import Mathlib.Tactic

/-!
# Weighted products of three bidiagonal matrices

Two lower bidiagonal factors followed by an upper bidiagonal factor give a
matrix with one upper and two lower bands. Nonnegative factor weights, positive
determinants and positive adjacent bands imply strict interlacing of consecutive
leading characteristic polynomials, with simple positive roots.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace Matrix

variable {R : Type*} [CommRing R]

/-- The product of two weighted lower bidiagonal sections and one weighted upper
bidiagonal section. -/
def threeBidiagonalProduction (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R) (n : ℕ) :
    Matrix (Fin n) (Fin n) R :=
  lowerBidiagonalFin n d₀ s₀ * lowerBidiagonalFin n d₁ s₁ *
    upperBidiagonalFin n d₂ s₂

/-- The diagonal weight, including the exceptional first row. -/
def threeBidiagonalDiag (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R) : ℕ → R
  | 0 => d₀ 0 * d₁ 0 * d₂ 0
  | i + 1 => d₀ (i + 1) * d₁ (i + 1) * d₂ (i + 1) +
      (s₀ i * d₁ i + d₀ (i + 1) * s₁ i) * s₂ i

/-- The first subdiagonal weight, including the exceptional first column. -/
def threeBidiagonalSub (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R) : ℕ → R
  | 0 => (s₀ 0 * d₁ 0 + d₀ 1 * s₁ 0) * d₂ 0
  | i + 1 => (s₀ (i + 1) * d₁ (i + 1) + d₀ (i + 2) * s₁ (i + 1)) *
      d₂ (i + 1) + s₀ (i + 1) * s₁ i * s₂ i

private lemma lowerBidiagonalFin_mul_zero {n : ℕ} (d s : ℕ → R)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (j : Fin (n + 1)) :
    (lowerBidiagonalFin (n + 1) d s * M) 0 j = d 0 * M 0 j := by
  rw [mul_apply]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    have hval : k.val ≠ 0 := fun h => hk (Fin.ext h)
    simp [lowerBidiagonalFin_apply, Ne.symm hk, hval]
  · simp

private lemma lowerBidiagonalFin_mul_succ {n k : ℕ} (hk : k + 1 < n)
    (d s : ℕ → R) (M : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    (lowerBidiagonalFin n d s * M) ⟨k + 1, hk⟩ j =
      d (k + 1) * M ⟨k + 1, hk⟩ j + s k * M ⟨k, by lia⟩ j := by
  rw [mul_apply]
  have hentry (a : Fin n) :
      lowerBidiagonalFin n d s ⟨k + 1, hk⟩ a * M a j =
        (if a = ⟨k + 1, hk⟩ then d (k + 1) * M a j else 0) +
          (if a = ⟨k, by lia⟩ then s k * M a j else 0) := by
    by_cases ha : a = ⟨k + 1, hk⟩
    · subst a
      simp [lowerBidiagonalFin_apply, Fin.ext_iff]
    · have hav : a.val ≠ k + 1 := fun h => ha (Fin.ext h)
      by_cases hb : a = ⟨k, by lia⟩
      · subst a
        simp [lowerBidiagonalFin_apply, Fin.ext_iff]
      · have hbv : a.val ≠ k := fun h => hb (Fin.ext h)
        simp [lowerBidiagonalFin_apply, Fin.ext_iff, hav, hbv, Ne.symm hav, Ne.symm hbv]
  simp_rw [hentry]
  rw [Finset.sum_add_distrib]
  simp

private lemma threeBidiagonalProduction_row_zero (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R)
    (n : ℕ) (j : Fin (n + 1)) :
    threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ (n + 1) 0 j =
      d₀ 0 * d₁ 0 * upperBidiagonalFin (n + 1) d₂ s₂ 0 j := by
  rw [threeBidiagonalProduction, Matrix.mul_assoc,
    lowerBidiagonalFin_mul_zero, lowerBidiagonalFin_mul_zero, mul_assoc]

private lemma threeBidiagonalProduction_row_one (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R)
    {n : ℕ} (hn : 1 < n) (j : Fin n) :
    threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n ⟨1, hn⟩ j =
      d₀ 1 * d₁ 1 * upperBidiagonalFin n d₂ s₂ ⟨1, hn⟩ j +
        (s₀ 0 * d₁ 0 + d₀ 1 * s₁ 0) * upperBidiagonalFin n d₂ s₂ ⟨0, by lia⟩ j := by
  cases n with
  | zero => lia
  | succ n =>
      rw [threeBidiagonalProduction, Matrix.mul_assoc,
        lowerBidiagonalFin_mul_succ hn, lowerBidiagonalFin_mul_succ hn]
      simp only [Fin.mk_zero, lowerBidiagonalFin_mul_zero]
      ring

private lemma threeBidiagonalProduction_row_add_two (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R)
    {n k : ℕ} (hk : k + 2 < n) (j : Fin n) :
    threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n ⟨k + 2, hk⟩ j =
      d₀ (k + 2) * d₁ (k + 2) * upperBidiagonalFin n d₂ s₂ ⟨k + 2, hk⟩ j +
        (s₀ (k + 1) * d₁ (k + 1) + d₀ (k + 2) * s₁ (k + 1)) *
          upperBidiagonalFin n d₂ s₂ ⟨k + 1, by lia⟩ j +
        s₀ (k + 1) * s₁ k * upperBidiagonalFin n d₂ s₂ ⟨k, by lia⟩ j := by
  rw [threeBidiagonalProduction, Matrix.mul_assoc,
    lowerBidiagonalFin_mul_succ hk, lowerBidiagonalFin_mul_succ hk,
    lowerBidiagonalFin_mul_succ (show k + 1 < n by lia)]
  ring

/-- The entry formula displays the diagonal, superdiagonal and two lower bands. -/
theorem threeBidiagonalProduction_apply (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R)
    (n : ℕ) (i j : Fin n) :
    threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n i j =
      if i.val = j.val then threeBidiagonalDiag d₀ s₀ d₁ s₁ d₂ s₂ i.val
      else if j.val = i.val + 1 then d₀ i.val * d₁ i.val * s₂ i.val
      else if i.val = j.val + 1 then threeBidiagonalSub d₀ s₀ d₁ s₁ d₂ s₂ j.val
      else if i.val = j.val + 2 then s₀ (j.val + 1) * s₁ j.val * d₂ j.val
      else 0 := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  match i with
  | 0 =>
      cases n with
      | zero => lia
      | succ n =>
          simp only [Fin.mk_zero]
          rw [threeBidiagonalProduction_row_zero]
          simp only [upperBidiagonalFin_apply, Fin.ext_iff, Fin.val_zero,
            threeBidiagonalDiag]
          split_ifs <;> grind
  | 1 =>
      rw [threeBidiagonalProduction_row_one d₀ s₀ d₁ s₁ d₂ s₂ hi]
      simp only [upperBidiagonalFin_apply, Fin.ext_iff]
      by_cases hj0 : j = 0
      · subst j
        simp [threeBidiagonalSub]
      · simp [hj0, Ne.symm hj0, threeBidiagonalDiag]
        split_ifs <;> grind
  | k + 2 =>
      rw [threeBidiagonalProduction_row_add_two d₀ s₀ d₁ s₁ d₂ s₂ hi]
      simp only [upperBidiagonalFin_apply, Fin.ext_iff]
      by_cases hj1 : j = k + 1
      · subst j
        simp [threeBidiagonalSub]
      · have hsub : k + 2 ≠ j + 1 := by lia
        simp only [hsub, ↓reduceIte, threeBidiagonalDiag]
        split_ifs <;> grind

/-- The first superdiagonal is the product of the two lower diagonal weights
and the upper off-diagonal weight. -/
theorem threeBidiagonalProduction_super (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R)
    {n : ℕ} (i : Fin n) :
    threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ (n + 1) i.castSucc i.succ =
      d₀ i.val * d₁ i.val * s₂ i.val := by
  simp [threeBidiagonalProduction_apply]

/-- The diagonal entries have the boundary-aware diagonal weights. -/
theorem threeBidiagonalProduction_diag (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R)
    {n : ℕ} (i : Fin n) :
    threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n i i =
      threeBidiagonalDiag d₀ s₀ d₁ s₁ d₂ s₂ i.val := by
  simp [threeBidiagonalProduction_apply]

/-- The top-left entry has no contribution from an off-diagonal weight. -/
theorem threeBidiagonalProduction_zero_zero (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R)
    (n : ℕ) :
    threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ (n + 1) 0 0 =
      d₀ 0 * d₁ 0 * d₂ 0 := by
  simp [threeBidiagonalProduction_diag, threeBidiagonalDiag]

/-- The positive-index diagonal entries include the preceding upper-band term. -/
theorem threeBidiagonalProduction_diag_succ (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R)
    {n i : ℕ} (hi : i + 1 < n) :
    threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n ⟨i + 1, hi⟩ ⟨i + 1, hi⟩ =
      d₀ (i + 1) * d₁ (i + 1) * d₂ (i + 1) +
        (s₀ i * d₁ i + d₀ (i + 1) * s₁ i) * s₂ i := by
  rw [threeBidiagonalProduction_diag]
  rfl

/-- The first subdiagonal has the boundary-aware first lower-band weights. -/
theorem threeBidiagonalProduction_sub (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R)
    {n : ℕ} (i : Fin n) :
    threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ (n + 1) i.succ i.castSucc =
      threeBidiagonalSub d₀ s₀ d₁ s₁ d₂ s₂ i.val := by
  simp [threeBidiagonalProduction_apply]
  lia

/-- The second subdiagonal is a product of three factor weights. -/
theorem threeBidiagonalProduction_sub_two (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R)
    {n i : ℕ} (hi : i + 2 < n) :
    threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n ⟨i + 2, hi⟩ ⟨i, by lia⟩ =
      s₀ (i + 1) * s₁ i * d₂ i := by
  simp [threeBidiagonalProduction_apply]
  lia

/-- Entries above the first superdiagonal vanish. -/
theorem threeBidiagonalProduction_eq_zero_of_above (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R)
    {n : ℕ} (i j : Fin n) (hij : i.val + 1 < j.val) :
    threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n i j = 0 := by
  rw [threeBidiagonalProduction_apply]
  split_ifs <;> lia

/-- Entries below the second subdiagonal vanish. -/
theorem threeBidiagonalProduction_eq_zero_of_below (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R)
    {n : ℕ} (i j : Fin n) (hij : j.val + 2 < i.val) :
    threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n i j = 0 := by
  rw [threeBidiagonalProduction_apply]
  split_ifs <;> lia

/-- Leading truncation commutes with the structured product. -/
theorem threeBidiagonalProduction_castSucc (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R)
    (n : ℕ) :
    (threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ (n + 1)).submatrix
        Fin.castSucc Fin.castSucc =
      threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n := by
  ext i j
  simp only [submatrix_apply, threeBidiagonalProduction_apply, Fin.val_castSucc]

private lemma det_upperBidiagonalFin (n : ℕ) (d s : ℕ → R) :
    (upperBidiagonalFin n d s).det = ∏ i : Fin n, d i.val := by
  rw [det_of_isUpperTriangular (upperBidiagonalFin_blockTriangular n d s)]
  simp

private lemma det_lowerBidiagonalFin (n : ℕ) (d s : ℕ → R) :
    (lowerBidiagonalFin n d s).det = ∏ i : Fin n, d i.val := by
  have h : lowerBidiagonalFin n d s = (upperBidiagonalFin n d s)ᵀ := rfl
  rw [h, det_transpose, det_upperBidiagonalFin]

/-- The determinant depends only on the diagonal weights of the factors. -/
theorem det_threeBidiagonalProduction (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R) (n : ℕ) :
    (threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n).det =
      ∏ i : Fin n, d₀ i.val * d₁ i.val * d₂ i.val := by
  simp only [threeBidiagonalProduction, det_mul, det_lowerBidiagonalFin,
    det_upperBidiagonalFin, Finset.prod_mul_distrib]

/-- Nonnegative factor weights give a totally nonnegative product, allowing
zero diagonal and off-diagonal weights. -/
theorem isTotallyNonneg_threeBidiagonalProduction
    (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → ℝ) (n : ℕ)
    (h : ∀ i, 0 ≤ d₀ i ∧ 0 ≤ s₀ i ∧ 0 ≤ d₁ i ∧ 0 ≤ s₁ i ∧
      0 ≤ d₂ i ∧ 0 ≤ s₂ i) :
    (threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n).IsTotallyNonneg :=
  ((isTotallyNonneg_lowerBidiagonalFin n d₀ s₀
    (fun i => (h i).1) (fun i => (h i).2.1)).mul
    (isTotallyNonneg_lowerBidiagonalFin n d₁ s₁
      (fun i => (h i).2.2.1) (fun i => (h i).2.2.2.1))).mul
    (isTotallyNonneg_upperBidiagonalFin n d₂ s₂
      (fun i => (h i).2.2.2.2.1) (fun i => (h i).2.2.2.2.2))

/-- Positive factor-diagonal products and positive adjacent product bands give
strict consecutive interlacing, simple roots, disjointness and positive spectrum. -/
theorem threeBidiagonalProduction_charpoly_strictInterlaces
    (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → ℝ)
    (h : ∀ i, 0 ≤ d₀ i ∧ 0 ≤ s₀ i ∧ 0 ≤ d₁ i ∧ 0 ≤ s₁ i ∧
      0 ≤ d₂ i ∧ 0 ≤ s₂ i)
    (hdet : ∀ i, 0 < d₀ i * d₁ i * d₂ i)
    (hsuper : ∀ i, 0 < d₀ i * d₁ i * s₂ i)
    (hsub : ∀ i, 0 < threeBidiagonalSub d₀ s₀ d₁ s₁ d₂ s₂ i) (n : ℕ) :
    let H := threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂
    RealRooted.Interlaces (H n).charpoly (H (n + 1)).charpoly ∧
      (∀ x : ℝ, (H (n + 1)).charpoly.IsRoot x →
        (H (n + 1)).charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, (H n).charpoly.IsRoot x → (H n).charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, ¬((H (n + 1)).charpoly.IsRoot x ∧ (H n).charpoly.IsRoot x)) ∧
      ∀ x ∈ (H (n + 1)).charpoly.roots, 0 < x := by
  have hTN := isTotallyNonneg_threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ (n + 1) h
  have hdet' : (threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ (n + 1)).det ≠ 0 := by
    rw [det_threeBidiagonalProduction]
    exact (Finset.prod_pos fun i _ => hdet i.val).ne'
  have hsuper' (i : Fin n) :
      0 < threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ (n + 1) i.castSucc i.succ := by
    rw [threeBidiagonalProduction_super]
    exact hsuper i.val
  have hsub' (i : Fin n) :
      0 < threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ (n + 1) i.succ i.castSucc := by
    rw [threeBidiagonalProduction_sub]
    exact hsub i.val
  simpa only [threeBidiagonalProduction_castSucc] using
    hTN.leading_charpoly_strictInterlaces hdet' hsuper' hsub'

section Oscillation

variable (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → ℝ)
  (h : ∀ i, 0 ≤ d₀ i ∧ 0 ≤ s₀ i ∧ 0 ≤ d₁ i ∧ 0 ≤ s₁ i ∧
    0 ≤ d₂ i ∧ 0 ≤ s₂ i)
  (hdet : ∀ i, 0 < d₀ i * d₁ i * d₂ i)
  (hsuper : ∀ i, 0 < d₀ i * d₁ i * s₂ i)
  (hsub : ∀ i, 0 < threeBidiagonalSub d₀ s₀ d₁ s₁ d₂ s₂ i)

include h hdet hsuper hsub

/-- Consecutive leading characteristic polynomials interlace. -/
theorem threeBidiagonalProduction_charpoly_interlaces (n : ℕ) :
    RealRooted.Interlaces
      (threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n).charpoly
      (threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ (n + 1)).charpoly :=
  (threeBidiagonalProduction_charpoly_strictInterlaces
    d₀ s₀ d₁ s₁ d₂ s₂ h hdet hsuper hsub n).1

/-- Every leading characteristic polynomial splits over the reals. -/
theorem threeBidiagonalProduction_charpoly_splits (n : ℕ) :
    (threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n).charpoly.Splits :=
  (threeBidiagonalProduction_charpoly_interlaces
    d₀ s₀ d₁ s₁ d₂ s₂ h hdet hsuper hsub n).2.1.2

/-- Every real root of a leading characteristic polynomial is simple and positive. -/
theorem threeBidiagonalProduction_charpoly_simple_pos (n : ℕ) :
    ∀ x : ℝ, (threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n).charpoly.IsRoot x →
      (threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n).charpoly.rootMultiplicity x =
        1 ∧ 0 < x := by
  cases n with
  | zero => simp [charpoly, threeBidiagonalProduction]
  | succ n =>
      have hp := threeBidiagonalProduction_charpoly_strictInterlaces
        d₀ s₀ d₁ s₁ d₂ s₂ h hdet hsuper hsub n
      intro x hx
      have hn :=
        (threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ (n + 1)).charpoly_monic.ne_zero
      have hxmem : x ∈
          (threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ (n + 1)).charpoly.roots :=
        (Polynomial.mem_roots hn).2 hx
      exact ⟨hp.2.1 x hx, hp.2.2.2.2 x hxmem⟩

end Oscillation

/-- With unit superdiagonal, the product is the tetradiagonal matrix whose
lower bands are indexed by their row. -/
theorem threeBidiagonalProduction_eq_tetradiagonalMatrix
    (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → ℝ)
    (hu : ∀ i, d₀ i * d₁ i * s₂ i = 1) (n : ℕ) :
    threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n =
      RealRooted.tetradiagonalMatrix (threeBidiagonalDiag d₀ s₀ d₁ s₁ d₂ s₂)
        (fun i => threeBidiagonalSub d₀ s₀ d₁ s₁ d₂ s₂ (i - 1))
        (fun i => s₀ (i - 1) * s₁ (i - 2) * d₂ (i - 2)) n := by
  ext i j
  simp only [threeBidiagonalProduction_apply, RealRooted.tetradiagonalMatrix,
    bandedLowerHessenberg_apply, hu]
  split_ifs with hdiag hsuper hsub hsubtwo
  · rfl
  · rfl
  · congr 1
    lia
  · rw [show i.val - 1 = j.val + 1 by lia, show i.val - 2 = j.val by lia]
  · rfl

/-- Leading characteristic polynomials of a unit-superdiagonal weighted product
satisfy the four-term determinant recurrence. -/
theorem threeBidiagonalProduction_charpoly_add_three
    (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → ℝ)
    (hu : ∀ i, d₀ i * d₁ i * s₂ i = 1) (n : ℕ) :
    let H := threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂
    (H (n + 3)).charpoly =
      (X - C (threeBidiagonalDiag d₀ s₀ d₁ s₁ d₂ s₂ (n + 2))) *
          (H (n + 2)).charpoly -
        C (threeBidiagonalSub d₀ s₀ d₁ s₁ d₂ s₂ (n + 1)) * (H (n + 1)).charpoly -
          C (s₀ (n + 1) * s₁ n * d₂ n) * (H n).charpoly := by
  dsimp only
  simp_rw [threeBidiagonalProduction_eq_tetradiagonalMatrix d₀ s₀ d₁ s₁ d₂ s₂ hu]
  simpa using RealRooted.tetradiagonalMatrix_charpoly_add_three
    (threeBidiagonalDiag d₀ s₀ d₁ s₁ d₂ s₂)
    (fun i => threeBidiagonalSub d₀ s₀ d₁ s₁ d₂ s₂ (i - 1))
    (fun i => s₀ (i - 1) * s₁ (i - 2) * d₂ (i - 2)) n

/-- The empty leading characteristic polynomial is one. -/
theorem threeBidiagonalProduction_charpoly_zero (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R) :
    (threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ 0).charpoly = 1 := by
  simp [Matrix.charpoly]

/-- The first leading characteristic polynomial is linear. -/
theorem threeBidiagonalProduction_charpoly_one (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R) :
    (threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ 1).charpoly =
      X - C (d₀ 0 * d₁ 0 * d₂ 0) := by
  simp [Matrix.charpoly, threeBidiagonalProduction_zero_zero]

/-- The second leading characteristic polynomial includes the product of its
first upper and lower band entries. -/
theorem threeBidiagonalProduction_charpoly_two (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → R) :
    (threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ 2).charpoly =
      (X - C (threeBidiagonalDiag d₀ s₀ d₁ s₁ d₂ s₂ 1)) *
          (X - C (d₀ 0 * d₁ 0 * d₂ 0)) -
        C (threeBidiagonalSub d₀ s₀ d₁ s₁ d₂ s₂ 0) * C (d₀ 0 * d₁ 0 * s₂ 0) := by
  simp [Matrix.charpoly, Matrix.det_fin_two,
    threeBidiagonalProduction_apply, threeBidiagonalDiag]
  ring

/-- The standard two-branched production matrix is a product of two unit lower
bidiagonal matrices and one upper bidiagonal matrix. -/
def twoBranchedProduction (α : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  threeBidiagonalProduction (fun _ => 1) (fun i => α (3 * i + 3))
    (fun _ => 1) (fun i => α (3 * i + 4)) (fun i => α (3 * i + 2)) (fun _ => 1) n

/-- The top-left entry of the standard product is the initial upper diagonal weight. -/
theorem twoBranchedProduction_zero_zero (α : ℕ → R) (n : ℕ) :
    twoBranchedProduction α (n + 1) 0 0 = α 2 := by
  simp [twoBranchedProduction, threeBidiagonalProduction_zero_zero]

/-- The positive-index standard diagonal is the sum of three consecutive weights. -/
theorem twoBranchedProduction_diag_succ (α : ℕ → R) {n i : ℕ} (hi : i + 1 < n) :
    twoBranchedProduction α n ⟨i + 1, hi⟩ ⟨i + 1, hi⟩ =
      α (3 * (i + 1)) + α (3 * (i + 1) + 1) + α (3 * (i + 1) + 2) := by
  rw [twoBranchedProduction, threeBidiagonalProduction_diag_succ]
  simp only [one_mul, mul_one]
  ring_nf

/-- The standard first subdiagonal has a genuine two-term boundary value. -/
theorem twoBranchedProduction_sub_zero (α : ℕ → R) (n : ℕ) :
    twoBranchedProduction α (n + 2) ⟨1, by lia⟩ ⟨0, by lia⟩ =
      α 2 * α 4 + α 2 * α 3 := by
  simp [twoBranchedProduction, threeBidiagonalProduction_apply, threeBidiagonalSub]
  ring

/-- Away from the boundary the standard first subdiagonal is a sum of three products. -/
theorem twoBranchedProduction_sub_succ (α : ℕ → R) {n i : ℕ} (hi : i + 2 < n) :
    twoBranchedProduction α n ⟨i + 2, hi⟩ ⟨i + 1, by lia⟩ =
      α (3 * (i + 1) + 2) * α (3 * (i + 1) + 4) +
        α (3 * (i + 1) + 2) * α (3 * (i + 1) + 3) +
        α (3 * (i + 1) + 1) * α (3 * (i + 1) + 3) := by
  simp [twoBranchedProduction, threeBidiagonalProduction_apply, threeBidiagonalSub]
  ring_nf

/-- With vanishing first weight, the standard lower-band weight has a uniform
three-term expression at every natural index, including zero. -/
theorem threeBidiagonalSub_branched (α : ℕ → R) (hα : α 1 = 0) (i : ℕ) :
    threeBidiagonalSub (fun _ => 1) (fun i => α (3 * i + 3))
        (fun _ => 1) (fun i => α (3 * i + 4)) (fun i => α (3 * i + 2))
        (fun _ => 1) i =
      α (3 * i + 2) * α (3 * i + 4) + α (3 * i + 2) * α (3 * i + 3) +
        α (3 * i + 1) * α (3 * i + 3) := by
  cases i with
  | zero => simp [threeBidiagonalSub, hα]; ring
  | succ i =>
      simp only [threeBidiagonalSub, one_mul, mul_one]
      ring_nf

/-- A vanishing first weight makes the standard first-subdiagonal formula uniform. -/
theorem twoBranchedProduction_sub (α : ℕ → R) (hα : α 1 = 0)
    {n : ℕ} (i : Fin n) :
    twoBranchedProduction α (n + 1) i.succ i.castSucc =
      α (3 * i.val + 2) * α (3 * i.val + 4) +
        α (3 * i.val + 2) * α (3 * i.val + 3) +
        α (3 * i.val + 1) * α (3 * i.val + 3) := by
  rw [twoBranchedProduction, threeBidiagonalProduction_sub,
    threeBidiagonalSub_branched α hα]

/-- The standard second subdiagonal is a product of three even-step weights. -/
theorem twoBranchedProduction_sub_two (α : ℕ → R) {n i : ℕ} (hi : i + 2 < n) :
    twoBranchedProduction α n ⟨i + 2, hi⟩ ⟨i, by lia⟩ =
      α (3 * i + 2) * α (3 * i + 4) * α (3 * i + 6) := by
  rw [twoBranchedProduction, threeBidiagonalProduction_sub_two]
  ring_nf

end Matrix

namespace RealRooted

/-- A four-term recurrence is determined by its first three polynomials. -/
theorem eq_tetradiagonalPolynomial_of_recurrence
    (d s t : ℕ → ℝ) (P : ℕ → ℝ[X])
    (hzero : P 0 = 1) (hone : P 1 = X - C (d 0))
    (htwo : P 2 = (X - C (d 1)) * (X - C (d 0)) - C (s 1))
    (hstep : ∀ n, P (n + 3) = (X - C (d (n + 2))) * P (n + 2) -
      C (s (n + 2)) * P (n + 1) - C (t (n + 2)) * P n) :
    ∀ n, P n = tetradiagonalPolynomial d s t n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => exact hzero
      | 1 => exact hone
      | 2 => exact htwo
      | n + 3 =>
          rw [hstep, tetradiagonalPolynomial, ih (n + 2) (by lia),
            ih (n + 1) (by lia), ih n (by lia)]

/-- Three startup identities and the four-term recurrence identify all leading
characteristic polynomials of a unit-superdiagonal tetradiagonal matrix. -/
theorem eq_charpoly_tetradiagonalMatrix_of_recurrence
    (d s t : ℕ → ℝ) (P : ℕ → ℝ[X])
    (hzero : P 0 = 1) (hone : P 1 = X - C (d 0))
    (htwo : P 2 = (X - C (d 1)) * (X - C (d 0)) - C (s 1))
    (hstep : ∀ n, P (n + 3) = (X - C (d (n + 2))) * P (n + 2) -
      C (s (n + 2)) * P (n + 1) - C (t (n + 2)) * P n) (n : ℕ) :
    P n = (tetradiagonalMatrix d s t n).charpoly := by
  rw [eq_tetradiagonalPolynomial_of_recurrence d s t P hzero hone htwo hstep,
    tetradiagonalPolynomial_eq_charpoly]

/-- Three startup identities and the weighted four-term recurrence identify
the characteristic polynomial of every leading product section. -/
theorem eq_charpoly_threeBidiagonalProduction_of_recurrence
    (d₀ s₀ d₁ s₁ d₂ s₂ : ℕ → ℝ) (hu : ∀ i, d₀ i * d₁ i * s₂ i = 1)
    (P : ℕ → ℝ[X])
    (hzero : P 0 = 1) (hone : P 1 = X - C (d₀ 0 * d₁ 0 * d₂ 0))
    (htwo : P 2 = (X - C (Matrix.threeBidiagonalDiag d₀ s₀ d₁ s₁ d₂ s₂ 1)) *
      (X - C (d₀ 0 * d₁ 0 * d₂ 0)) -
        C (Matrix.threeBidiagonalSub d₀ s₀ d₁ s₁ d₂ s₂ 0))
    (hstep : ∀ n, P (n + 3) =
      (X - C (Matrix.threeBidiagonalDiag d₀ s₀ d₁ s₁ d₂ s₂ (n + 2))) * P (n + 2) -
        C (Matrix.threeBidiagonalSub d₀ s₀ d₁ s₁ d₂ s₂ (n + 1)) * P (n + 1) -
          C (s₀ (n + 1) * s₁ n * d₂ n) * P n) (n : ℕ) :
    P n = (Matrix.threeBidiagonalProduction d₀ s₀ d₁ s₁ d₂ s₂ n).charpoly := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 => rw [hzero, Matrix.threeBidiagonalProduction_charpoly_zero]
      | 1 => rw [hone, Matrix.threeBidiagonalProduction_charpoly_one]
      | 2 =>
          rw [htwo, Matrix.threeBidiagonalProduction_charpoly_two, hu 0,
            Polynomial.C_1, mul_one]
      | n + 3 =>
          rw [hstep, Matrix.threeBidiagonalProduction_charpoly_add_three
            d₀ s₀ d₁ s₁ d₂ s₂ hu, ih (n + 2) (by lia),
            ih (n + 1) (by lia), ih n (by lia)]

/-- A negative rescaling of the variable preserves proper position for a pair
whose degrees differ by one. Nonzero scalar normalizations may then be applied. -/
theorem StrictInterl.comp_neg_mul_X_of_natDegree_succ {p q : ℝ[X]}
    (h : StrictInterl p q) (hdeg : p.natDegree + 1 = q.natDegree)
    {c : ℝ} (hc : 0 < c) :
    StrictInterl (p.comp (C (-c) * X)) (q.comp (C (-c) * X)) := by
  have href := (interlaces_comp_neg_X (h.toInterlaces hdeg)).toStrictInterl
  simpa [Polynomial.comp_assoc] using href.comp_C_mul_X hc

/-- The degree-normalized reflected reciprocal is `(-x)^degree p(-1/x)`. -/
def reflectedReciprocal (p : ℝ[X]) : ℝ[X] :=
  C ((-1 : ℝ) ^ p.natDegree) * (p.comp (-X)).reverse

private lemma roots_comp_neg_X_neg {p : ℝ[X]}
    (hp : ∀ x ∈ p.roots, 0 < x) :
    ∀ x ∈ (p.comp (-X)).roots, x < 0 := by
  intro x hx
  rw [Polynomial.roots_comp_neg_X, Multiset.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact neg_neg_of_pos (hp y hy)

private lemma coeff_zero_ne_of_roots_strictly_neg {p : ℝ[X]} (hp : p ≠ 0)
    (hneg : ∀ x ∈ p.roots, x < 0) : p.coeff 0 ≠ 0 := by
  intro hzero
  have hz : p.IsRoot 0 := by
    rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero]
    exact hzero
  exact (lt_irrefl (0 : ℝ)) (hneg 0 ((Polynomial.mem_roots hp).2 hz))

/-- The reflected reciprocal sends every positive root to its negative inverse,
with multiplicities preserved. -/
theorem reflectedReciprocal_roots {p : ℝ[X]} (hp : p ≠ 0) (hs : p.Splits)
    (hpos : ∀ x ∈ p.roots, 0 < x) :
    (reflectedReciprocal p).roots = p.roots.map (fun x => -x⁻¹) := by
  have hn : p.comp (-X) ≠ 0 := by
    have h := isRealRooted_comp_C_mul_X hp hs (by norm_num : (-1 : ℝ) ≠ 0)
    simpa using h.1
  rw [reflectedReciprocal, Polynomial.roots_C_mul _ (pow_ne_zero _ (by norm_num)),
    Polynomial.roots_reverse_eq_map_inv hs.comp_neg_X
      (coeff_zero_ne_of_roots_strictly_neg hn (roots_comp_neg_X_neg hpos)),
    Polynomial.roots_comp_neg_X, Multiset.map_map]
  simp only [Function.comp_def, inv_neg]

/-- Degree-normalized reflected reciprocals preserve consecutive interlacing
for positive spectra. Both transformed spectra are strictly negative. -/
theorem Interlaces.reflectedReciprocal {p q : ℝ[X]} (h : Interlaces p q)
    (hp : ∀ x ∈ p.roots, 0 < x) (hq : ∀ x ∈ q.roots, 0 < x) :
    Interlaces (reflectedReciprocal p) (reflectedReciprocal q) ∧
      (∀ x ∈ (reflectedReciprocal p).roots, x < 0) ∧
      ∀ x ∈ (reflectedReciprocal q).roots, x < 0 := by
  have href := interlaces_comp_neg_X h
  have hrev := interlaces_reverse_of_roots_neg href
    (roots_comp_neg_X_neg hq) (roots_comp_neg_X_neg hp)
  have hsign (n : ℕ) : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hnormalized := ((hrev.toStrictInterl.C_mul_left
    (hsign p.natDegree)).C_mul_right (hsign q.natDegree)).toInterlaces
      (by simpa only [Polynomial.natDegree_C_mul (hsign p.natDegree),
          Polynomial.natDegree_C_mul (hsign q.natDegree)]
        using hrev.2.2.1)
  refine ⟨hnormalized, ?_, ?_⟩
  · intro x hx
    rw [reflectedReciprocal_roots h.2.1.1 h.2.1.2 hp, Multiset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact neg_neg_of_pos (inv_pos.mpr (hp y hy))
  · intro x hx
    rw [reflectedReciprocal_roots h.1.1 h.1.2 hq, Multiset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact neg_neg_of_pos (inv_pos.mpr (hq y hy))

/-- A positive-spectrum interlacing pair with disjoint roots transfers to a
proper-position pair with simple negative roots and no common root. -/
theorem Interlaces.reflectedReciprocal_strict {p q : ℝ[X]} (h : Interlaces p q)
    (hp : ∀ x ∈ p.roots, 0 < x) (hq : ∀ x ∈ q.roots, 0 < x)
    (hno : ∀ x : ℝ, ¬(p.IsRoot x ∧ q.IsRoot x)) :
    StrictInterl (RealRooted.reflectedReciprocal p) (RealRooted.reflectedReciprocal q) ∧
      HasSimpleRoots (RealRooted.reflectedReciprocal p) ∧
      HasSimpleRoots (RealRooted.reflectedReciprocal q) ∧
      (∀ x : ℝ, ¬((RealRooted.reflectedReciprocal p).IsRoot x ∧
        (RealRooted.reflectedReciprocal q).IsRoot x)) ∧
      (∀ x ∈ (RealRooted.reflectedReciprocal p).roots, x < 0) ∧
      ∀ x ∈ (RealRooted.reflectedReciprocal q).roots, x < 0 := by
  obtain ⟨hout, hpneg, hqneg⟩ := h.reflectedReciprocal hp hq
  have hnout : ∀ x : ℝ, ¬((RealRooted.reflectedReciprocal p).IsRoot x ∧
      (RealRooted.reflectedReciprocal q).IsRoot x) := by
    intro x hx
    have hxp := (Polynomial.mem_roots hout.2.1.1).2 hx.1
    have hxq := (Polynomial.mem_roots hout.1.1).2 hx.2
    rw [reflectedReciprocal_roots h.2.1.1 h.2.1.2 hp, Multiset.mem_map] at hxp
    rw [reflectedReciprocal_roots h.1.1 h.1.2 hq, Multiset.mem_map] at hxq
    obtain ⟨a, ha, hax⟩ := hxp
    obtain ⟨b, hb, hbx⟩ := hxq
    have hab : a = b := inv_injective (neg_injective (hax.trans hbx.symm))
    apply hno a
    exact ⟨(Polynomial.mem_roots h.2.1.1).1 ha,
      (Polynomial.mem_roots h.1.1).1 (hab.symm ▸ hb)⟩
  have hsimp := hout.toStrictInterl.hasSimpleRoots_of_no_common_root hnout
  exact ⟨hout.toStrictInterl, hsimp.1, hsimp.2, hnout, hpneg, hqneg⟩

end RealRooted

section

open Matrix

local notation "H" => threeBidiagonalProduction (R := ℚ)
  (fun _ => 2) (fun _ => 3) (fun _ => 5) (fun _ => 7) (fun _ => 11) (fun _ => 13)

example : H 0 = 1 := by
  ext i
  exact Fin.elim0 i

example : H 1 = !![110] := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [threeBidiagonalProduction_apply, threeBidiagonalDiag]

example : H 2 = !![110, 130; 319, 487] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [threeBidiagonalProduction_apply, threeBidiagonalDiag, threeBidiagonalSub]

example : H 3 = !![110, 130, 0; 319, 487, 130; 231, 592, 487] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [threeBidiagonalProduction_apply, threeBidiagonalDiag, threeBidiagonalSub]

example (n : ℕ) : (H n).det = (110 : ℚ) ^ n := by
  simp [det_threeBidiagonalProduction]
  norm_num

example (n : ℕ) :
    let K := threeBidiagonalProduction (R := ℝ)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 1)
    RealRooted.Interlaces (K n).charpoly (K (n + 1)).charpoly := by
  apply threeBidiagonalProduction_charpoly_interlaces
  · intro i
    norm_num
  · intro i
    norm_num
  · intro i
    norm_num
  · intro i
    cases i <;> norm_num [threeBidiagonalSub]

end
