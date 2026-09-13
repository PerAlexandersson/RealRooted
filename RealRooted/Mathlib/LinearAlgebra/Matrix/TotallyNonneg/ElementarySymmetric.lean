import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Bidiagonal
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul

/-!
# Elementary-symmetric lower-triangular matrices

This file factors finite elementary-symmetric triangles into nonnegative lower
bidiagonal matrices. The construction is independent of path-network and LGV
infrastructure.
-/

namespace Multiset

variable {R : Type*} [CommSemiring R]

/-- Adjoining one variable gives the elementary-symmetric recurrence. -/
theorem esymm_cons (a : R) (s : Multiset R) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [esymm, powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Multiset.sum_map_mul_left]

end Multiset

namespace Matrix

noncomputable section

section Semiring

variable {R : Type*} [CommSemiring R]

/-- The elementary symmetric function of degree `j` in the first `n`
values of `w`. -/
def elementarySymmetricPrefix (w : ℕ → R) (n j : ℕ) : R :=
  ((Multiset.range n).map w).esymm j

@[simp]
theorem elementarySymmetricPrefix_zero (w : ℕ → R) (n : ℕ) :
    elementarySymmetricPrefix w n 0 = 1 := by
  simp [elementarySymmetricPrefix, Multiset.esymm]

theorem elementarySymmetricPrefix_succ (w : ℕ → R) (n j : ℕ) :
    elementarySymmetricPrefix w (n + 1) (j + 1) =
      elementarySymmetricPrefix w n (j + 1) +
        w n * elementarySymmetricPrefix w n j := by
  simp [elementarySymmetricPrefix, Multiset.esymm_cons]

/-- The generic lower-unitriangular elementary-symmetric array. -/
def elementarySymmetricTriangle (w : ℕ → R) : Matrix ℕ ℕ R :=
  fun n k => if k ≤ n then elementarySymmetricPrefix w n (n - k) else 0

@[simp]
theorem elementarySymmetricTriangle_apply (w : ℕ → R) (n k : ℕ) :
    elementarySymmetricTriangle w n k =
      if k ≤ n then elementarySymmetricPrefix w n (n - k) else 0 := rfl

/-- The elementary-symmetric triangle obeys the weighted Stirling
recurrence. -/
theorem elementarySymmetricTriangle_succ_succ
    (w : ℕ → R) (n k : ℕ) :
    elementarySymmetricTriangle w (n + 1) (k + 1) =
      elementarySymmetricTriangle w n k +
        w n * elementarySymmetricTriangle w n (k + 1) := by
  by_cases hk : k ≤ n
  · by_cases hkn : k = n
    · subst k
      simp [elementarySymmetricTriangle, elementarySymmetricPrefix_zero]
    · have hklt : k < n := lt_of_le_of_ne hk hkn
      have hdegree : n + 1 - (k + 1) = (n - (k + 1)) + 1 := by lia
      simp only [elementarySymmetricTriangle_apply, if_pos hk,
        if_pos (by lia : k + 1 ≤ n + 1), if_pos (by lia : k + 1 ≤ n)]
      rw [hdegree, elementarySymmetricPrefix_succ]
      congr 2
      lia
  · have hnk : n < k := Nat.lt_of_not_ge hk
    simp [elementarySymmetricTriangle, hk, show ¬k + 1 ≤ n by lia,
      show ¬k + 1 ≤ n + 1 by lia]

/-- Leading finite truncation of `elementarySymmetricTriangle`. -/
def elementarySymmetricTriangleFin (w : ℕ → R) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  (elementarySymmetricTriangle w).submatrix Fin.val Fin.val

@[simp]
theorem elementarySymmetricTriangleFin_apply
    (w : ℕ → R) (N : ℕ) (i j : Fin (N + 1)) :
    elementarySymmetricTriangleFin w N i j =
      if j.val ≤ i.val then
        elementarySymmetricPrefix w i.val (i.val - j.val)
      else 0 := rfl

end Semiring

section Ring

variable {R : Type*} [CommRing R]

/-- The factor introducing `w r`; its subdiagonal starts at level `r`. -/
def elementarySymmetricStep (w : ℕ → R) (N r : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  lowerBidiagonalFin (N + 1) (fun _ => 1)
    (fun j => if r ≤ j then w r else 0)

/-- Factors are multiplied with the newest variable on the left. -/
def elementarySymmetricStepProduct (w : ℕ → R) (N : ℕ) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) R
  | 0 => 1
  | r + 1 =>
      elementarySymmetricStep w N r * elementarySymmetricStepProduct w N r

private theorem elementarySymmetricStep_mul_apply
    (w : ℕ → R) (N r : ℕ)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (i j : Fin (N + 1)) :
    (elementarySymmetricStep w N r * A) i j =
      A i j + if r < i.val then
        w r * A ⟨i.val - 1, by lia⟩ j
      else 0 := by
  rw [Matrix.mul_apply]
  simp only [elementarySymmetricStep, lowerBidiagonalFin_apply, ite_mul,
    one_mul, zero_mul]
  calc
    (∑ x, if i = x then A x j
        else if i.val = x.val + 1 then
          if r ≤ x.val then w r * A x j else 0
        else 0) =
        ∑ x, ((if i = x then A x j else 0) +
          if i.val = x.val + 1 then
            if r ≤ x.val then w r * A x j else 0
          else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hix : i = x <;> simp [hix]
    _ = A i j + ∑ x,
        if i.val = x.val + 1 then
          if r ≤ x.val then w r * A x j else 0
        else 0 := by simp [Finset.sum_add_distrib]
    _ = A i j + if r < i.val then
        w r * A ⟨i.val - 1, by lia⟩ j
      else 0 := by
      congr 1
      by_cases hri : r < i.val
      · rw [if_pos hri]
        let p : Fin (N + 1) := ⟨i.val - 1, by lia⟩
        have hip : i.val = p.val + 1 := by simp [p]; lia
        rw [Finset.sum_eq_single p]
        · rw [if_pos hip, if_pos (by simp [p]; lia)]
        · intro b hb hbp
          by_cases hib : i.val = b.val + 1
          · have hval : b.val = p.val := by simp [p] at hib ⊢; lia
            exact (hbp (Fin.ext hval)).elim
          · simp [hib]
        · simp
      · rw [if_neg hri]
        apply Finset.sum_eq_zero
        intro x hx
        by_cases hix : i.val = x.val + 1
        · have hrx : ¬r ≤ x.val := by lia
          simp [hix, hrx]
        · simp [hix]

/-- After `r` factors, row `i` contains elementary symmetric functions in the
first `min r i` weights. -/
theorem elementarySymmetricStepProduct_apply
    (w : ℕ → R) (N r : ℕ) (hr : r ≤ N)
    (i j : Fin (N + 1)) :
    elementarySymmetricStepProduct w N r i j =
      if j.val ≤ i.val then
        elementarySymmetricPrefix w (min r i.val) (i.val - j.val)
      else 0 := by
  induction r generalizing i j with
  | zero =>
      rw [elementarySymmetricStepProduct]
      by_cases hij : i = j
      · subst j
        simp
      · by_cases hji : j.val ≤ i.val
        · have hlt : j.val < i.val := lt_of_le_of_ne hji
            (fun h => hij (Fin.ext h.symm))
          rw [if_pos hji, Matrix.one_apply, if_neg hij]
          simp [elementarySymmetricPrefix, Multiset.esymm,
            Multiset.powersetCard_eq_empty, hlt]
        · rw [if_neg hji, Matrix.one_apply, if_neg hij]
  | succ r ih =>
      rw [elementarySymmetricStepProduct, elementarySymmetricStep_mul_apply,
        ih (by lia)]
      by_cases hji : j.val ≤ i.val
      · simp only [if_pos hji]
        by_cases hri : r < i.val
        · rw [if_pos hri]
          let p : Fin (N + 1) := ⟨i.val - 1, by lia⟩
          change elementarySymmetricPrefix w (min r i.val) (i.val - j.val) +
              w r * elementarySymmetricStepProduct w N r p j =
            elementarySymmetricPrefix w (min (r + 1) i.val) (i.val - j.val)
          by_cases hij : i = j
          · subst j
            rw [ih (by lia), if_neg (by simp [p]; lia)]
            simp
          · have hji' : j.val < i.val := lt_of_le_of_ne hji
                (fun h => hij (Fin.ext h.symm))
            have hjp : j.val ≤ p.val := by simp [p]; lia
            rw [ih (by lia), if_pos hjp]
            have hmin : min r i.val = r := min_eq_left (Nat.le_of_lt hri)
            have hmin' : min r p.val = r := by
              rw [min_eq_left]
              simp [p]
              lia
            have hminSucc : min (r + 1) i.val = r + 1 :=
              min_eq_left (by lia)
            rw [hmin, hmin', hminSucc]
            have hdegree : i.val - j.val = (p.val - j.val) + 1 := by
              simp [p]
              lia
            rw [hdegree, elementarySymmetricPrefix_succ]
        · rw [if_neg hri]
          have hir : i.val ≤ r := by lia
          rw [min_eq_right hir, min_eq_right (by lia : i.val ≤ r + 1)]
          simp
      · simp only [if_neg hji]
        by_cases hri : r < i.val
        · rw [if_pos hri]
          have hpj : ¬j.val ≤ i.val - 1 := by lia
          rw [ih (by lia), if_neg hpj]
          simp
        · rw [if_neg hri]
          simp

/-- Exact bidiagonal factorization of every leading finite truncation. -/
theorem elementarySymmetricTriangleFin_eq_stepProduct
    (w : ℕ → R) (N : ℕ) :
    elementarySymmetricTriangleFin w N =
      elementarySymmetricStepProduct w N N := by
  ext i j
  rw [elementarySymmetricStepProduct_apply w N N (le_refl N)]
  by_cases hji : j.val ≤ i.val
  · rw [elementarySymmetricTriangleFin_apply, if_pos hji, if_pos hji,
      min_eq_right (by lia)]
  · rw [elementarySymmetricTriangleFin_apply, if_neg hji, if_neg hji]

section Ordered

variable [PartialOrder R] [IsStrictOrderedRing R]

theorem elementarySymmetricStep_isTotallyNonneg
    {w : ℕ → R} (hw : ∀ i, 0 ≤ w i) (N r : ℕ) :
    (elementarySymmetricStep w N r).IsTotallyNonneg := by
  apply isTotallyNonneg_lowerBidiagonalFin
  · simp
  · intro j
    by_cases hrj : r ≤ j
    · simp [hrj, hw r]
    · simp [hrj]

theorem elementarySymmetricStepProduct_isTotallyNonneg
    {w : ℕ → R} (hw : ∀ i, 0 ≤ w i) (N r : ℕ) :
    (elementarySymmetricStepProduct w N r).IsTotallyNonneg := by
  induction r with
  | zero =>
      simpa [elementarySymmetricStepProduct,
        Matrix.submatrix_one Fin.val Fin.val_injective] using
        (Matrix.IsTotallyNonneg.one (R := R)).submatrix
          Fin.val_strictMono Fin.val_strictMono
  | succ r ih =>
      rw [elementarySymmetricStepProduct]
      exact (elementarySymmetricStep_isTotallyNonneg hw N r).mul ih

/-- Nonnegative weights make every leading truncation of the elementary-
symmetric triangle totally nonnegative. -/
theorem elementarySymmetricTriangleFin_isTotallyNonneg
    {w : ℕ → R} (hw : ∀ i, 0 ≤ w i) (N : ℕ) :
    (elementarySymmetricTriangleFin w N).IsTotallyNonneg := by
  rw [elementarySymmetricTriangleFin_eq_stepProduct]
  exact elementarySymmetricStepProduct_isTotallyNonneg hw N N

/-- The infinite elementary-symmetric triangle is totally nonnegative. -/
theorem elementarySymmetricTriangle_isTotallyNonneg
    {w : ℕ → R} (hw : ∀ i, 0 ≤ w i) :
    (elementarySymmetricTriangle w).IsTotallyNonneg := by
  intro n
  cases n with
  | zero => simp
  | succ n =>
      intro rows cols hrows hcols
      let N := max (rows (Fin.last n)) (cols (Fin.last n))
      let rows' : Fin (n + 1) → Fin (N + 1) := fun i =>
        ⟨rows i, by
          exact Nat.lt_succ_of_le
            (le_max_of_le_left (hrows.monotone (Fin.le_last i)))⟩
      let cols' : Fin (n + 1) → Fin (N + 1) := fun i =>
        ⟨cols i, by
          exact Nat.lt_succ_of_le
            (le_max_of_le_right (hcols.monotone (Fin.le_last i)))⟩
      have hfin := elementarySymmetricTriangleFin_isTotallyNonneg hw N
        (rows := rows') (cols := cols')
        (by intro i j hij; exact hrows hij)
        (by intro i j hij; exact hcols hij)
      have hminor :
          (elementarySymmetricTriangleFin w N).submatrix rows' cols' =
            (elementarySymmetricTriangle w).submatrix rows cols := by
        ext i j
        rfl
      rw [hminor] at hfin
      exact hfin

end Ordered

end Ring

end

end Matrix
