import RealRooted.Mathlib.LinearAlgebra.Matrix.GantmacherKrein
import RealRooted.Mathlib.LinearAlgebra.Matrix.Oscillatory

/-!
# Leading-principal interlacing for oscillatory matrices

This file develops the missing all-rank part of the Gantmacher--Krein
oscillation theorem.  The first step below proves the order-one compound case:
the adjacent `2 × 2` minors force a positive diagonal, so the original matrix
is primitive.
-/

namespace Matrix

open scoped BigOperators

section WhitneyDeterminants

variable {R : Type*} [CommRing R]

/-- Adjoin a final column and a final row to a square matrix. -/
private def border {q : ℕ} (A : Matrix (Fin q) (Fin q) R)
    (b x : Fin q → R) (a : R) : Matrix (Fin (q + 1)) (Fin (q + 1)) R :=
  fun i j ↦ Fin.lastCases (motive := fun _ ↦ Fin (q + 1) → R)
    (Fin.snoc x a) (fun k ↦ Fin.snoc (A k) (b k)) i j

/-- Adjoin a row and a column at specified positions. -/
private def borderAt {q : ℕ} (A : Matrix (Fin q) (Fin q) R)
    (rp cp : Fin (q + 1)) (b x : Fin q → R) (a : R) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) R :=
  rp.insertNth (cp.insertNth a x) (fun i ↦ cp.insertNth (b i) (A i))

private lemma insertNth_apply_eq_cons_cycleRange {q : ℕ} {α : Type*}
    (p : Fin (q + 1)) (a : α) (x : Fin q → α) (i : Fin (q + 1)) :
    (@Fin.insertNth q (fun _ ↦ α) p a x) i =
      (@Fin.cons q (fun _ ↦ α) a x) (p.cycleRange i) := by
  simpa [Function.comp_apply] using
    congrFun (Fin.cons_comp_cycleRange a x p).symm i

/-- The bordered determinant acquires the expected row and column insertion
signs.  In particular the two signs cancel when both insertions are final. -/
private theorem det_borderAt {q : ℕ} (A : Matrix (Fin q) (Fin q) R)
    (rp cp : Fin (q + 1)) (b x : Fin q → R) (a : R) :
    (borderAt A rp cp b x a).det =
      (-1 : R) ^ ((rp : ℕ) + (cp : ℕ)) * (border A b x a).det := by
  let F : Matrix (Fin (q + 1)) (Fin (q + 1)) R :=
    Fin.cons (Fin.cons a x) (fun i ↦ Fin.cons (b i) (A i))
  have hat (u v : Fin (q + 1)) : borderAt A u v b x a =
      F.submatrix u.cycleRange v.cycleRange := by
    ext i j
    change (@Fin.insertNth q (fun _ ↦ Fin (q + 1) → R) u
        (@Fin.insertNth q (fun _ ↦ R) v a x)
        (fun k ↦ @Fin.insertNth q (fun _ ↦ R) v (b k) (A k))) i j =
      (@Fin.cons q (fun _ ↦ Fin (q + 1) → R)
        (@Fin.cons q (fun _ ↦ R) a x)
        (fun k ↦ @Fin.cons q (fun _ ↦ R) (b k) (A k)))
          (u.cycleRange i) (v.cycleRange j)
    rw [insertNth_apply_eq_cons_cycleRange]
    change (@Fin.cons q (fun _ ↦ Fin (q + 1) → R)
        (v.insertNth a x) (fun k ↦ v.insertNth (b k) (A k)))
          (u.cycleRange i) j = _
    refine Fin.cases ?_ (fun k ↦ ?_) (u.cycleRange i)
    · exact insertNth_apply_eq_cons_cycleRange v a x j
    · exact insertNth_apply_eq_cons_cycleRange v (b _) (A _) j
  have hborderAtLast : borderAt A (Fin.last q) (Fin.last q) b x a =
      border A b x a := by
    ext i j
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · simp [borderAt, border]
    · refine Fin.lastCases ?_ (fun j ↦ ?_) j <;>
        simp [borderAt, border]
  have hlast : border A b x a =
      F.submatrix (Fin.last q).cycleRange (Fin.last q).cycleRange := by
    rw [← hborderAtLast]
    exact hat (Fin.last q) (Fin.last q)
  have hdet (u v : Fin (q + 1)) :
      (F.submatrix u.cycleRange v.cycleRange).det =
        (-1 : R) ^ ((u : ℕ) + (v : ℕ)) * F.det := by
    calc
      (F.submatrix u.cycleRange v.cycleRange).det =
          ((F.submatrix id v.cycleRange).submatrix u.cycleRange id).det := by
            rfl
      _ = (Equiv.Perm.sign u.cycleRange : R) *
          (F.submatrix id v.cycleRange).det :=
            Matrix.det_permute u.cycleRange _
      _ = (Equiv.Perm.sign u.cycleRange : R) *
          ((Equiv.Perm.sign v.cycleRange : R) * F.det) := by
            rw [Matrix.det_permute']
      _ = (-1 : R) ^ ((u : ℕ) + (v : ℕ)) * F.det := by
            simp [pow_add, mul_assoc]
  have hlastSign : (-1 : R) ^ (q + q) = 1 := by
    rw [show q + q = 2 * q by lia, pow_mul]
    simp
  rw [hat, hdet, hlast, hdet]
  simp only [Fin.val_last, hlastSign]
  ring

@[simp] private lemma border_castSucc_castSucc {q : ℕ}
    (A : Matrix (Fin q) (Fin q) R) (b x : Fin q → R) (a : R)
    (i j : Fin q) :
    border A b x a i.castSucc j.castSucc = A i j := by
  simp [border]

@[simp] private lemma border_castSucc_last {q : ℕ}
    (A : Matrix (Fin q) (Fin q) R) (b x : Fin q → R) (a : R)
    (i : Fin q) :
    border A b x a i.castSucc (Fin.last q) = b i := by
  simp [border]

@[simp] private lemma border_last_castSucc {q : ℕ}
    (A : Matrix (Fin q) (Fin q) R) (b x : Fin q → R) (a : R)
    (j : Fin q) :
    border A b x a (Fin.last q) j.castSucc = x j := by
  simp [border]

@[simp] private lemma border_last_last {q : ℕ}
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
private theorem det_border_plucker {q : ℕ}
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

/-- The bordered-minor identity with the adjoined row and column inserted in
arbitrary positions.  This is the order-aware form used for naturally ordered
minors in Whitney elimination. -/
private theorem det_borderAt_plucker {q : ℕ}
    (A : Matrix (Fin q) (Fin q) R) (r0 : Fin q)
    (rp cp : Fin (q + 1)) (b x y c d : Fin q → R)
    (alpha beta : R) (hx : c ᵥ* A = x) (hy : d ᵥ* A = y) :
    A.det * (borderAt (A.updateRow r0 x) rp cp
        (Function.update b r0 alpha) y beta).det =
      (A.updateRow r0 x).det * (borderAt A rp cp b y beta).det -
        (A.updateRow r0 y).det * (borderAt A rp cp b x alpha).det := by
  have hborderUpdate :
      border (A.updateRow r0 x) (Function.update b r0 alpha) y beta =
        (border A b y beta).updateRow r0.castSucc (Fin.snoc x alpha) := by
    ext i j
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · rw [Matrix.updateRow_ne (Fin.castSucc_ne_last r0).symm]
      simp [border]
    · by_cases hi : i = r0
      · subst i
        refine Fin.lastCases ?_ (fun j ↦ ?_) j <;>
          simp [border, Function.update]
      · refine Fin.lastCases ?_ (fun j ↦ ?_) j <;>
          simp [border, Matrix.updateRow, Function.update, hi]
  have hfinal := det_border_plucker A r0 b x y c d alpha beta hx hy
  rw [← hborderUpdate] at hfinal
  rw [det_borderAt, det_borderAt, det_borderAt]
  linear_combination (-1 : R) ^ ((rp : ℕ) + (cp : ℕ)) * hfinal

/-- Expansion of a top-left border whose new column vanishes below its first
old row. -/
private theorem det_borderAt_zero_zero_of_tail {q : ℕ}
    (A : Matrix (Fin (q + 1)) (Fin (q + 1)) R)
    (b x : Fin (q + 1) → R) (a : R)
    (hb : ∀ i, 0 < i → b i = 0) :
    (borderAt A 0 0 b x a).det =
      a * A.det - b 0 * (A.updateRow 0 x).det := by
  let M := borderAt A 0 0 b x a
  have hminor0 : M.submatrix (0 : Fin (q + 2)).succAbove Fin.succ = A := by
    ext i j
    simp [M, borderAt]
  have hminor1 : M.submatrix (1 : Fin (q + 2)).succAbove Fin.succ =
      A.updateRow 0 x := by
    ext i j
    refine Fin.cases ?_ (fun i ↦ ?_) i <;>
      simp [M, borderAt, Matrix.updateRow]
  have hminor1' :
      M.submatrix (Fin.succ (0 : Fin (q + 1))).succAbove Fin.succ =
        A.updateRow 0 x := by
    simpa using hminor1
  rw [Matrix.det_succ_column_zero M, Fin.sum_univ_succ,
    Fin.sum_univ_succ, hminor0, hminor1']
  have htail : ∑ i : Fin q,
      (-1 : R) ^ ((i.succ.succ : Fin (q + 2)) : ℕ) *
        M i.succ.succ 0 *
          (M.submatrix i.succ.succ.succAbove Fin.succ).det = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hbi : b i.succ = 0 := hb i.succ (by simp)
    simp [M, borderAt, hbi]
  rw [htail]
  simp [M, borderAt]
  ring

end WhitneyDeterminants

section WhitneyElimination

/-- One step of Whitney--Neville elimination in the first column: subtract
from row `s + 1` the pivot ratio times row `s`. -/
noncomputable def whitneyEliminateFirst {m n : ℕ}
    (A : Matrix (Fin (m + 2)) (Fin (n + 1)) ℝ) (s : Fin (m + 1)) :
    Matrix (Fin (m + 2)) (Fin (n + 1)) ℝ :=
  A.updateRow s.succ fun j ↦
    A s.succ j - (A s.succ 0 / A s.castSucc 0) * A s.castSucc j

private theorem det_submatrix_whitneyEliminateFirst {m n q : ℕ}
    (A : Matrix (Fin (m + 2)) (Fin (n + 1)) ℝ) (s : Fin (m + 1))
    (rows : Fin q → Fin (m + 2)) (cols : Fin q → Fin (n + 1))
    (hrows : StrictMono rows) (p : Fin q) (hp : rows p = s.succ) :
    ((whitneyEliminateFirst A s).submatrix rows cols).det =
      (A.submatrix rows cols).det -
        (A s.succ 0 / A s.castSucc 0) *
          (A.submatrix (Function.update rows p s.castSucc) cols).det := by
  let M := A.submatrix rows cols
  let v : Fin q → ℝ := fun j ↦ A s.castSucc (cols j)
  have hmatrix : (whitneyEliminateFirst A s).submatrix rows cols =
      M.updateRow p (M p - (A s.succ 0 / A s.castSucc 0) • v) := by
    ext i j
    by_cases hi : i = p
    · subst i
      simp [whitneyEliminateFirst, M, v, hp, Pi.smul_apply]
    · have hrow : rows i ≠ s.succ := by
        intro h
        exact hi (hrows.injective (h.trans hp.symm))
      simp [whitneyEliminateFirst, M, v, Matrix.updateRow, hi, hrow]
  have hreplace : M.updateRow p v =
      A.submatrix (Function.update rows p s.castSucc) cols := by
    ext i j
    by_cases hi : i = p
    · subst i
      simp [M, v, Function.update]
    · simp [M, v, Matrix.updateRow, Function.update, hi]
  have hneg : -((A s.succ 0 / A s.castSucc 0) • v) =
      (-(A s.succ 0 / A s.castSucc 0)) • v := by
    simp
  rw [hmatrix, sub_eq_add_neg, Matrix.det_updateRow_add, hneg,
    Matrix.det_updateRow_smul, Matrix.updateRow_eq_self M p, hreplace]
  change (A.submatrix rows cols).det + _ = _
  ring

private theorem submatrix_whitneyEliminateFirst_eq_of_not_mem {m n q : ℕ}
    (A : Matrix (Fin (m + 2)) (Fin (n + 1)) ℝ) (s : Fin (m + 1))
    (rows : Fin q → Fin (m + 2)) (cols : Fin q → Fin (n + 1))
    (hu : ∀ i, rows i ≠ s.succ) :
    (whitneyEliminateFirst A s).submatrix rows cols =
      A.submatrix rows cols := by
  ext i j
  simp [whitneyEliminateFirst, Matrix.updateRow, hu i]

private theorem det_submatrix_whitneyEliminateFirst_eq_of_pivot_mem
    {m n q : ℕ}
    (A : Matrix (Fin (m + 2)) (Fin (n + 1)) ℝ) (s : Fin (m + 1))
    (rows : Fin q → Fin (m + 2)) (cols : Fin q → Fin (n + 1))
    (hrows : StrictMono rows) (p r : Fin q)
    (hp : rows p = s.succ) (hr : rows r = s.castSucc) :
    ((whitneyEliminateFirst A s).submatrix rows cols).det =
      (A.submatrix rows cols).det := by
  have hpr : p ≠ r := by
    intro h
    subst r
    have : s.succ = s.castSucc := hp.symm.trans hr
    exact Fin.ne_of_gt s.castSucc_lt_succ this
  let M := A.submatrix rows cols
  have hreplace : A.submatrix (Function.update rows p s.castSucc) cols =
      M.updateRow p (M r) := by
    ext i j
    by_cases hi : i = p
    · subst i
      simp [M, Function.update, hr]
    · simp [M, Function.update, Matrix.updateRow, hi]
  have hzero :
      (A.submatrix (Function.update rows p s.castSucc) cols).det = 0 := by
    rw [hreplace]
    exact Matrix.det_updateRow_eq_zero hpr.symm
  rw [det_submatrix_whitneyEliminateFirst A s rows cols hrows p hp,
    hzero, mul_zero, sub_zero]

private theorem det_submatrix_whitneyEliminateFirst_eq_zero_of_first_col
    {m n q : ℕ}
    (A : Matrix (Fin (m + 2)) (Fin (n + 1)) ℝ) (s : Fin (m + 1))
    (rows : Fin (q + 1) → Fin (m + 2))
    (cols : Fin (q + 1) → Fin (n + 1))
    (hrows : StrictMono rows) (hrow0 : rows 0 = s.succ)
    (hcol0 : cols 0 = 0) (hpivot : 0 < A s.castSucc 0)
    (htail : ∀ i, s.succ < i → A i 0 = 0) :
    ((whitneyEliminateFirst A s).submatrix rows cols).det = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero 0
  intro i
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · simp [whitneyEliminateFirst, hrow0, hcol0, hpivot.ne']
  · have hgt : s.succ < rows k.succ := by
      rw [← hrow0]
      exact hrows (by simp)
    have hne : rows k.succ ≠ s.succ := ne_of_gt hgt
    simp [whitneyEliminateFirst, hcol0, Matrix.updateRow, hne,
      htail _ hgt]

private theorem det_submatrix_whitneyEliminateFirst_nonneg_of_first_row
    {m n q : ℕ}
    (A : Matrix (Fin (m + 2)) (Fin (n + 1)) ℝ) (s : Fin (m + 1))
    (hA : A.IsTotallyNonnegRect) (hpivot : 0 < A s.castSucc 0)
    (htail : ∀ i, s.succ < i → A i 0 = 0)
    (rows : Fin (q + 1) → Fin (m + 2))
    (cols : Fin (q + 1) → Fin (n + 1))
    (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hrow0 : rows 0 = s.succ) (hcol0 : 0 < cols 0) :
    0 ≤ ((whitneyEliminateFirst A s).submatrix rows cols).det := by
  let M := A.submatrix rows cols
  let b : Fin (q + 1) → ℝ := fun i ↦ A (rows i) 0
  let x : Fin (q + 1) → ℝ := fun j ↦ A s.castSucc (cols j)
  let augRows : Fin (q + 2) → Fin (m + 2) := Fin.cons s.castSucc rows
  let augCols : Fin (q + 2) → Fin (n + 1) := Fin.cons 0 cols
  have haugRows : StrictMono augRows := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · simpa [augRows, hrow0] using s.castSucc_lt_succ
    · simpa [augRows] using
        (Fin.strictMono_iff_lt_succ.mp hrows k)
  have haugCols : StrictMono augCols := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · simpa [augCols] using hcol0
    · simpa [augCols] using
        (Fin.strictMono_iff_lt_succ.mp hcols k)
  have hborder : borderAt M 0 0 b x (A s.castSucc 0) =
      A.submatrix augRows augCols := by
    ext i j
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · refine Fin.cases ?_ (fun j ↦ ?_) j <;>
        simp [M, b, x, augRows, augCols, borderAt]
    · refine Fin.cases ?_ (fun j ↦ ?_) j <;>
        simp [M, b, x, augRows, augCols, borderAt]
  have hb : ∀ i, 0 < i → b i = 0 := by
    intro i hi
    have hgt : s.succ < rows i := by
      rw [← hrow0]
      exact hrows hi
    exact htail _ hgt
  have hreplace : M.updateRow 0 x =
      A.submatrix (Function.update rows 0 s.castSucc) cols := by
    ext i j
    refine Fin.cases ?_ (fun i ↦ ?_) i <;>
      simp [M, x, Function.update, Matrix.updateRow]
  have hprod : A s.castSucc 0 *
      ((whitneyEliminateFirst A s).submatrix rows cols).det =
        (borderAt M 0 0 b x (A s.castSucc 0)).det := by
    rw [det_submatrix_whitneyEliminateFirst A s rows cols hrows 0 hrow0,
      det_borderAt_zero_zero_of_tail M b x (A s.castSucc 0) hb,
      hreplace]
    simp only [M, b, hrow0]
    field_simp [hpivot.ne']
  have hborderNonneg :
      0 ≤ (borderAt M 0 0 b x (A s.castSucc 0)).det := by
    rw [hborder]
    exact hA haugRows haugCols
  nlinarith

/-- The ordered-minor inequality in the hard Whitney induction branch, after
the three-term bordered identity and the smaller eliminated minor have been
identified. -/
private theorem whitney_hard_minor_nonneg
    {pivot lower D0 DA DC P Q E small : ℝ}
    (hpivot : 0 < pivot) (hD0 : 0 < D0)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hDC : 0 ≤ DC)
    (hsmall : 0 ≤ small)
    (hplucker : D0 * DA = P * Q + E * DC)
    (hsmallEq : pivot * small = pivot * E - lower * D0) :
    0 ≤ DA - (lower / pivot) * DC := by
  have hfactor : 0 < pivot * D0 := mul_pos hpivot hD0
  have hnonneg :
      0 ≤ pivot * (P * Q) + DC * (pivot * small) :=
    add_nonneg (mul_nonneg hpivot.le (mul_nonneg hP hQ))
      (mul_nonneg hDC (mul_nonneg hpivot.le hsmall))
  have hid : pivot * D0 * (DA - (lower / pivot) * DC) =
      pivot * (P * Q) + DC * (pivot * small) := by
    field_simp [hpivot.ne']
    nlinarith [hplucker, hsmallEq]
  nlinarith

end WhitneyElimination

/-- In a TN matrix with positive adjacent off-diagonal entries, the two
diagonal entries at every adjacent pair are positive. -/
theorem IsTotallyNonneg.adjacent_diagonal_pos {n : ℕ}
    {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ}
    (hA : A.IsTotallyNonneg)
    (hsuper : ∀ i : Fin (n + 1), 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin (n + 1), 0 < A i.succ i.castSucc)
    (i : Fin (n + 1)) :
    0 < A i.castSucc i.castSucc ∧ 0 < A i.succ i.succ := by
  let pair : Fin 2 → Fin (n + 2) := ![i.castSucc, i.succ]
  have hpair : StrictMono pair := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [pair]
  have hminor := hA hpair hpair
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, pair,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hminor
  have hcross : 0 < A i.castSucc i.succ * A i.succ i.castSucc :=
    mul_pos (hsuper i) (hsub i)
  have hdiag : 0 < A i.castSucc i.castSucc * A i.succ i.succ := by
    linarith
  constructor
  · nlinarith [hA.nonneg i.castSucc i.castSucc,
      hA.nonneg i.succ i.succ]
  · nlinarith [hA.nonneg i.castSucc i.castSucc,
      hA.nonneg i.succ i.succ]

/-- Positive adjacent off-diagonal entries in a TN matrix of size at least two
force every diagonal entry to be positive. -/
theorem IsTotallyNonneg.diagonal_pos_of_adjacent_pos {n : ℕ}
    {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ}
    (hA : A.IsTotallyNonneg)
    (hsuper : ∀ i : Fin (n + 1), 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin (n + 1), 0 < A i.succ i.castSucc) :
    ∀ i, 0 < A i i := by
  intro i
  refine Fin.cases ?_ (fun k ↦ (hA.adjacent_diagonal_pos hsuper hsub k).2) i
  exact (hA.adjacent_diagonal_pos hsuper hsub 0).1

/-- The matrix itself (the order-one compound) in the oscillation criterion is
primitive. -/
theorem IsTotallyNonneg.isPrimitive_of_adjacent_pos {n : ℕ}
    {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ}
    (hA : A.IsTotallyNonneg)
    (hsuper : ∀ i : Fin (n + 1), 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin (n + 1), 0 < A i.succ i.castSucc) :
    A.IsPrimitive :=
  IsPrimitive.of_irreducible_pos_diagonal A hA.nonneg
    (isIrreducible_of_nonneg_of_adjacent_pos hA.nonneg hsuper hsub)
    (hA.diagonal_pos_of_adjacent_pos hsuper hsub)

/-- The nonsingular TN adjacent-diagonal criterion makes the order-one
compound primitive in every positive dimension. -/
theorem IsTotallyNonneg.isPrimitive_of_det_ne_zero_of_adjacent_pos
    {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0)
    (hsuper : ∀ i : Fin n, 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin n, 0 < A i.succ i.castSucc) :
    A.IsPrimitive := by
  cases n with
  | zero =>
      apply IsPrimitive.of_irreducible_pos_diagonal A hA.nonneg
        (hA.isIrreducible_of_det_ne_zero_of_adjacent_pos hdet hsuper hsub)
      intro i
      rw [Fin.eq_zero i]
      have hne : A 0 0 ≠ 0 := by
        simpa [Matrix.det_fin_one] using hdet
      exact lt_of_le_of_ne (hA.nonneg 0 0) hne.symm
  | succ n =>
      exact hA.isPrimitive_of_adjacent_pos hsuper hsub

/-- The leading principal section of a TN matrix with positive adjacent
off-diagonal entries is primitive. -/
theorem IsTotallyNonneg.leadingPrincipal_isPrimitive_of_adjacent_pos
    {n : ℕ} {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ}
    (hA : A.IsTotallyNonneg)
    (hsuper : ∀ i : Fin (n + 1), 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin (n + 1), 0 < A i.succ i.castSucc) :
    (A.submatrix Fin.castSucc Fin.castSucc).IsPrimitive := by
  let B := A.submatrix Fin.castSucc Fin.castSucc
  have hB : B.IsTotallyNonneg :=
    hA.submatrix Fin.strictMono_castSucc Fin.strictMono_castSucc
  cases n with
  | zero =>
      apply IsPrimitive.of_irreducible_pos_diagonal B hB.nonneg
      · apply hB.isIrreducible_of_det_ne_zero_of_adjacent_pos
        · have h00 := (hA.adjacent_diagonal_pos hsuper hsub 0).1
          simpa [B, Matrix.det_fin_one] using h00.ne'
        · exact fun i ↦ Fin.elim0 i
        · exact fun i ↦ Fin.elim0 i
      · intro i
        rw [Fin.eq_zero i]
        simpa [B] using (hA.adjacent_diagonal_pos hsuper hsub 0).1
  | succ n =>
      apply hB.isPrimitive_of_adjacent_pos
      · intro i
        simpa [B] using hsuper i.castSucc
      · intro i
        simpa [B] using hsub i.castSucc

end Matrix
