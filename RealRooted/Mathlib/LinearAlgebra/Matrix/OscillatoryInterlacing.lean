import RealRooted.Mathlib.LinearAlgebra.Matrix.GantmacherKrein
import RealRooted.Mathlib.LinearAlgebra.Matrix.Oscillatory
import RealRooted.CauchyInterlacing
import RealRooted.Basic
import RealRooted.Challenges.CauchyInterlacing
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Matrix.Transvection
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Charpoly

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

private lemma borderAt_submatrix {q : ℕ} {ι κ : Type*}
    (M : Matrix ι κ R) (rows : Fin q → ι) (cols : Fin q → κ)
    (rp cp : Fin (q + 1)) (row : ι) (col : κ) :
    borderAt (M.submatrix rows cols) rp cp
        (fun i ↦ M (rows i) col) (fun j ↦ M row (cols j)) (M row col) =
      M.submatrix (rp.insertNth row rows) (cp.insertNth col cols) := by
  ext i j
  refine Fin.succAboveCases rp ?_ (fun i' ↦ ?_) i
  · refine Fin.succAboveCases cp ?_ (fun j' ↦ ?_) j <;> simp [borderAt]
  · refine Fin.succAboveCases cp ?_ (fun j' ↦ ?_) j <;> simp [borderAt]

private lemma updateRow_submatrix {q : ℕ} {ι κ : Type*}
    [DecidableEq (Fin q)] (M : Matrix ι κ R)
    (rows : Fin q → ι) (cols : Fin q → κ) (r : Fin q) (row : ι) :
    (M.submatrix rows cols).updateRow r (fun j ↦ M row (cols j)) =
      M.submatrix (Function.update rows r row) cols := by
  ext i j
  by_cases hi : i = r <;>
    simp [Matrix.updateRow, Function.update, hi]

private lemma strictMono_update_at {q : ℕ} {ι : Type*} [LinearOrder ι]
    (f : Fin q → ι) (p : Fin q) (x : ι) (hf : StrictMono f)
    (hleft : ∀ i, i < p → f i < x)
    (hright : ∀ i, p < i → x < f i) :
    StrictMono (Function.update f p x) := by
  intro i j hij
  by_cases hi : i = p
  · subst i
    have hj : j ≠ p := ne_of_gt hij
    simpa [Function.update, hj] using hright j hij
  · by_cases hj : j = p
    · subst j
      simp [Function.update, hi, hleft i hij]
    · simpa [Function.update, hi, hj] using hf hij

/-- The five adjacent deletion/insertion identities used to recognize every
matrix in Whitney's hard branch as a naturally ordered minor. -/
private theorem whitney_adjacent_selector_identities {q : ℕ} {ι : Type*}
    [DecidableEq ι] (rows : Fin (q + 1) → ι) (r : Fin q)
    (pivot prior changed : ι)
    (hchanged : rows r.succ = changed)
    (hprior : rows r.castSucc = prior) :
    let replaced := Function.update rows r.succ pivot
    let base := r.castSucc.removeNth replaced
    Function.update base r prior = r.succ.removeNth rows ∧
      Function.update base r changed = r.castSucc.removeNth rows ∧
      r.succ.insertNth changed (Function.update base r prior) = rows ∧
      r.succ.insertNth changed base = Function.update rows r.castSucc pivot ∧
      r.castSucc.insertNth prior base = replaced := by
  classical
  let replaced := Function.update rows r.succ pivot
  let base := r.castSucc.removeNth replaced
  have hpositions : r.castSucc ≠ r.succ := Fin.ne_of_lt r.castSucc_lt_succ
  have hP : Function.update base r prior = r.succ.removeNth rows := by
    ext i
    rcases lt_trichotomy i r with hir | rfl | hri
    · have hir' : i.castSucc < r.succ :=
        Fin.castSucc_lt_succ_iff.2 hir.le
      simp [base, replaced, Fin.removeNth,
        Fin.succAbove_castSucc_of_lt _ _ hir,
        Fin.succAbove_succ_of_le _ _ hir.le, Function.update,
        ne_of_lt hir, ne_of_lt hir']
    · simp [base, replaced, Fin.removeNth, Function.update, hprior]
    · have hne : i ≠ r := ne_of_gt hri
      have hne' : i.succ ≠ r.succ := by simpa
      simp [base, replaced, Fin.removeNth,
        Fin.succAbove_castSucc_of_le _ _ hri.le,
        Fin.succAbove_succ_of_lt _ _ hri, Function.update, hne, hne']
  have hE : Function.update base r changed = r.castSucc.removeNth rows := by
    ext i
    rcases lt_trichotomy i r with hir | rfl | hri
    · have hir' : i.castSucc < r.succ :=
        Fin.castSucc_lt_succ_iff.2 hir.le
      simp [base, replaced, Fin.removeNth,
        Fin.succAbove_castSucc_of_lt _ _ hir, Function.update,
        ne_of_lt hir, ne_of_lt hir']
    · simp [base, replaced, Fin.removeNth, Function.update, hchanged]
    · have hne : i ≠ r := ne_of_gt hri
      have hne' : i.succ ≠ r.succ := by simpa
      simp [base, replaced, Fin.removeNth,
        Fin.succAbove_castSucc_of_le _ _ hri.le, Function.update, hne, hne']
  have hDA : r.succ.insertNth changed (Function.update base r prior) = rows := by
    exact Fin.insertNth_eq_iff.2 ⟨hchanged.symm, hP⟩
  have hQ : r.succ.insertNth changed base =
      Function.update rows r.castSucc pivot := by
    apply Fin.insertNth_eq_iff.2
    constructor
    · simp [Function.update, hpositions.symm, hchanged]
    · ext i
      rcases lt_trichotomy i r with hir | rfl | hri
      · have hir' : i.castSucc < r.succ :=
          Fin.castSucc_lt_succ_iff.2 hir.le
        simp [base, replaced, Fin.removeNth,
          Fin.succAbove_castSucc_of_lt _ _ hir,
          Fin.succAbove_succ_of_le _ _ hir.le, Function.update,
          ne_of_lt hir, ne_of_lt hir']
      · simp [base, replaced, Fin.removeNth, Function.update]
      · have hne : i.succ ≠ r.castSucc := by
          exact ne_of_gt (lt_trans r.castSucc_lt_succ (Fin.succ_lt_succ_iff.2 hri))
        have hne' : i.succ ≠ r.succ := by simpa using ne_of_gt hri
        simp [base, replaced, Fin.removeNth,
          Fin.succAbove_castSucc_of_le _ _ hri.le,
          Fin.succAbove_succ_of_lt _ _ hri, Function.update, hne, hne']
  have hDC : r.castSucc.insertNth prior base = replaced := by
    apply Fin.insertNth_eq_iff.2
    constructor
    · simp [replaced, Function.update, hpositions, hprior]
    · rfl
  exact ⟨hP, hE, hDA, hQ, hDC⟩

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

/-- Moving an inserted row one place to the right changes the bordered
determinant's sign. -/
private theorem det_borderAt_pred_insert {q : ℕ}
    (A : Matrix (Fin q) (Fin q) R)
    (p : Fin (q + 1)) (hp : p ≠ 0) (cp : Fin (q + 1))
    (b x : Fin q → R) (a : R) :
    (borderAt A p cp b x a).det =
      -(borderAt A (p.pred hp).castSucc cp b x a).det := by
  rw [det_borderAt, det_borderAt]
  have hpval : (p : ℕ) = (p.pred hp : ℕ) + 1 := by
    rw [← Fin.val_succ, Fin.succ_pred p hp]
  rw [hpval]
  simp only [Fin.val_castSucc]
  rw [show (p.pred hp : ℕ) + 1 + (cp : ℕ) =
      ((p.pred hp : ℕ) + (cp : ℕ)) + 1 by lia, pow_succ']
  ring

end WhitneyDeterminants

section WhitneyElimination

/-- One step of Whitney--Neville elimination in a selected column: subtract
from row `s + 1` the pivot ratio times row `s`. -/
noncomputable def whitneyEliminateAt {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m)
    (c : Fin (n + 1)) :
    Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ :=
  A.updateRow s.succ fun j ↦
    A s.succ j - (A s.succ c / A s.castSucc c) * A s.castSucc j

/-- Whitney--Neville elimination specialized to the first column. -/
noncomputable def whitneyEliminateFirst {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m) :
    Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ :=
  whitneyEliminateAt A s 0

@[simp] private theorem whitneyEliminateAt_apply_same {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m)
    (c : Fin (n + 1)) (j : Fin (n + 1)) :
    whitneyEliminateAt A s c s.succ j =
      A s.succ j - (A s.succ c / A s.castSucc c) * A s.castSucc j := by
  simp [whitneyEliminateAt]

@[simp] private theorem whitneyEliminateAt_apply_of_ne {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m)
    (c : Fin (n + 1)) (i : Fin (m + 1)) (j : Fin (n + 1))
    (hi : i ≠ s.succ) :
    whitneyEliminateAt A s c i j = A i j := by
  simp [whitneyEliminateAt, hi]

private theorem det_submatrix_whitneyEliminateFirst {m n q : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m)
    (rows : Fin q → Fin (m + 1)) (cols : Fin q → Fin (n + 1))
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
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m)
    (rows : Fin q → Fin (m + 1)) (cols : Fin q → Fin (n + 1))
    (hu : ∀ i, rows i ≠ s.succ) :
    (whitneyEliminateFirst A s).submatrix rows cols =
      A.submatrix rows cols := by
  ext i j
  simp [whitneyEliminateFirst, hu i]

private theorem det_submatrix_whitneyEliminateAt {m n q : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m)
    (c : Fin (n + 1)) (rows : Fin q → Fin (m + 1))
    (cols : Fin q → Fin (n + 1)) (hrows : StrictMono rows)
    (p : Fin q) (hp : rows p = s.succ) :
    ((whitneyEliminateAt A s c).submatrix rows cols).det =
      (A.submatrix rows cols).det -
        (A s.succ c / A s.castSucc c) *
          (A.submatrix (Function.update rows p s.castSucc) cols).det := by
  let M := A.submatrix rows cols
  let v : Fin q → ℝ := fun j ↦ A s.castSucc (cols j)
  have hmatrix : (whitneyEliminateAt A s c).submatrix rows cols =
      M.updateRow p (M p - (A s.succ c / A s.castSucc c) • v) := by
    ext i j
    by_cases hi : i = p
    · subst i
      simp [whitneyEliminateAt, M, v, hp, Pi.smul_apply]
    · have hrow : rows i ≠ s.succ := by
        intro h
        exact hi (hrows.injective (h.trans hp.symm))
      simp [whitneyEliminateAt, M, v, Matrix.updateRow, hi, hrow]
  have hreplace : M.updateRow p v =
      A.submatrix (Function.update rows p s.castSucc) cols := by
    ext i j
    by_cases hi : i = p
    · subst i
      simp [M, v, Function.update]
    · simp [M, v, Matrix.updateRow, Function.update, hi]
  have hneg : -((A s.succ c / A s.castSucc c) • v) =
      (-(A s.succ c / A s.castSucc c)) • v := by
    simp
  rw [hmatrix, sub_eq_add_neg, Matrix.det_updateRow_add, hneg,
    Matrix.det_updateRow_smul, Matrix.updateRow_eq_self M p, hreplace]
  change (A.submatrix rows cols).det + _ = _
  ring

private theorem submatrix_whitneyEliminateAt_eq_of_not_mem {m n q : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m)
    (c : Fin (n + 1)) (rows : Fin q → Fin (m + 1))
    (cols : Fin q → Fin (n + 1)) (hu : ∀ i, rows i ≠ s.succ) :
    (whitneyEliminateAt A s c).submatrix rows cols =
      A.submatrix rows cols := by
  ext i j
  simp [whitneyEliminateAt, Matrix.updateRow, hu i]

private theorem det_submatrix_whitneyEliminateAt_eq_of_pivot_mem
    {m n q : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ)
    (s : Fin m) (c : Fin (n + 1))
    (rows : Fin q → Fin (m + 1)) (cols : Fin q → Fin (n + 1))
    (hrows : StrictMono rows) (p r : Fin q)
    (hp : rows p = s.succ) (hr : rows r = s.castSucc) :
    ((whitneyEliminateAt A s c).submatrix rows cols).det =
      (A.submatrix rows cols).det := by
  have hpr : p ≠ r := by
    intro h
    subst r
    exact Fin.ne_of_gt s.castSucc_lt_succ (hp.symm.trans hr)
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
  rw [det_submatrix_whitneyEliminateAt A s c rows cols hrows p hp,
    hzero, mul_zero, sub_zero]

private theorem det_submatrix_whitneyEliminateFirst_eq_of_pivot_mem
    {m n q : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m)
    (rows : Fin q → Fin (m + 1)) (cols : Fin q → Fin (n + 1))
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
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m)
    (rows : Fin (q + 1) → Fin (m + 1))
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
    simp [whitneyEliminateFirst, hcol0, hne, htail _ hgt]

private theorem det_submatrix_whitneyEliminateFirst_nonneg_of_first_row
    {m n q : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m)
    (hA : A.IsTotallyNonnegRect) (hpivot : 0 < A s.castSucc 0)
    (htail : ∀ i, s.succ < i → A i 0 = 0)
    (rows : Fin (q + 1) → Fin (m + 1))
    (cols : Fin (q + 1) → Fin (n + 1))
    (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hrow0 : rows 0 = s.succ) (hcol0 : 0 < cols 0) :
    0 ≤ ((whitneyEliminateFirst A s).submatrix rows cols).det := by
  let M := A.submatrix rows cols
  let b : Fin (q + 1) → ℝ := fun i ↦ A (rows i) 0
  let x : Fin (q + 1) → ℝ := fun j ↦ A s.castSucc (cols j)
  let augRows : Fin (q + 2) → Fin (m + 1) := Fin.cons s.castSucc rows
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

private theorem det_submatrix_whitneyEliminateAt_eq_zero_of_initial_col
    {m n q : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ)
    (s : Fin m) (c : Fin (n + 1))
    (rows : Fin (q + 1) → Fin (m + 1))
    (cols : Fin (q + 1) → Fin (n + 1))
    (hrows : StrictMono rows) (hrow0 : rows 0 = s.succ)
    (hcol : cols 0 ≤ c) (hpivot : 0 < A s.castSucc c)
    (htail : ∀ i, s.succ < i → A i c = 0)
    (hleft : ∀ i, s.castSucc ≤ i → ∀ j, j < c → A i j = 0) :
    ((whitneyEliminateAt A s c).submatrix rows cols).det = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero 0
  intro i
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · rcases hcol.eq_or_lt with hcolEq | hcolLt
    · have hc : cols 0 = c := hcolEq
      simp [whitneyEliminateAt, hrow0, hc, hpivot.ne']
    · have htarget : A s.succ (cols 0) = 0 :=
        hleft s.succ (Fin.le_def.mpr (by simp)) _ hcolLt
      have hpivotLeft : A s.castSucc (cols 0) = 0 :=
        hleft s.castSucc le_rfl _ hcolLt
      simp [whitneyEliminateAt, hrow0, htarget, hpivotLeft]
  · have hgt : s.succ < rows k.succ := by
      rw [← hrow0]
      exact hrows (by simp)
    have hne : rows k.succ ≠ s.succ := ne_of_gt hgt
    rcases hcol.eq_or_lt with hcolEq | hcolLt
    · have hc : cols 0 = c := hcolEq
      simp [whitneyEliminateAt, hc, Matrix.updateRow, hne, htail _ hgt]
    · have hzero : A (rows k.succ) (cols 0) = 0 :=
        hleft (rows k.succ) (le_trans (Fin.le_def.mpr (by simp)) hgt.le)
          _ hcolLt
      simp [whitneyEliminateAt, Matrix.updateRow, hne, hzero]

private theorem det_submatrix_whitneyEliminateAt_nonneg_of_first_row
    {m n q : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ)
    (s : Fin m) (c : Fin (n + 1)) (hA : A.IsTotallyNonnegRect)
    (hpivot : 0 < A s.castSucc c)
    (htail : ∀ i, s.succ < i → A i c = 0)
    (rows : Fin (q + 1) → Fin (m + 1))
    (cols : Fin (q + 1) → Fin (n + 1))
    (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hrow0 : rows 0 = s.succ) (hcol : c < cols 0) :
    0 ≤ ((whitneyEliminateAt A s c).submatrix rows cols).det := by
  let M := A.submatrix rows cols
  let b : Fin (q + 1) → ℝ := fun i ↦ A (rows i) c
  let x : Fin (q + 1) → ℝ := fun j ↦ A s.castSucc (cols j)
  let augRows : Fin (q + 2) → Fin (m + 1) := Fin.cons s.castSucc rows
  let augCols : Fin (q + 2) → Fin (n + 1) := Fin.cons c cols
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
    · simpa [augCols] using hcol
    · simpa [augCols] using
        (Fin.strictMono_iff_lt_succ.mp hcols k)
  have hborder : borderAt M 0 0 b x (A s.castSucc c) =
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
  have hprod : A s.castSucc c *
      ((whitneyEliminateAt A s c).submatrix rows cols).det =
        (borderAt M 0 0 b x (A s.castSucc c)).det := by
    rw [det_submatrix_whitneyEliminateAt A s c rows cols hrows 0 hrow0,
      det_borderAt_zero_zero_of_tail M b x (A s.castSucc c) hb,
      hreplace]
    simp only [M, b, hrow0]
    field_simp [hpivot.ne']
  have hborderNonneg :
      0 ≤ (borderAt M 0 0 b x (A s.castSucc c)).det := by
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

private theorem exists_pos_deleted_minor_of_det_pos {q : ℕ}
    (M : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (r : Fin (q + 1))
    (hminor : ∀ j : Fin (q + 1),
      0 ≤ (M.submatrix r.succAbove j.succAbove).det)
    (hdet : 0 < M.det) :
    ∃ j : Fin (q + 1),
      0 < (M.submatrix r.succAbove j.succAbove).det := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hzero : ∀ j : Fin (q + 1),
      (M.submatrix r.succAbove j.succAbove).det = 0 := by
    intro j
    exact le_antisymm (h j) (hminor j)
  rw [Matrix.det_succ_row M r] at hdet
  simp [hzero] at hdet

/-- Whitney's one-row elimination preserves total nonnegativity when the
eliminated entry is followed by a zero tail in the first column. -/
theorem IsTotallyNonnegRect.whitneyEliminateFirst {m n : ℕ}
    {A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonnegRect) (s : Fin m)
    (hpivot : 0 < A s.castSucc 0)
    (htail : ∀ i, s.succ < i → A i 0 = 0) :
    (whitneyEliminateFirst A s).IsTotallyNonnegRect := by
  intro k
  induction k with
  | zero =>
      intro rows cols hrows hcols
      simp
  | succ q ih =>
      intro rows cols hrows hcols
      by_cases hu : ∃ p, rows p = s.succ
      · obtain ⟨p, hp⟩ := hu
        by_cases hs : ∃ r, rows r = s.castSucc
        · obtain ⟨r, hr⟩ := hs
          rw [det_submatrix_whitneyEliminateFirst_eq_of_pivot_mem
            A s rows cols hrows p r hp hr]
          exact hA hrows hcols
        · simp only [not_exists] at hs
          by_cases hp0 : p = 0
          · subst p
            rcases eq_or_lt_of_le (Fin.zero_le (cols 0)) with hcol | hcol
            · have hcol0 : cols 0 = 0 := hcol.symm
              rw [det_submatrix_whitneyEliminateFirst_eq_zero_of_first_col
                A s rows cols hrows hp hcol0 hpivot htail]
            · exact det_submatrix_whitneyEliminateFirst_nonneg_of_first_row
                A s hA hpivot htail rows cols hrows hcols hp hcol
          · let r : Fin q := p.pred hp0
            have hrp : r.succ = p := Fin.succ_pred p hp0
            have hp' : rows r.succ = s.succ := by rw [hrp]; exact hp
            let prior := rows r.castSucc
            let replaced := Function.update rows r.succ s.castSucc
            let qrows := Function.update rows r.castSucc s.castSucc
            let baseRows := r.castSucc.removeNth replaced
            have hreplaced : StrictMono replaced := by
              apply strictMono_update_at rows r.succ s.castSucc hrows
              · intro i hi
                have hiu : rows i < s.succ := by
                  rw [← hp']
                  exact hrows hi
                have hle : rows i ≤ s.castSucc := by
                  apply Fin.le_iff_val_le_val.2
                  change (rows i).val < s.val + 1 at hiu
                  exact Nat.lt_succ_iff.mp hiu
                exact lt_of_le_of_ne hle (hs i)
              · intro i hi
                exact lt_trans s.castSucc_lt_succ (by
                  rw [← hp']
                  exact hrows hi)
            have hqrows : StrictMono qrows := by
              apply strictMono_update_at rows r.castSucc s.castSucc hrows
              · intro i hi
                have hir : rows i < prior := by
                  exact hrows hi
                have hpriorLt : prior < s.castSucc := by
                  have hlt : prior < s.succ := by
                    rw [← hp']
                    exact hrows r.castSucc_lt_succ
                  have hle : prior ≤ s.castSucc := by
                    apply Fin.le_iff_val_le_val.2
                    change prior.val < s.val + 1 at hlt
                    exact Nat.lt_succ_iff.mp hlt
                  exact lt_of_le_of_ne hle (hs r.castSucc)
                exact hir.trans hpriorLt
              · intro i hi
                have hindex : r.succ ≤ i := by
                  apply Fin.le_iff_val_le_val.2
                  change r.val < i.val at hi
                  exact Nat.succ_le_iff.2 hi
                have hmono : rows r.succ ≤ rows i := hrows.monotone hindex
                exact lt_of_lt_of_le (by simpa [hp'] using s.castSucc_lt_succ) hmono
            have hbaseRows : StrictMono baseRows :=
              hreplaced.comp (Fin.strictMono_succAbove r.castSucc)
            have hselectors := whitney_adjacent_selector_identities rows r
              s.castSucc prior s.succ hp' rfl
            have hProws : Function.update baseRows r prior =
                r.succ.removeNth rows := hselectors.1
            have hErows : Function.update baseRows r s.succ =
                r.castSucc.removeNth rows := hselectors.2.1
            have hDArows : r.succ.insertNth s.succ
                (Function.update baseRows r prior) = rows := hselectors.2.2.1
            have hQrows : r.succ.insertNth s.succ baseRows = qrows :=
              hselectors.2.2.2.1
            have hDCrows : r.castSucc.insertNth prior baseRows = replaced :=
              hselectors.2.2.2.2
            have hDCnonneg : 0 ≤ (A.submatrix replaced cols).det :=
              hA hreplaced hcols
            by_cases hDCzero : (A.submatrix replaced cols).det = 0
            · rw [det_submatrix_whitneyEliminateFirst A s rows cols hrows p hp,
                show Function.update rows p s.castSucc = replaced by rw [← hrp],
                hDCzero, mul_zero, sub_zero]
              exact hA hrows hcols
            · have hDCpos : 0 < (A.submatrix replaced cols).det :=
                lt_of_le_of_ne hDCnonneg (Ne.symm hDCzero)
              let MC := A.submatrix replaced cols
              have hdeleted : ∀ j : Fin (q + 1),
                  0 ≤ (MC.submatrix r.castSucc.succAbove j.succAbove).det := by
                intro j
                rw [Matrix.submatrix_submatrix]
                exact hA
                  (hreplaced.comp (Fin.strictMono_succAbove r.castSucc))
                  (hcols.comp (Fin.strictMono_succAbove j))
              obtain ⟨j, hD0pos⟩ :=
                exists_pos_deleted_minor_of_det_pos MC r.castSucc hdeleted hDCpos
              let baseCols := j.removeNth cols
              let M0 := A.submatrix baseRows baseCols
              let b : Fin q → ℝ := fun i ↦ A (baseRows i) (cols j)
              let x : Fin q → ℝ := fun a ↦ A prior (baseCols a)
              let y : Fin q → ℝ := fun a ↦ A s.succ (baseCols a)
              let alpha := A prior (cols j)
              let beta := A s.succ (cols j)
              have hM0det : 0 < M0.det := by
                have hMCminor :
                    MC.submatrix r.castSucc.succAbove j.succAbove = M0 := by
                  rfl
                rw [hMCminor] at hD0pos
                exact hD0pos
              have hsurj : Function.Surjective M0.vecMul := by
                apply Matrix.vecMul_surjective_iff_isUnit.2
                exact (Matrix.isUnit_iff_isUnit_det M0).2
                  (isUnit_iff_ne_zero.2 hM0det.ne')
              obtain ⟨c, hc⟩ := hsurj x
              obtain ⟨d, hd⟩ := hsurj y
              have hPdet : (M0.updateRow r x).det =
                  (A.submatrix (r.succ.removeNth rows) baseCols).det := by
                rw [updateRow_submatrix, hProws]
              have hEdet : (M0.updateRow r y).det =
                  (A.submatrix (r.castSucc.removeNth rows) baseCols).det := by
                rw [updateRow_submatrix, hErows]
              have hDAdet : (borderAt (M0.updateRow r x) r.succ j
                  (Function.update b r alpha) y beta).det =
                    (A.submatrix rows cols).det := by
                rw [updateRow_submatrix]
                have hbupdate : Function.update b r alpha =
                    fun i ↦ A ((Function.update baseRows r prior) i) (cols j) := by
                  ext i
                  by_cases hi : i = r <;>
                    simp [b, alpha, Function.update, hi]
                rw [hbupdate]
                change (borderAt (A.submatrix (Function.update baseRows r prior) baseCols)
                    r.succ j (fun i ↦ A ((Function.update baseRows r prior) i) (cols j))
                    (fun a ↦ A s.succ (baseCols a)) (A s.succ (cols j))).det = _
                rw [borderAt_submatrix, hDArows, j.insertNth_self_removeNth cols]
              have hQdet : (borderAt M0 r.succ j b y beta).det =
                  (A.submatrix qrows cols).det := by
                rw [borderAt_submatrix, hQrows, j.insertNth_self_removeNth cols]
              have hDCdet : (borderAt M0 r.castSucc j b x alpha).det =
                  (A.submatrix replaced cols).det := by
                rw [borderAt_submatrix, hDCrows, j.insertNth_self_removeNth cols]
              have hswap : (borderAt M0 r.succ j b x alpha).det =
                  -(A.submatrix replaced cols).det := by
                rw [det_borderAt_pred_insert M0 r.succ (by simp) j b x alpha,
                  Fin.pred_succ, hDCdet]
              have hplucker0 := det_borderAt_plucker M0 r r.succ j b x y c d
                alpha beta hc hd
              have hplucker : M0.det * (A.submatrix rows cols).det =
                  (A.submatrix (r.succ.removeNth rows) baseCols).det *
                      (A.submatrix qrows cols).det +
                    (A.submatrix (r.castSucc.removeNth rows) baseCols).det *
                      (A.submatrix replaced cols).det := by
                rw [hDAdet, hPdet, hQdet, hEdet, hswap] at hplucker0
                linarith
              have hPnonneg : 0 ≤
                  (A.submatrix (r.succ.removeNth rows) baseCols).det :=
                hA (hrows.comp (Fin.strictMono_succAbove r.succ))
                  (hcols.comp (Fin.strictMono_succAbove j))
              have hQnonneg : 0 ≤ (A.submatrix qrows cols).det :=
                hA hqrows hcols
              have hsmall : 0 ≤
                  ((Matrix.whitneyEliminateFirst A s).submatrix
                    (r.castSucc.removeNth rows) baseCols).det :=
                ih (hrows.comp (Fin.strictMono_succAbove r.castSucc))
                  (hcols.comp (Fin.strictMono_succAbove j))
              have hbaseAt : baseRows r = s.castSucc := by
                simp [baseRows, replaced, Fin.removeNth, Function.update]
              have hbaseRecover :
                  Function.update (r.castSucc.removeNth rows) r s.castSucc =
                    baseRows := by
                rw [← hErows]
                ext i
                by_cases hi : i = r <;>
                  simp [Function.update, hi, hbaseAt]
              have hsmallEq : A s.castSucc 0 *
                    ((Matrix.whitneyEliminateFirst A s).submatrix
                      (r.castSucc.removeNth rows) baseCols).det =
                  A s.castSucc 0 *
                    (A.submatrix (r.castSucc.removeNth rows) baseCols).det -
                  A s.succ 0 * M0.det := by
                rw [det_submatrix_whitneyEliminateFirst A s
                  (r.castSucc.removeNth rows) baseCols
                  (hrows.comp (Fin.strictMono_succAbove r.castSucc)) r,
                  hbaseRecover]
                · field_simp [hpivot.ne']
                  rfl
                · simp [hp', Fin.removeNth]
              rw [det_submatrix_whitneyEliminateFirst A s rows cols hrows p hp,
                show Function.update rows p s.castSucc = replaced by rw [← hrp]]
              exact whitney_hard_minor_nonneg hpivot hM0det hPnonneg hQnonneg
                hDCnonneg hsmall hplucker hsmallEq
      · simp only [not_exists] at hu
        rw [submatrix_whitneyEliminateFirst_eq_of_not_mem A s rows cols hu]
        exact hA hrows hcols

/-- Whitney elimination in a later column preserves total nonnegativity once
all earlier entries in the pivot row and its tail have already been cleared. -/
theorem IsTotallyNonnegRect.whitneyEliminateAt_nonneg {m n : ℕ}
    {A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonnegRect) (s : Fin m) (c : Fin (n + 1))
    (hpivot : 0 < A s.castSucc c)
    (htail : ∀ i, s.succ < i → A i c = 0)
    (hleft : ∀ i, s.castSucc ≤ i → ∀ j, j < c → A i j = 0) :
    (whitneyEliminateAt A s c).IsTotallyNonnegRect := by
  intro k
  induction k with
  | zero =>
      intro rows cols hrows hcols
      simp
  | succ q ih =>
      intro rows cols hrows hcols
      by_cases hu : ∃ p, rows p = s.succ
      · obtain ⟨p, hp⟩ := hu
        by_cases hs : ∃ r, rows r = s.castSucc
        · obtain ⟨r, hr⟩ := hs
          rw [det_submatrix_whitneyEliminateAt_eq_of_pivot_mem
            A s c rows cols hrows p r hp hr]
          exact hA hrows hcols
        · simp only [not_exists] at hs
          by_cases hp0 : p = 0
          · subst p
            rcases le_or_gt (cols 0) c with hcol | hcol
            · rw [det_submatrix_whitneyEliminateAt_eq_zero_of_initial_col
                A s c rows cols hrows hp hcol hpivot htail hleft]
            · exact det_submatrix_whitneyEliminateAt_nonneg_of_first_row
                A s c hA hpivot htail rows cols hrows hcols hp hcol
          · let r : Fin q := p.pred hp0
            have hrp : r.succ = p := Fin.succ_pred p hp0
            have hp' : rows r.succ = s.succ := by rw [hrp]; exact hp
            let prior := rows r.castSucc
            let replaced := Function.update rows r.succ s.castSucc
            let qrows := Function.update rows r.castSucc s.castSucc
            let baseRows := r.castSucc.removeNth replaced
            have hreplaced : StrictMono replaced := by
              apply strictMono_update_at rows r.succ s.castSucc hrows
              · intro i hi
                have hiu : rows i < s.succ := by
                  rw [← hp']
                  exact hrows hi
                have hle : rows i ≤ s.castSucc := by
                  apply Fin.le_iff_val_le_val.2
                  change (rows i).val < s.val + 1 at hiu
                  exact Nat.lt_succ_iff.mp hiu
                exact lt_of_le_of_ne hle (hs i)
              · intro i hi
                exact lt_trans s.castSucc_lt_succ (by
                  rw [← hp']
                  exact hrows hi)
            have hqrows : StrictMono qrows := by
              apply strictMono_update_at rows r.castSucc s.castSucc hrows
              · intro i hi
                have hir : rows i < prior := hrows hi
                have hpriorLt : prior < s.castSucc := by
                  have hlt : prior < s.succ := by
                    rw [← hp']
                    exact hrows r.castSucc_lt_succ
                  have hle : prior ≤ s.castSucc := by
                    apply Fin.le_iff_val_le_val.2
                    change prior.val < s.val + 1 at hlt
                    exact Nat.lt_succ_iff.mp hlt
                  exact lt_of_le_of_ne hle (hs r.castSucc)
                exact hir.trans hpriorLt
              · intro i hi
                have hindex : r.succ ≤ i := by
                  apply Fin.le_iff_val_le_val.2
                  change r.val < i.val at hi
                  exact Nat.succ_le_iff.2 hi
                have hmono : rows r.succ ≤ rows i := hrows.monotone hindex
                exact lt_of_lt_of_le
                  (by simpa [hp'] using s.castSucc_lt_succ) hmono
            have hbaseRows : StrictMono baseRows :=
              hreplaced.comp (Fin.strictMono_succAbove r.castSucc)
            have hselectors := whitney_adjacent_selector_identities rows r
              s.castSucc prior s.succ hp' rfl
            have hProws : Function.update baseRows r prior =
                r.succ.removeNth rows := hselectors.1
            have hErows : Function.update baseRows r s.succ =
                r.castSucc.removeNth rows := hselectors.2.1
            have hDArows : r.succ.insertNth s.succ
                (Function.update baseRows r prior) = rows :=
              hselectors.2.2.1
            have hQrows : r.succ.insertNth s.succ baseRows = qrows :=
              hselectors.2.2.2.1
            have hDCrows : r.castSucc.insertNth prior baseRows = replaced :=
              hselectors.2.2.2.2
            have hDCnonneg : 0 ≤ (A.submatrix replaced cols).det :=
              hA hreplaced hcols
            by_cases hDCzero : (A.submatrix replaced cols).det = 0
            · rw [det_submatrix_whitneyEliminateAt A s c rows cols hrows p hp,
                show Function.update rows p s.castSucc = replaced by rw [← hrp],
                hDCzero, mul_zero, sub_zero]
              exact hA hrows hcols
            · have hDCpos : 0 < (A.submatrix replaced cols).det :=
                lt_of_le_of_ne hDCnonneg (Ne.symm hDCzero)
              let MC := A.submatrix replaced cols
              have hdeleted : ∀ j : Fin (q + 1),
                  0 ≤ (MC.submatrix r.castSucc.succAbove j.succAbove).det := by
                intro j
                rw [Matrix.submatrix_submatrix]
                exact hA
                  (hreplaced.comp (Fin.strictMono_succAbove r.castSucc))
                  (hcols.comp (Fin.strictMono_succAbove j))
              obtain ⟨j, hD0pos⟩ :=
                exists_pos_deleted_minor_of_det_pos MC r.castSucc hdeleted hDCpos
              let baseCols := j.removeNth cols
              let M0 := A.submatrix baseRows baseCols
              let b : Fin q → ℝ := fun i ↦ A (baseRows i) (cols j)
              let x : Fin q → ℝ := fun a ↦ A prior (baseCols a)
              let y : Fin q → ℝ := fun a ↦ A s.succ (baseCols a)
              let alpha := A prior (cols j)
              let beta := A s.succ (cols j)
              have hM0det : 0 < M0.det := by
                have hMCminor :
                    MC.submatrix r.castSucc.succAbove j.succAbove = M0 := by
                  rfl
                rw [hMCminor] at hD0pos
                exact hD0pos
              have hsurj : Function.Surjective M0.vecMul := by
                apply Matrix.vecMul_surjective_iff_isUnit.2
                exact (Matrix.isUnit_iff_isUnit_det M0).2
                  (isUnit_iff_ne_zero.2 hM0det.ne')
              obtain ⟨u, hu⟩ := hsurj x
              obtain ⟨v, hv⟩ := hsurj y
              have hPdet : (M0.updateRow r x).det =
                  (A.submatrix (r.succ.removeNth rows) baseCols).det := by
                rw [updateRow_submatrix, hProws]
              have hEdet : (M0.updateRow r y).det =
                  (A.submatrix (r.castSucc.removeNth rows) baseCols).det := by
                rw [updateRow_submatrix, hErows]
              have hDAdet : (borderAt (M0.updateRow r x) r.succ j
                  (Function.update b r alpha) y beta).det =
                    (A.submatrix rows cols).det := by
                rw [updateRow_submatrix]
                have hbupdate : Function.update b r alpha =
                    fun i ↦ A ((Function.update baseRows r prior) i)
                      (cols j) := by
                  ext i
                  by_cases hi : i = r <;>
                    simp [b, alpha, Function.update, hi]
                rw [hbupdate]
                change (borderAt
                    (A.submatrix (Function.update baseRows r prior) baseCols)
                    r.succ j
                    (fun i ↦ A ((Function.update baseRows r prior) i) (cols j))
                    (fun a ↦ A s.succ (baseCols a))
                    (A s.succ (cols j))).det = _
                rw [borderAt_submatrix, hDArows,
                  j.insertNth_self_removeNth cols]
              have hQdet : (borderAt M0 r.succ j b y beta).det =
                  (A.submatrix qrows cols).det := by
                rw [borderAt_submatrix, hQrows,
                  j.insertNth_self_removeNth cols]
              have hDCdet : (borderAt M0 r.castSucc j b x alpha).det =
                  (A.submatrix replaced cols).det := by
                rw [borderAt_submatrix, hDCrows,
                  j.insertNth_self_removeNth cols]
              have hswap : (borderAt M0 r.succ j b x alpha).det =
                  -(A.submatrix replaced cols).det := by
                rw [det_borderAt_pred_insert M0 r.succ (by simp) j b x alpha,
                  Fin.pred_succ, hDCdet]
              have hplucker0 := det_borderAt_plucker M0 r r.succ j b x y u v
                alpha beta hu hv
              have hplucker : M0.det * (A.submatrix rows cols).det =
                  (A.submatrix (r.succ.removeNth rows) baseCols).det *
                      (A.submatrix qrows cols).det +
                    (A.submatrix (r.castSucc.removeNth rows) baseCols).det *
                      (A.submatrix replaced cols).det := by
                rw [hDAdet, hPdet, hQdet, hEdet, hswap] at hplucker0
                linarith
              have hPnonneg : 0 ≤
                  (A.submatrix (r.succ.removeNth rows) baseCols).det :=
                hA (hrows.comp (Fin.strictMono_succAbove r.succ))
                  (hcols.comp (Fin.strictMono_succAbove j))
              have hQnonneg : 0 ≤ (A.submatrix qrows cols).det :=
                hA hqrows hcols
              have hsmall : 0 ≤
                  ((whitneyEliminateAt A s c).submatrix
                    (r.castSucc.removeNth rows) baseCols).det :=
                ih (hrows.comp (Fin.strictMono_succAbove r.castSucc))
                  (hcols.comp (Fin.strictMono_succAbove j))
              have hbaseAt : baseRows r = s.castSucc := by
                simp [baseRows, replaced, Fin.removeNth, Function.update]
              have hbaseRecover :
                  Function.update (r.castSucc.removeNth rows) r s.castSucc =
                    baseRows := by
                rw [← hErows]
                ext i
                by_cases hi : i = r <;>
                  simp [Function.update, hi, hbaseAt]
              have hsmallEq : A s.castSucc c *
                    ((whitneyEliminateAt A s c).submatrix
                      (r.castSucc.removeNth rows) baseCols).det =
                  A s.castSucc c *
                    (A.submatrix (r.castSucc.removeNth rows) baseCols).det -
                  A s.succ c * M0.det := by
                rw [det_submatrix_whitneyEliminateAt A s c
                  (r.castSucc.removeNth rows) baseCols
                  (hrows.comp (Fin.strictMono_succAbove r.castSucc)) r,
                  hbaseRecover]
                · field_simp [hpivot.ne']
                  rfl
                · simp [hp', Fin.removeNth]
              rw [det_submatrix_whitneyEliminateAt A s c rows cols hrows p hp,
                show Function.update rows p s.castSucc = replaced by rw [← hrp]]
              exact whitney_hard_minor_nonneg hpivot hM0det hPnonneg hQnonneg
                hDCnonneg hsmall hplucker hsmallEq
      · simp only [not_exists] at hu
        rw [submatrix_whitneyEliminateAt_eq_of_not_mem A s c rows cols hu]
        exact hA hrows hcols

/-- Add a nonnegative multiple of a row to its immediate successor. This is
the inverse elementary operation to `whitneyEliminateFirst`. -/
noncomputable def whitneyRestoreFirst {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m)
    (c : ℝ) : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ :=
  A.updateRow s.succ (A s.succ + c • A s.castSucc)

/-- Adding a nonnegative multiple of a row to its immediate successor
preserves rectangular total nonnegativity. -/
theorem IsTotallyNonnegRect.whitneyRestoreFirst_nonneg {m n : ℕ}
    {A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonnegRect) (s : Fin m) (c : ℝ) (hc : 0 ≤ c) :
    (Matrix.whitneyRestoreFirst A s c).IsTotallyNonnegRect := by
  intro q rows cols hrows hcols
  by_cases hu : ∃ p, rows p = s.succ
  · obtain ⟨p, hp⟩ := hu
    let M := A.submatrix rows cols
    let prev : Fin (m + 1) := s.castSucc
    let v : Fin q → ℝ := fun j ↦ A prev (cols j)
    have hsub : (Matrix.whitneyRestoreFirst A s c).submatrix rows cols =
        M.updateRow p (M p + c • v) := by
      ext i j
      by_cases hi : i = p
      · subst i
        simp [Matrix.whitneyRestoreFirst, M, v, prev, hp]
      · have hne : rows i ≠ s.succ := by
          intro h
          exact hi (hrows.injective (h.trans hp.symm))
        simp [Matrix.whitneyRestoreFirst, M, v, prev, hi, hne]
    rw [hsub, Matrix.det_updateRow_add, Matrix.updateRow_eq_self,
      Matrix.det_updateRow_smul]
    have hM : 0 ≤ M.det := hA hrows hcols
    by_cases hprev : ∃ r, rows r = prev
    · obtain ⟨r, hr⟩ := hprev
      have hrp : r ≠ p := by
        intro h
        subst r
        exact (Fin.ne_of_gt s.castSucc_lt_succ) (hp.symm.trans hr)
      have hzero : (M.updateRow p v).det = 0 := by
        apply Matrix.det_zero_of_row_eq hrp
        funext j
        simp [M, v, Matrix.updateRow, hrp, hr]
      rw [hzero, mul_zero, add_zero]
      exact hM
    · simp only [not_exists] at hprev
      let rows' := Function.update rows p prev
      have hrows' : StrictMono rows' := by
        apply strictMono_update_at rows p prev hrows
        · intro i hi
          have hlt := hrows hi
          have hle : rows i ≤ prev := by
            rw [hp] at hlt
            exact Fin.le_iff_val_le_val.2 (by
              change (rows i).val < s.val + 1 at hlt
              exact Nat.lt_succ_iff.mp hlt)
          exact lt_of_le_of_ne hle (hprev i)
        · intro i hi
          exact lt_trans s.castSucc_lt_succ (by rw [← hp]; exact hrows hi)
      have hreplace : M.updateRow p v = A.submatrix rows' cols := by
        rw [updateRow_submatrix]
      rw [hreplace]
      exact add_nonneg hM (mul_nonneg hc (hA hrows' hcols))
  · simp only [not_exists] at hu
    have hsub : (Matrix.whitneyRestoreFirst A s c).submatrix rows cols =
        A.submatrix rows cols := by
      ext i j
      simp [Matrix.whitneyRestoreFirst, Matrix.updateRow, hu i]
    rw [hsub]
    exact hA hrows hcols

/-- Adjacent row restoration is left multiplication by the corresponding
elementary lower transvection. -/
theorem whitneyRestoreFirst_eq_transvection_mul {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m) (c : ℝ) :
    Matrix.whitneyRestoreFirst A s c =
      Matrix.transvection s.succ s.castSucc c * A := by
  ext i j
  by_cases hi : i = s.succ
  · subst i
    rw [Matrix.transvection_mul_apply_same (i := s.succ)
      (j := s.castSucc) j c A]
    simp [Matrix.whitneyRestoreFirst]
  · rw [Matrix.transvection_mul_apply_of_ne (i := s.succ)
      (j := s.castSucc) i j hi c A]
    simp [Matrix.whitneyRestoreFirst, Matrix.updateRow, hi]

/-- A nonnegative adjacent lower transvection is totally nonnegative. -/
theorem isTotallyNonneg_transvection_succ_castSucc {m : ℕ}
    (s : Fin m) (c : ℝ) (hc : 0 ≤ c) :
    (Matrix.transvection s.succ s.castSucc c).IsTotallyNonneg := by
  have hone : (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).IsTotallyNonneg :=
    by
      simpa [Matrix.submatrix_one Fin.val Fin.val_injective] using
        (Matrix.IsTotallyNonneg.one (R := ℝ)).submatrix
          Fin.val_strictMono Fin.val_strictMono
  have hrestore := hone.toRect.whitneyRestoreFirst_nonneg s c hc
  rw [whitneyRestoreFirst_eq_transvection_mul, Matrix.mul_one] at hrestore
  exact hrestore.toSquare

private theorem trailing_submatrix_mul_of_left_firstColumn_zero {m : ℕ}
    (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hzero : ∀ i : Fin m, A i.succ 0 = 0) :
    (A * B).submatrix Fin.succ Fin.succ =
      A.submatrix Fin.succ Fin.succ * B.submatrix Fin.succ Fin.succ := by
  ext i j
  change (A * B) i.succ j.succ =
    (A.submatrix Fin.succ Fin.succ *
      B.submatrix Fin.succ Fin.succ) i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [Fin.sum_univ_succ]
  simp [hzero]

private theorem trailing_submatrix_mul_of_right_firstRow_zero {m : ℕ}
    (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hzero : ∀ j : Fin m, B 0 j.succ = 0) :
    (A * B).submatrix Fin.succ Fin.succ =
      A.submatrix Fin.succ Fin.succ * B.submatrix Fin.succ Fin.succ := by
  ext i j
  change (A * B) i.succ j.succ =
    (A.submatrix Fin.succ Fin.succ *
      B.submatrix Fin.succ Fin.succ) i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [Fin.sum_univ_succ]
  simp [hzero]

private theorem transvection_succ_castSucc_firstColumn_zero {m : ℕ}
    (s : Fin m) (hs : s.castSucc ≠ (0 : Fin (m + 1)))
    (c : ℝ) (i : Fin m) :
    Matrix.transvection s.succ s.castSucc c i.succ 0 = 0 := by
  simp [Matrix.transvection, Matrix.single, hs]

private theorem transvection_succ_castSucc_firstRow_zero {m : ℕ}
    (s : Fin m) (c : ℝ) (j : Fin m) :
    Matrix.transvection s.succ s.castSucc c 0 j.succ = 0 := by
  have hzero : (0 : Fin (m + 1)) ≠ j.succ := ne_of_lt (Fin.succ_pos j)
  simp [Matrix.transvection, Matrix.single, hzero]

/-- Restoring with the pivot ratio exactly reverses one Whitney elimination
step. -/
theorem whitneyRestoreFirst_eliminate {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m) :
    Matrix.whitneyRestoreFirst (whitneyEliminateFirst A s) s
      (A s.succ 0 / A s.castSucc 0) = A := by
  ext i j
  by_cases hi : i = s.succ
  · subst i
    have hne : s.castSucc ≠ s.succ := Fin.ne_of_lt s.castSucc_lt_succ
    simp [Matrix.whitneyRestoreFirst, whitneyEliminateFirst,
      Matrix.updateRow, hne]
  · simp [Matrix.whitneyRestoreFirst, whitneyEliminateFirst,
      Matrix.updateRow, hi]

/-- Restoring with the selected-column pivot ratio reverses the corresponding
Whitney elimination. -/
theorem whitneyRestoreFirst_eliminateAt {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m)
    (c : Fin (n + 1)) :
    Matrix.whitneyRestoreFirst (whitneyEliminateAt A s c) s
      (A s.succ c / A s.castSucc c) = A := by
  ext i j
  by_cases hi : i = s.succ
  · subst i
    have hne : s.castSucc ≠ s.succ := Fin.ne_of_lt s.castSucc_lt_succ
    simp [Matrix.whitneyRestoreFirst, whitneyEliminateAt,
      Matrix.updateRow, hne]
  · simp [Matrix.whitneyRestoreFirst, whitneyEliminateAt,
      Matrix.updateRow, hi]

/-- A Whitney row operation does not change the determinant. -/
theorem det_whitneyEliminateFirst {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (s : Fin m) :
    (whitneyEliminateFirst A s).det = A.det := by
  let c := A s.succ 0 / A s.castSucc 0
  have hmatrix : whitneyEliminateFirst A s =
      A.updateRow s.succ (A s.succ + (-c) • A s.castSucc) := by
    ext i j
    by_cases hi : i = s.succ
    · subst i
      simp [whitneyEliminateFirst, c, Matrix.updateRow]
      ring
    · simp [whitneyEliminateFirst, c, Matrix.updateRow, hi]
  rw [hmatrix, Matrix.det_updateRow_add_smul_self]
  exact Fin.ne_of_gt s.castSucc_lt_succ

/-- A Whitney row operation in any selected column preserves determinant. -/
theorem det_whitneyEliminateAt {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (s : Fin m)
    (c : Fin (m + 1)) :
    (whitneyEliminateAt A s c).det = A.det := by
  let ratio := A s.succ c / A s.castSucc c
  have hmatrix : whitneyEliminateAt A s c =
      A.updateRow s.succ (A s.succ + (-ratio) • A s.castSucc) := by
    ext i j
    by_cases hi : i = s.succ
    · subst i
      simp [whitneyEliminateAt, ratio, Matrix.updateRow]
      ring
    · simp [whitneyEliminateAt, ratio, Matrix.updateRow, hi]
  rw [hmatrix, Matrix.det_updateRow_add_smul_self]
  exact Fin.ne_of_gt s.castSucc_lt_succ

/-- For a nonsingular TN matrix, a first-column zero forces the entire tail
below it to vanish. -/
private theorem IsTotallyNonneg.firstColumn_zero_tail_of_det_ne_zero
    {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0)
    {i : Fin (N + 1)} (hi : A i 0 = 0) :
    ∀ j, i < j → A j 0 = 0 := by
  intro j hij
  by_contra hj
  have hjpos : 0 < A j 0 :=
    lt_of_le_of_ne (hA.nonneg j 0) (Ne.symm hj)
  have hrow : ∀ k, A i k = 0 := by
    intro k
    by_cases hk : k = 0
    · simpa [hk] using hi
    · have hkpos : (0 : Fin (N + 1)) < k := Fin.pos_iff_ne_zero.2 hk
      let rows : Fin 2 → Fin (N + 1) := ![i, j]
      let cols : Fin 2 → Fin (N + 1) := ![0, k]
      have hrows : StrictMono rows := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all [rows]
      have hcols : StrictMono cols := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all [cols]
      have hminor := hA hrows hcols
      simp only [Matrix.det_fin_two, Matrix.submatrix_apply, rows, cols,
        Matrix.cons_val_zero, Matrix.cons_val_one] at hminor
      rw [hi, zero_mul, zero_sub] at hminor
      nlinarith [hA.nonneg i k]
  exact hdet (Matrix.det_eq_zero_of_row_eq_zero i hrow)

/-- Consequently, positive first-column support in a nonsingular TN matrix
has no gaps. -/
private theorem IsTotallyNonneg.firstColumn_pred_pos_of_det_ne_zero
    {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0)
    (i : Fin (N + 1)) (hi0 : i ≠ 0) (hi : 0 < A i 0) :
    0 < A (i.pred hi0).castSucc 0 := by
  have hnonneg := hA.nonneg (i.pred hi0).castSucc 0
  by_cases hzero : A (i.pred hi0).castSucc 0 = 0
  · have htail := hA.firstColumn_zero_tail_of_det_ne_zero hdet hzero i
    exact (hi.ne' (htail (Fin.castSucc_pred_lt hi0))).elim
  · exact lt_of_le_of_ne hnonneg (Ne.symm hzero)

/-- Under an already-cleared Hessenberg prefix, a zero below a selected
column in a nonsingular TN matrix forces the rest of that column to vanish. -/
private theorem IsTotallyNonneg.column_zero_tail_of_det_ne_zero
    {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0)
    {c i : Fin (N + 1)} (hci : c < i)
    (hleft : ∀ k, k < c → A i k = 0) (hi : A i c = 0) :
    ∀ j, i < j → A j c = 0 := by
  intro j hij
  by_contra hj
  have hjpos : 0 < A j c :=
    lt_of_le_of_ne (hA.nonneg j c) (Ne.symm hj)
  have hrow : ∀ k, A i k = 0 := by
    intro k
    rcases lt_trichotomy k c with hkc | rfl | hck
    · exact hleft k hkc
    · exact hi
    · let rows : Fin 2 → Fin (N + 1) := ![i, j]
      let cols : Fin 2 → Fin (N + 1) := ![c, k]
      have hrows : StrictMono rows := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all [rows]
      have hcols : StrictMono cols := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all [cols]
      have hminor := hA hrows hcols
      simp only [Matrix.det_fin_two, Matrix.submatrix_apply, rows, cols,
        Matrix.cons_val_zero, Matrix.cons_val_one] at hminor
      rw [hi, zero_mul, zero_sub] at hminor
      nlinarith [hA.nonneg i k]
  exact hdet (Matrix.det_eq_zero_of_row_eq_zero i hrow)

/-- Positive support below a selected column has no gaps once all columns to
its left have already been cleared. -/
private theorem IsTotallyNonneg.column_pred_pos_of_det_ne_zero
    {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0)
    (c i : Fin (N + 1)) (hgap : c.val + 1 < i.val)
    (hprefix : ∀ r k, k.val < c.val → k.val + 1 < r.val → A r k = 0)
    (hi : 0 < A i c) :
    0 < A (i.pred (by lia)).castSucc c := by
  let p : Fin (N + 1) := (i.pred (by lia)).castSucc
  have hpc : c < p := by
    apply Fin.lt_def.2
    dsimp [p]
    lia
  have hnonneg := hA.nonneg p c
  by_cases hzero : A p c = 0
  · have hleft : ∀ k, k < c → A p k = 0 := by
      intro k hkc
      apply hprefix p k (Fin.lt_def.mp hkc)
      have hpval : p.val + 1 = i.val := by
        dsimp [p]
        lia
      lia
    have htail := hA.column_zero_tail_of_det_ne_zero hdet hpc hleft hzero i
    have hpi : p < i := by
      apply Fin.lt_def.2
      dsimp [p]
      lia
    exact (hi.ne' (htail hpi)).elim
  · exact lt_of_le_of_ne hnonneg (Ne.symm hzero)

/-- Bottom-up Whitney sweep in a selected column.  The number of active
stages is exactly the number of entries below its subdiagonal. -/
noncomputable def whitneyClearColumnAux {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (c : Fin (N + 1)) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  | 0 => A
  | t + 1 =>
      if ht : t < N - (c.val + 1) then
        let s : Fin N := ⟨N - (t + 1), by lia⟩
        let B := whitneyClearColumnAux A c t
        if B s.succ c = 0 then B else whitneyEliminateAt B s c
      else
        whitneyClearColumnAux A c t

/-- Product of the nonnegative lower transvections removed by a selected
column sweep. -/
noncomputable def whitneyClearColumnLowerAux {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (c : Fin (N + 1)) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  | 0 => 1
  | t + 1 =>
      if ht : t < N - (c.val + 1) then
        let s : Fin N := ⟨N - (t + 1), by lia⟩
        let B := whitneyClearColumnAux A c t
        let L := whitneyClearColumnLowerAux A c t
        if B s.succ c = 0 then L
        else L * Matrix.transvection s.succ s.castSucc
          (B s.succ c / B s.castSucc c)
      else
        whitneyClearColumnLowerAux A c t

private theorem whitneyClearColumnAux_spec {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) (c : Fin (N + 1))
    (hprefix : ∀ r k, k.val < c.val → k.val + 1 < r.val → A r k = 0) :
    ∀ t, t ≤ N - (c.val + 1) →
      (whitneyClearColumnAux A c t).IsTotallyNonneg ∧
      (whitneyClearColumnAux A c t).det = A.det ∧
      (∀ r k, k.val < c.val → k.val + 1 < r.val →
        whitneyClearColumnAux A c t r k = 0) ∧
      ∀ i, N - t < i.val → whitneyClearColumnAux A c t i c = 0 := by
  intro t ht
  induction t with
  | zero =>
      refine ⟨hA, rfl, hprefix, ?_⟩
      intro i hi
      exact (Nat.not_lt_of_ge (Nat.le_of_lt_succ i.isLt) hi).elim
  | succ t ih =>
      have htActive : t < N - (c.val + 1) := by lia
      obtain ⟨hB, hBdet, hBprefix, hBtail⟩ := ih htActive.le
      let s : Fin N := ⟨N - (t + 1), by lia⟩
      let B := whitneyClearColumnAux A c t
      have hsval : s.succ.val = N - t := by
        simp [s]
        lia
      have hsc : c.val + 1 < s.succ.val := by
        rw [hsval]
        lia
      have hBdetne : B.det ≠ 0 := by rw [hBdet]; exact hdet
      rw [whitneyClearColumnAux, dif_pos htActive]
      dsimp only
      by_cases hzero : B s.succ c = 0
      · rw [if_pos hzero]
        refine ⟨hB, hBdet, hBprefix, ?_⟩
        intro i hi
        by_cases his : i = s.succ
        · simpa [his] using hzero
        · apply hBtail i
          have hle : s.succ.val ≤ i.val := by
            rw [hsval]
            lia
          rw [← hsval]
          exact lt_of_le_of_ne hle (fun h ↦ his (Fin.ext h.symm))
      · rw [if_neg hzero]
        have htarget : 0 < B s.succ c :=
          lt_of_le_of_ne (hB.nonneg s.succ c) (Ne.symm hzero)
        have hpivot : 0 < B s.castSucc c := by
          have hpred := hB.column_pred_pos_of_det_ne_zero hBdetne c s.succ
            (by simpa using hsc) hBprefix htarget
          simpa using hpred
        have htail : ∀ i, s.succ < i → B i c = 0 := by
          intro i hi
          apply hBtail i
          rw [← hsval]
          exact hi
        have hleft : ∀ i, s.castSucc ≤ i → ∀ j, j < c → B i j = 0 := by
          intro i hsi j hjc
          apply hBprefix i j (Fin.lt_def.mp hjc)
          have hsLower : j.val + 1 < s.castSucc.val := by
            have hjle : j.val + 1 ≤ c.val := by lia
            have hcs : c.val < s.castSucc.val := by
              rw [Fin.val_castSucc]
              dsimp [s]
              lia
            exact lt_of_le_of_lt hjle hcs
          exact lt_of_lt_of_le hsLower (Fin.le_def.mp hsi)
        have hTN := hB.toRect.whitneyEliminateAt_nonneg s c hpivot htail hleft
        have hdetEq : (whitneyEliminateAt B s c).det = A.det := by
          rw [det_whitneyEliminateAt, hBdet]
        refine ⟨hTN.toSquare, hdetEq, ?_, ?_⟩
        · intro r k hkc hkr
          by_cases hrs : r = s.succ
          · subst r
            have htargetZero : B s.succ k = 0 := hBprefix _ _ hkc hkr
            have hpivotZero : B s.castSucc k = 0 := by
              apply hBprefix _ _ hkc
              dsimp [s] at hkr ⊢
              lia
            change whitneyEliminateAt B s c s.succ k = 0
            rw [whitneyEliminateAt_apply_same, htargetZero, hpivotZero]
            ring
          · change whitneyEliminateAt B s c r k = 0
            rw [whitneyEliminateAt_apply_of_ne B s c r k hrs]
            exact hBprefix r k hkc hkr
        · intro i hi
          by_cases his : i = s.succ
          · subst i
            change whitneyEliminateAt B s c s.succ c = 0
            rw [whitneyEliminateAt_apply_same]
            field_simp [hpivot.ne']
            ring
          · have hit : s.succ < i := by
              apply Fin.lt_def.2
              have hle : s.succ.val ≤ i.val := by
                rw [hsval]
                lia
              exact lt_of_le_of_ne hle (fun h ↦ his (Fin.ext h.symm))
            change whitneyEliminateAt B s c i c = 0
            rw [whitneyEliminateAt_apply_of_ne B s c i c his]
            exact htail i hit

private theorem whitneyClearColumnLowerAux_spec {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) (c : Fin (N + 1))
    (hprefix : ∀ r k, k.val < c.val → k.val + 1 < r.val → A r k = 0) :
    ∀ t, t ≤ N - (c.val + 1) →
      (whitneyClearColumnLowerAux A c t).IsTotallyNonneg ∧
      A = whitneyClearColumnLowerAux A c t *
        whitneyClearColumnAux A c t := by
  intro t ht
  induction t with
  | zero =>
      have hone :
          (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ).IsTotallyNonneg := by
        simpa [Matrix.submatrix_one Fin.val Fin.val_injective] using
          (Matrix.IsTotallyNonneg.one (R := ℝ)).submatrix
            Fin.val_strictMono Fin.val_strictMono
      exact ⟨hone, by
        simp [whitneyClearColumnLowerAux, whitneyClearColumnAux]⟩
  | succ t ih =>
      have htActive : t < N - (c.val + 1) := by lia
      obtain ⟨hL, hfactor⟩ := ih htActive.le
      obtain ⟨hB, hBdet, hBprefix, hBtail⟩ :=
        whitneyClearColumnAux_spec A hA hdet c hprefix t htActive.le
      let s : Fin N := ⟨N - (t + 1), by lia⟩
      let B := whitneyClearColumnAux A c t
      let L := whitneyClearColumnLowerAux A c t
      have hsval : s.succ.val = N - t := by
        simp [s]
        lia
      have hsc : c.val + 1 < s.succ.val := by
        rw [hsval]
        lia
      have hBdetne : B.det ≠ 0 := by rw [hBdet]; exact hdet
      have hclear : whitneyClearColumnAux A c (t + 1) =
          if B s.succ c = 0 then B else whitneyEliminateAt B s c := by
        rw [whitneyClearColumnAux, dif_pos htActive]
      have hlower : whitneyClearColumnLowerAux A c (t + 1) =
          if B s.succ c = 0 then L
          else L * Matrix.transvection s.succ s.castSucc
            (B s.succ c / B s.castSucc c) := by
        rw [whitneyClearColumnLowerAux, dif_pos htActive]
      rw [hclear, hlower]
      by_cases hzero : B s.succ c = 0
      · rw [if_pos hzero, if_pos hzero]
        exact ⟨hL, hfactor⟩
      · rw [if_neg hzero, if_neg hzero]
        have htarget : 0 < B s.succ c :=
          lt_of_le_of_ne (hB.nonneg s.succ c) (Ne.symm hzero)
        have hpivot : 0 < B s.castSucc c := by
          have hpred := hB.column_pred_pos_of_det_ne_zero hBdetne c s.succ
            (by simpa using hsc) hBprefix htarget
          simpa using hpred
        have hratio : 0 ≤ B s.succ c / B s.castSucc c :=
          div_nonneg htarget.le hpivot.le
        have hE := isTotallyNonneg_transvection_succ_castSucc s _ hratio
        have hLE : (L * Matrix.transvection s.succ s.castSucc
            (B s.succ c / B s.castSucc c)).IsTotallyNonneg :=
          (hL.toRect.mul hE.toRect).toSquare
        refine ⟨hLE, ?_⟩
        calc
          A = L * B := hfactor
          _ = L * (Matrix.transvection s.succ s.castSucc
              (B s.succ c / B s.castSucc c) *
                whitneyEliminateAt B s c) := by
            rw [← whitneyRestoreFirst_eq_transvection_mul,
              whitneyRestoreFirst_eliminateAt]
          _ = (L * Matrix.transvection s.succ s.castSucc
              (B s.succ c / B s.castSucc c)) *
                whitneyEliminateAt B s c := by rw [Matrix.mul_assoc]

private theorem whitneyClearColumnLowerAux_prefix_block {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (c : Fin (N + 1)) :
    ∀ t,
      (∀ i j, j.val ≤ c.val →
        whitneyClearColumnLowerAux A c t i j =
          (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) i j) ∧
      ∀ j, whitneyClearColumnLowerAux A c t 0 j =
        (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) 0 j := by
  intro t
  induction t with
  | zero =>
      exact ⟨fun _ _ _ ↦ rfl, fun _ ↦ rfl⟩
  | succ t ih =>
      by_cases htActive : t < N - (c.val + 1)
      · let s : Fin N := ⟨N - (t + 1), by lia⟩
        let B := whitneyClearColumnAux A c t
        let L := whitneyClearColumnLowerAux A c t
        rw [whitneyClearColumnLowerAux, dif_pos htActive]
        by_cases hzero : B s.succ c = 0
        · rw [if_pos hzero]
          exact ih
        · rw [if_neg hzero]
          have hcs : c.val < s.castSucc.val := by
            dsimp [s]
            lia
          constructor
          · intro i j hjc
            have hne : j ≠ s.castSucc := by
              intro h
              subst j
              lia
            rw [Matrix.mul_transvection_apply_of_ne
              (i := s.succ) (j := s.castSucc) i j hne]
            exact ih.1 i j hjc
          · intro j
            by_cases hj : j = s.castSucc
            · subst j
              rw [Matrix.mul_transvection_apply_same
                (i := s.succ) (j := s.castSucc)]
              rw [ih.2 s.castSucc, ih.2 s.succ]
              have hzeroCast : (0 : Fin (N + 1)) ≠ s.castSucc :=
                ne_of_lt (lt_of_le_of_lt (Fin.zero_le c) (Fin.lt_def.2 hcs))
              have hzeroSucc : (0 : Fin (N + 1)) ≠ s.succ :=
                ne_of_lt (Fin.succ_pos s)
              simp [hzeroCast, hzeroSucc]
            · rw [Matrix.mul_transvection_apply_of_ne
                (i := s.succ) (j := s.castSucc) 0 j hj]
              exact ih.2 j
      · rw [whitneyClearColumnLowerAux, dif_neg htActive]
        exact ih

private theorem whitneyClearColumnAux_preserves_upperZeros {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (c : Fin (N + 1))
    (hupper : ∀ i j, i.val + 1 < j.val → A i j = 0) :
    ∀ t i j, i.val + 1 < j.val → whitneyClearColumnAux A c t i j = 0 := by
  intro t
  induction t with
  | zero => exact hupper
  | succ t ih =>
      intro i j hij
      by_cases htActive : t < N - (c.val + 1)
      · let s : Fin N := ⟨N - (t + 1), by lia⟩
        let B := whitneyClearColumnAux A c t
        rw [whitneyClearColumnAux, dif_pos htActive]
        by_cases hzero : B s.succ c = 0
        · rw [if_pos hzero]
          exact ih i j hij
        · rw [if_neg hzero]
          by_cases his : i = s.succ
          · rw [his] at hij ⊢
            have htarget : B s.succ j = 0 := ih s.succ j hij
            have hpivot : B s.castSucc j = 0 := by
              apply ih
              dsimp [s] at hij ⊢
              lia
            change whitneyEliminateAt B s c s.succ j = 0
            rw [whitneyEliminateAt_apply_same, htarget, hpivot]
            ring
          · change whitneyEliminateAt B s c i j = 0
            rw [whitneyEliminateAt_apply_of_ne B s c i j his]
            exact ih i j hij
      · rw [whitneyClearColumnAux, dif_neg htActive]
        exact ih i j hij

private theorem whitneyClearColumnLowerAux_lowerTriangular {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (c : Fin (N + 1)) :
    ∀ t i j, i < j → whitneyClearColumnLowerAux A c t i j = 0 := by
  intro t
  induction t with
  | zero =>
      intro i j hij
      exact Matrix.one_apply_ne (ne_of_lt hij)
  | succ t ih =>
      intro i j hij
      by_cases htActive : t < N - (c.val + 1)
      · let s : Fin N := ⟨N - (t + 1), by lia⟩
        let B := whitneyClearColumnAux A c t
        let L := whitneyClearColumnLowerAux A c t
        rw [whitneyClearColumnLowerAux, dif_pos htActive]
        by_cases hzero : B s.succ c = 0
        · rw [if_pos hzero]
          exact ih i j hij
        · rw [if_neg hzero]
          by_cases hj : j = s.castSucc
          · rw [hj] at hij ⊢
            rw [Matrix.mul_transvection_apply_same
              (i := s.succ) (j := s.castSucc)]
            rw [ih i s.castSucc hij]
            have his : i < s.succ := hij.trans s.castSucc_lt_succ
            rw [ih i s.succ his]
            ring
          · rw [Matrix.mul_transvection_apply_of_ne
              (i := s.succ) (j := s.castSucc) i j hj]
            exact ih i j hij
      · rw [whitneyClearColumnLowerAux, dif_neg htActive]
        exact ih i j hij

/-- One recursive Whitney cycle extends an upper-Hessenberg prefix by one
column while preserving TN, nonsingularity, and the full and trailing
principal characteristic polynomials. -/
theorem exists_whitneyClearColumn {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) (c : Fin (N + 1))
    (hprefix : ∀ r k, k.val < c.val → k.val + 1 < r.val → A r k = 0) :
    ∃ C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
      C.IsTotallyNonneg ∧ C.det ≠ 0 ∧ C.charpoly = A.charpoly ∧
        (C.submatrix Fin.succ Fin.succ).charpoly =
          (A.submatrix Fin.succ Fin.succ).charpoly ∧
        ((∀ i j, i.val + 1 < j.val → A i j = 0) →
          ∀ i j, i.val + 1 < j.val → C i j = 0) ∧
        ∀ r k, k.val ≤ c.val → k.val + 1 < r.val → C r k = 0 := by
  let stages := N - (c.val + 1)
  let L := whitneyClearColumnLowerAux A c stages
  let B := whitneyClearColumnAux A c stages
  let C := B * L
  obtain ⟨hB, hBdet, hBprefix, hBtail⟩ :=
    whitneyClearColumnAux_spec A hA hdet c hprefix stages le_rfl
  obtain ⟨hL, hfactor⟩ :=
    whitneyClearColumnLowerAux_spec A hA hdet c hprefix stages le_rfl
  obtain ⟨hLcols, hLrowZero⟩ :=
    whitneyClearColumnLowerAux_prefix_block A c stages
  have hLcols' : ∀ i j, j.val ≤ c.val →
      L i j = (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) i j := hLcols
  have hLrowZero' : ∀ j,
      L (0 : Fin (N + 1)) j =
        (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
          (0 : Fin (N + 1)) j :=
    hLrowZero
  have hLcolZero : ∀ i : Fin N, L i.succ 0 = 0 := by
    intro i
    rw [hLcols' i.succ 0 (Nat.zero_le c.val)]
    simp
  have hLrow : ∀ j : Fin N, L (0 : Fin (N + 1)) j.succ = 0 := by
    intro j
    calc
      L (0 : Fin (N + 1)) j.succ =
          (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
            (0 : Fin (N + 1)) j.succ :=
        hLrowZero' j.succ
      _ = 0 := Matrix.one_apply_ne (ne_of_lt (Fin.succ_pos j))
  have hC : C.IsTotallyNonneg := (hB.toRect.mul hL.toRect).toSquare
  have hCdet : C.det ≠ 0 := by
    intro hzero
    apply hdet
    rw [hfactor, Matrix.det_mul]
    simp only [C, Matrix.det_mul] at hzero
    simpa only [mul_comm] using hzero
  have hCchar : C.charpoly = A.charpoly := by
    calc
      C.charpoly = (B * L).charpoly := rfl
      _ = (L * B).charpoly := Matrix.charpoly_mul_comm B L
      _ = A.charpoly := congrArg Matrix.charpoly hfactor.symm
  have hAtrailing : A.submatrix Fin.succ Fin.succ =
      L.submatrix Fin.succ Fin.succ * B.submatrix Fin.succ Fin.succ := by
    rw [hfactor,
      trailing_submatrix_mul_of_left_firstColumn_zero L B hLcolZero]
  have hCtrailing : C.submatrix Fin.succ Fin.succ =
      B.submatrix Fin.succ Fin.succ * L.submatrix Fin.succ Fin.succ := by
    change (B * L).submatrix Fin.succ Fin.succ = _
    exact trailing_submatrix_mul_of_right_firstRow_zero B L hLrow
  have htrailingChar : (C.submatrix Fin.succ Fin.succ).charpoly =
      (A.submatrix Fin.succ Fin.succ).charpoly := by
    rw [hAtrailing, hCtrailing, Matrix.charpoly_mul_comm]
  have hCcol : ∀ i j, j.val ≤ c.val → C i j = B i j := by
    intro i j hjc
    change (B * L) i j = B i j
    calc
      (B * L) i j =
          (B * (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)) i j := by
        simp only [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro x _
        rw [hLcols' x j hjc]
      _ = B i j := by rw [Matrix.mul_one]
  have hLtri : ∀ i j, i < j → L i j = 0 :=
    whitneyClearColumnLowerAux_lowerTriangular A c stages
  have hCupper : (∀ i j, i.val + 1 < j.val → A i j = 0) →
      ∀ i j, i.val + 1 < j.val → C i j = 0 := by
    intro hupper i j hij
    have hBupper := whitneyClearColumnAux_preserves_upperZeros A c hupper
      stages
    have hBupper' : ∀ i j, i.val + 1 < j.val → B i j = 0 := hBupper
    change (B * L) i j = 0
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hix : i.val + 1 < x.val
    · rw [hBupper' i x hix, zero_mul]
    · have hxj : x < j := Fin.lt_def.2 (by lia)
      rw [hLtri x j hxj, mul_zero]
  refine ⟨C, hC, hCdet, hCchar, htrailingChar, hCupper, ?_⟩
  intro r k hkc hkr
  rw [hCcol r k hkc]
  rcases hkc.eq_or_lt with hkcEq | hkcLt
  · have hk : k = c := Fin.ext hkcEq
    subst k
    apply hBtail r
    dsimp [stages]
    have hrBound := r.isLt
    lia
  · exact hBprefix r k hkcLt hkr

/-- Iterating the recursive Whitney column cycle produces an upper-Hessenberg
matrix while preserving TN, nonsingularity, and the full and trailing
principal characteristic polynomials. A lower-Hessenberg zero pattern on the
other side is preserved as well. -/
theorem exists_whitneyUpperHessenberg {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) :
    ∃ H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
      H.IsTotallyNonneg ∧ H.det ≠ 0 ∧ H.charpoly = A.charpoly ∧
        (H.submatrix Fin.succ Fin.succ).charpoly =
          (A.submatrix Fin.succ Fin.succ).charpoly ∧
        ((∀ i j, i.val + 1 < j.val → A i j = 0) →
          ∀ i j, i.val + 1 < j.val → H i j = 0) ∧
        ∀ r k, k.val + 1 < r.val → H r k = 0 := by
  have hsweep : ∀ t, t ≤ N →
      ∃ H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
        H.IsTotallyNonneg ∧ H.det ≠ 0 ∧ H.charpoly = A.charpoly ∧
          (H.submatrix Fin.succ Fin.succ).charpoly =
            (A.submatrix Fin.succ Fin.succ).charpoly ∧
          ((∀ i j, i.val + 1 < j.val → A i j = 0) →
            ∀ i j, i.val + 1 < j.val → H i j = 0) ∧
          ∀ r k, k.val < t → k.val + 1 < r.val → H r k = 0 := by
    intro t ht
    induction t with
    | zero =>
        refine ⟨A, hA, hdet, rfl, rfl, ?_, ?_⟩
        · exact fun hupper ↦ hupper
        · intro r k hk
          simp at hk
    | succ t ih =>
        have htN : t < N := by lia
        obtain ⟨B, hB, hBdet, hBchar, hBtrailing, hBupper, hBprefix⟩ :=
          ih (Nat.le_of_lt htN)
        let c : Fin (N + 1) := ⟨t, by lia⟩
        obtain ⟨C, hC, hCdet, hCchar, hCtrailing, hCupper, hCprefix⟩ :=
          exists_whitneyClearColumn B hB hBdet c (by
            intro r k hkt hkr
            exact hBprefix r k hkt hkr)
        refine ⟨C, hC, hCdet, hCchar.trans hBchar,
          hCtrailing.trans hBtrailing, ?_, ?_⟩
        · intro hupper
          exact hCupper (hBupper hupper)
        · intro r k hkt hkr
          apply hCprefix r k
          · show k.val ≤ c.val
            dsimp [c]
            lia
          · exact hkr
  obtain ⟨H, hH, hHdet, hHchar, hHtrailing, hHupper, hHprefix⟩ :=
    hsweep N le_rfl
  refine ⟨H, hH, hHdet, hHchar, hHtrailing, hHupper, ?_⟩
  intro r k hkr
  exact hHprefix r k (by have := r.isLt; lia) hkr

/-- Applying the Whitney sweep first to a matrix and then to its transpose
produces a tridiagonal TN matrix with the same full and trailing principal
characteristic polynomials. -/
theorem exists_whitneyTridiagonal {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) :
    ∃ T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
      T.IsTotallyNonneg ∧ T.det ≠ 0 ∧ T.charpoly = A.charpoly ∧
        (T.submatrix Fin.succ Fin.succ).charpoly =
          (A.submatrix Fin.succ Fin.succ).charpoly ∧
        (∀ r k, k.val + 1 < r.val → T r k = 0) ∧
        ∀ i j, i.val + 1 < j.val → T i j = 0 := by
  obtain ⟨H, hH, hHdet, hHchar, hHtrailing, _, hHlower⟩ :=
    exists_whitneyUpperHessenberg A hA hdet
  have hHT : H.transpose.IsTotallyNonneg :=
    hH.toRect.transpose.toSquare
  have hHTdet : H.transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact hHdet
  obtain ⟨T, hT, hTdet, hTchar, hTtrailing, hTupper, hTlower⟩ :=
    exists_whitneyUpperHessenberg H.transpose hHT hHTdet
  have hHTupper : ∀ i j, i.val + 1 < j.val → H.transpose i j = 0 := by
    intro i j hij
    exact hHlower j i hij
  refine ⟨T, hT, hTdet, ?_, ?_, hTlower, hTupper hHTupper⟩
  · calc
      T.charpoly = H.transpose.charpoly := hTchar
      _ = H.charpoly := Matrix.charpoly_transpose H
      _ = A.charpoly := hHchar
  · calc
      (T.submatrix Fin.succ Fin.succ).charpoly =
          (H.transpose.submatrix Fin.succ Fin.succ).charpoly :=
        hTtrailing
      _ = ((H.submatrix Fin.succ Fin.succ).transpose).charpoly := by
        rw [Matrix.transpose_submatrix]
      _ = (H.submatrix Fin.succ Fin.succ).charpoly :=
        Matrix.charpoly_transpose _
      _ = (A.submatrix Fin.succ Fin.succ).charpoly := hHtrailing

/-- Bottom-up Whitney sweep of the first column. After `t` stages the last
`t` entries have been cleared, unless `t` exceeds the matrix dimension. -/
noncomputable def whitneyClearFirstAux {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  | 0 => A
  | t + 1 =>
      if ht : t < N then
        let s : Fin N := ⟨N - (t + 1), by lia⟩
        let B := whitneyClearFirstAux A t
        if B s.succ 0 = 0 then B else whitneyEliminateFirst B s
      else
        whitneyClearFirstAux A t

/-- Product of the nonnegative lower transvections removed by
`whitneyClearFirstAux`. -/
noncomputable def whitneyClearLowerAux {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  | 0 => 1
  | t + 1 =>
      if ht : t < N then
        let s : Fin N := ⟨N - (t + 1), by lia⟩
        let B := whitneyClearFirstAux A t
        let L := whitneyClearLowerAux A t
        if B s.succ 0 = 0 then L
        else L * Matrix.transvection s.succ s.castSucc
          (B s.succ 0 / B s.castSucc 0)
      else
        whitneyClearLowerAux A t

private theorem whitneyClearFirstAux_spec {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) :
    ∀ t, t ≤ N →
      (whitneyClearFirstAux A t).IsTotallyNonneg ∧
      (whitneyClearFirstAux A t).det = A.det ∧
      ∀ i, N - t < i.val → (whitneyClearFirstAux A t) i 0 = 0 := by
  intro t ht
  induction t with
  | zero =>
      exact ⟨hA, rfl, fun i hi ↦
        (Nat.not_lt_of_ge (Nat.le_of_lt_succ i.isLt) hi).elim⟩
  | succ t ih =>
      have htN : t < N := by lia
      have htle : t ≤ N := htN.le
      obtain ⟨hB, hBdet, hBtail⟩ := ih htle
      let s : Fin N := ⟨N - (t + 1), by lia⟩
      let B := whitneyClearFirstAux A t
      have hsval : s.succ.val = N - t := by
        simp [s]
        lia
      have hBdetne : B.det ≠ 0 := by rw [hBdet]; exact hdet
      rw [whitneyClearFirstAux, dif_pos htN]
      dsimp only
      by_cases hzero : B s.succ 0 = 0
      · rw [if_pos hzero]
        refine ⟨hB, hBdet, ?_⟩
        intro i hi
        by_cases his : i = s.succ
        · simpa [his] using hzero
        · apply hBtail i
          have hsbase : s.val = N - (t + 1) := rfl
          have hle : s.succ.val ≤ i.val := by
            rw [Fin.val_succ, hsbase]
            lia
          have hlt : s.succ.val < i.val :=
            lt_of_le_of_ne hle (fun h ↦ his (Fin.ext h.symm))
          rwa [hsval] at hlt
      · rw [if_neg hzero]
        have htarget : 0 < B s.succ 0 :=
          lt_of_le_of_ne (hB.nonneg s.succ 0) (Ne.symm hzero)
        have hpivot : 0 < B s.castSucc 0 := by
          have hpred := hB.firstColumn_pred_pos_of_det_ne_zero
            hBdetne s.succ (by simp) htarget
          simpa using hpred
        have htail : ∀ i, s.succ < i → B i 0 = 0 := by
          intro i hi
          apply hBtail i
          rw [← hsval]
          exact hi
        have hTN := hB.toRect.whitneyEliminateFirst s hpivot htail
        have hdetEq : (whitneyEliminateFirst B s).det = A.det := by
          rw [det_whitneyEliminateFirst, hBdet]
        refine ⟨hTN.toSquare, hdetEq, ?_⟩
        intro i hi
        by_cases his : i = s.succ
        · subst i
          change (whitneyEliminateFirst B s) s.succ 0 = 0
          simp [whitneyEliminateFirst, hpivot.ne']
        · have hit : s.succ < i := by
            apply Fin.lt_def.2
            have hsbase : s.val = N - (t + 1) := rfl
            have hle : s.succ.val ≤ i.val := by
              rw [Fin.val_succ, hsbase]
              lia
            exact lt_of_le_of_ne hle (fun h ↦ his (Fin.ext h.symm))
          change (whitneyEliminateFirst B s) i 0 = 0
          simp [whitneyEliminateFirst, his, htail i hit]

private theorem isTotallyNonneg_one_fin (N : ℕ) :
    (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ).IsTotallyNonneg := by
  simpa [Matrix.submatrix_one Fin.val Fin.val_injective] using
    (Matrix.IsTotallyNonneg.one (R := ℝ)).submatrix
      Fin.val_strictMono Fin.val_strictMono

private theorem whitneyClearLowerAux_spec {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) :
    ∀ t, t ≤ N →
      (whitneyClearLowerAux A t).IsTotallyNonneg ∧
      A = whitneyClearLowerAux A t * whitneyClearFirstAux A t := by
  intro t ht
  induction t with
  | zero =>
      exact ⟨isTotallyNonneg_one_fin N, by simp [whitneyClearLowerAux,
        whitneyClearFirstAux]⟩
  | succ t ih =>
      have htN : t < N := by lia
      obtain ⟨hL, hfactor⟩ := ih htN.le
      obtain ⟨hB, hBdet, hBtail⟩ :=
        whitneyClearFirstAux_spec A hA hdet t htN.le
      let s : Fin N := ⟨N - (t + 1), by lia⟩
      let B := whitneyClearFirstAux A t
      let L := whitneyClearLowerAux A t
      have hsval : s.succ.val = N - t := by
        simp [s]
        lia
      have hBdetne : B.det ≠ 0 := by rw [hBdet]; exact hdet
      have hclear : whitneyClearFirstAux A (t + 1) =
          if B s.succ 0 = 0 then B else whitneyEliminateFirst B s := by
        rw [whitneyClearFirstAux, dif_pos htN]
      have hlower : whitneyClearLowerAux A (t + 1) =
          if B s.succ 0 = 0 then L
          else L * Matrix.transvection s.succ s.castSucc
            (B s.succ 0 / B s.castSucc 0) := by
        rw [whitneyClearLowerAux, dif_pos htN]
      rw [hclear, hlower]
      by_cases hzero : B s.succ 0 = 0
      · rw [if_pos hzero, if_pos hzero]
        exact ⟨hL, hfactor⟩
      · rw [if_neg hzero, if_neg hzero]
        have htarget : 0 < B s.succ 0 :=
          lt_of_le_of_ne (hB.nonneg s.succ 0) (Ne.symm hzero)
        have hpivot : 0 < B s.castSucc 0 := by
          have hpred := hB.firstColumn_pred_pos_of_det_ne_zero
            hBdetne s.succ (by simp) htarget
          simpa using hpred
        have hratio : 0 ≤ B s.succ 0 / B s.castSucc 0 :=
          (div_nonneg htarget.le hpivot.le)
        have hE := isTotallyNonneg_transvection_succ_castSucc s _ hratio
        have hLE : (L * Matrix.transvection s.succ s.castSucc
            (B s.succ 0 / B s.castSucc 0)).IsTotallyNonneg :=
          (hL.toRect.mul hE.toRect).toSquare
        refine ⟨hLE, ?_⟩
        calc
          A = L * B := hfactor
          _ = L * (Matrix.transvection s.succ s.castSucc
              (B s.succ 0 / B s.castSucc 0) *
                whitneyEliminateFirst B s) := by
            rw [← whitneyRestoreFirst_eq_transvection_mul,
              whitneyRestoreFirst_eliminate]
          _ = (L * Matrix.transvection s.succ s.castSucc
              (B s.succ 0 / B s.castSucc 0)) *
                whitneyEliminateFirst B s := by rw [Matrix.mul_assoc]

private theorem whitneyClearLowerAux_first_block {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∀ t, t < N →
      (∀ i : Fin N, whitneyClearLowerAux A t i.succ 0 = 0) ∧
      ∀ j : Fin N, whitneyClearLowerAux A t 0 j.succ = 0 := by
  intro t ht
  induction t with
  | zero =>
      constructor
      · intro i
        simp [whitneyClearLowerAux]
      · intro j
        have hne : (0 : Fin (N + 1)) ≠ j.succ :=
          ne_of_lt (Fin.succ_pos j)
        simp [whitneyClearLowerAux, hne]
  | succ t ih =>
      have htN : t < N := by lia
      obtain ⟨hcol, hrow⟩ := ih htN
      let s : Fin N := ⟨N - (t + 1), by lia⟩
      have hs : s.castSucc ≠ (0 : Fin (N + 1)) := by
        apply Fin.ne_of_gt
        rw [Fin.pos_iff_ne_zero]
        intro hzero
        have : s.val = 0 := congrArg Fin.val hzero
        dsimp [s] at this
        lia
      by_cases hzero : whitneyClearFirstAux A t s.succ 0 = 0
      · rw [whitneyClearLowerAux, dif_pos htN, if_pos hzero]
        exact ⟨hcol, hrow⟩
      · rw [whitneyClearLowerAux, dif_pos htN, if_neg hzero]
        let E := Matrix.transvection s.succ s.castSucc
          (whitneyClearFirstAux A t s.succ 0 /
            whitneyClearFirstAux A t s.castSucc 0)
        have hEcol : ∀ i : Fin N, E i.succ 0 = 0 :=
          transvection_succ_castSucc_firstColumn_zero s hs _
        have hErow : ∀ j : Fin N, E 0 j.succ = 0 :=
          transvection_succ_castSucc_firstRow_zero s _
        constructor
        · intro i
          change (whitneyClearLowerAux A t * E) i.succ 0 = 0
          simp only [Matrix.mul_apply]
          rw [Fin.sum_univ_succ]
          rw [hcol i, zero_mul]
          simp_rw [hEcol]
          simp
        · intro j
          change (whitneyClearLowerAux A t * E) 0 j.succ = 0
          simp only [Matrix.mul_apply]
          rw [Fin.sum_univ_succ]
          rw [hErow j, mul_zero]
          simp_rw [hrow]
          simp

/-- Cycling one bottom-up Whitney sweep produces a TN matrix with the same
ambient and trailing-principal characteristic polynomials, and clears the
first column below the subdiagonal. -/
theorem exists_whitneyClearBelowSubdiagonal {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) :
    ∃ C : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ,
      C.IsTotallyNonneg ∧ C.det ≠ 0 ∧ C.charpoly = A.charpoly ∧
        (C.submatrix Fin.succ Fin.succ).charpoly =
          (A.submatrix Fin.succ Fin.succ).charpoly ∧
        ∀ i, 1 < i → C i 0 = 0 := by
  let L := whitneyClearLowerAux A n
  let B := whitneyClearFirstAux A n
  let C := B * L
  have hnlt : n < n + 1 := Nat.lt_succ_self n
  obtain ⟨hB, hBdet, hBzero⟩ :=
    whitneyClearFirstAux_spec A hA hdet n hnlt.le
  obtain ⟨hL, hfactor⟩ :=
    whitneyClearLowerAux_spec A hA hdet n hnlt.le
  obtain ⟨hLcol, hLrow⟩ := whitneyClearLowerAux_first_block A n hnlt
  have hC : C.IsTotallyNonneg := (hB.toRect.mul hL.toRect).toSquare
  have hCdet : C.det ≠ 0 := by
    intro hzero
    apply hdet
    rw [hfactor, Matrix.det_mul]
    simp only [C, Matrix.det_mul] at hzero
    simpa only [mul_comm] using hzero
  have hCchar : C.charpoly = A.charpoly := by
    calc
      C.charpoly = (B * L).charpoly := rfl
      _ = (L * B).charpoly := Matrix.charpoly_mul_comm B L
      _ = A.charpoly := congrArg Matrix.charpoly hfactor.symm
  have hAtrailing : A.submatrix Fin.succ Fin.succ =
      L.submatrix Fin.succ Fin.succ * B.submatrix Fin.succ Fin.succ := by
    rw [hfactor,
      trailing_submatrix_mul_of_left_firstColumn_zero L B hLcol]
  have hCtrailing : C.submatrix Fin.succ Fin.succ =
      B.submatrix Fin.succ Fin.succ * L.submatrix Fin.succ Fin.succ := by
    change (B * L).submatrix Fin.succ Fin.succ = _
    exact trailing_submatrix_mul_of_right_firstRow_zero B L hLrow
  have htrailingChar : (C.submatrix Fin.succ Fin.succ).charpoly =
      (A.submatrix Fin.succ Fin.succ).charpoly := by
    rw [hAtrailing, hCtrailing, Matrix.charpoly_mul_comm]
  refine ⟨C, hC, hCdet, hCchar, htrailingChar, ?_⟩
  intro i hi
  change (B * L) i 0 = 0
  simp only [Matrix.mul_apply]
  rw [Fin.sum_univ_succ]
  have hi' : 1 < i.val := hi
  have hiB : B i 0 = 0 := hBzero i (by simpa using hi')
  have hLcol' : ∀ j : Fin (n + 1), L j.succ 0 = 0 := hLcol
  rw [hiB, zero_mul, zero_add]
  apply Finset.sum_eq_zero
  intro j _
  rw [hLcol' j, mul_zero]

/-- The completed bottom-up sweep clears every first-column entry below the
top pivot while preserving TN and determinant. -/
theorem exists_whitneyClearFirst {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) :
    ∃ B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
      B.IsTotallyNonneg ∧ B.det = A.det ∧ ∀ i, 0 < i → B i 0 = 0 := by
  refine ⟨whitneyClearFirstAux A N, ?_⟩
  obtain ⟨hTN, hdetEq, htail⟩ := whitneyClearFirstAux_spec A hA hdet N le_rfl
  exact ⟨hTN, hdetEq, fun i hi ↦ htail i (by simpa using hi)⟩

/-- The complete Whitney sweep records the removed nonnegative lower
transvections as an exact factorization. -/
theorem whitneyClearFirst_factorization {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) :
    let L := whitneyClearLowerAux A N
    let B := whitneyClearFirstAux A N
    L.IsTotallyNonneg ∧ B.IsTotallyNonneg ∧ B.det = A.det ∧
      A = L * B ∧ ∀ i, 0 < i → B i 0 = 0 := by
  dsimp only
  obtain ⟨hB, hBdet, hBzero⟩ :=
    whitneyClearFirstAux_spec A hA hdet N le_rfl
  obtain ⟨hL, hfactor⟩ := whitneyClearLowerAux_spec A hA hdet N le_rfl
  exact ⟨hL, hB, hBdet, hfactor,
    fun i hi ↦ hBzero i (by simpa using hi)⟩

private theorem det_eq_entry_zero_zero_mul_trailing_of_firstColumn_zero
    {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hzero : ∀ i : Fin m, A i.succ 0 = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [hzero]

/-- The trailing block after a complete Whitney sweep remains nonsingular and
totally nonnegative. -/
theorem whitneyClearFirst_trailing {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) :
    let B := whitneyClearFirstAux A N
    (B.submatrix Fin.succ Fin.succ).IsTotallyNonneg ∧
      (B.submatrix Fin.succ Fin.succ).det ≠ 0 := by
  dsimp only
  obtain ⟨hB, hBdet, hBzero⟩ :=
    whitneyClearFirstAux_spec A hA hdet N le_rfl
  have hzero : ∀ i : Fin N, whitneyClearFirstAux A N i.succ 0 = 0 :=
    fun i ↦ hBzero i.succ (by
      simpa only [Nat.sub_self, Fin.val_succ] using Nat.zero_lt_succ i.val)
  refine ⟨hB.submatrix Fin.strictMono_succ Fin.strictMono_succ, ?_⟩
  intro htrailing
  have hfactor :=
    det_eq_entry_zero_zero_mul_trailing_of_firstColumn_zero
      (whitneyClearFirstAux A N) hzero
  rw [htrailing, mul_zero] at hfactor
  exact hdet (hBdet.symm.trans hfactor)

/-- In a TN square matrix with positive diagonal, a zero in the first column
forces the entire tail below it to vanish. -/
private theorem IsTotallyNonneg.firstColumn_zero_tail_of_diagonal_pos
    {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdiag : ∀ i, 0 < A i i)
    {i : Fin (N + 1)} (hi : A i 0 = 0) :
    ∀ j, i < j → A j 0 = 0 := by
  intro j hij
  have hi0 : (0 : Fin (N + 1)) < i := by
    apply Fin.pos_iff_ne_zero.2
    intro hieq
    subst i
    exact (hdiag 0).ne' hi
  let rows : Fin 2 → Fin (N + 1) := ![i, j]
  let cols : Fin 2 → Fin (N + 1) := ![0, i]
  have hrows : StrictMono rows := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [rows]
  have hcols : StrictMono cols := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [cols]
  have hminor := hA hrows hcols
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, rows, cols,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hminor
  have hj0 : 0 ≤ A j 0 := hA.nonneg j 0
  rw [hi, zero_mul, zero_sub] at hminor
  nlinarith [hdiag i]

/-- Nonzero first-column support in a TN matrix with positive diagonal has no
gaps: a positive entry has a positive immediate predecessor. -/
private theorem IsTotallyNonneg.firstColumn_pred_pos_of_pos
    {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdiag : ∀ i, 0 < A i i)
    (i : Fin (N + 1)) (hi0 : i ≠ 0) (hi : 0 < A i 0) :
    0 < A (i.pred hi0).castSucc 0 := by
  have hnonneg := hA.nonneg (i.pred hi0).castSucc 0
  by_cases hzero : A (i.pred hi0).castSucc 0 = 0
  · have htail := hA.firstColumn_zero_tail_of_diagonal_pos hdiag hzero i
    have hlt : (i.pred hi0).castSucc < i := by
      exact Fin.castSucc_pred_lt hi0
    exact (hi.ne' (htail hlt)).elim
  · exact lt_of_le_of_ne hnonneg (Ne.symm hzero)

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

private theorem whitneyClearLowerAux_unitLower {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    ∀ t,
      (∀ i j, i < j → whitneyClearLowerAux A t i j = 0) ∧
      ∀ i, whitneyClearLowerAux A t i i = 1 := by
  intro t
  induction t with
  | zero =>
      constructor
      · intro i j hij
        exact Matrix.one_apply_ne (ne_of_lt hij)
      · intro i
        exact Matrix.one_apply_eq i
  | succ t ih =>
      by_cases htActive : t < N
      · let s : Fin N := ⟨N - (t + 1), by lia⟩
        let B := whitneyClearFirstAux A t
        let L := whitneyClearLowerAux A t
        rw [whitneyClearLowerAux, dif_pos htActive]
        by_cases hzero : B s.succ 0 = 0
        · rw [if_pos hzero]
          exact ih
        · rw [if_neg hzero]
          constructor
          · intro i j hij
            by_cases hj : j = s.castSucc
            · rw [hj] at hij ⊢
              rw [Matrix.mul_transvection_apply_same
                (i := s.succ) (j := s.castSucc)]
              rw [ih.1 i s.castSucc hij]
              have his : i < s.succ := hij.trans s.castSucc_lt_succ
              rw [ih.1 i s.succ his]
              ring
            · rw [Matrix.mul_transvection_apply_of_ne
                (i := s.succ) (j := s.castSucc) i j hj]
              exact ih.1 i j hij
          · intro i
            by_cases hi : i = s.castSucc
            · subst i
              rw [Matrix.mul_transvection_apply_same
                (i := s.succ) (j := s.castSucc)]
              rw [ih.2 s.castSucc, ih.1 s.castSucc s.succ
                s.castSucc_lt_succ]
              ring
            · rw [Matrix.mul_transvection_apply_of_ne
                (i := s.succ) (j := s.castSucc) i i hi]
              exact ih.2 i
      · rw [whitneyClearLowerAux, dif_neg htActive]
        exact ih

/-- Every diagonal entry of a nonsingular totally nonnegative real matrix is
positive. -/
theorem IsTotallyNonneg.diagonal_pos_of_det_ne_zero {N : ℕ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) :
    ∀ i, 0 < A i i := by
  induction N with
  | zero =>
      intro i
      rw [Fin.eq_zero i]
      have hne : A 0 0 ≠ 0 := by
        simpa [Matrix.det_fin_one] using hdet
      exact lt_of_le_of_ne (hA.nonneg 0 0) hne.symm
  | succ N ih =>
      let L := whitneyClearLowerAux A (N + 1)
      let B := whitneyClearFirstAux A (N + 1)
      obtain ⟨hL, hB, hBdet, hfactor, hBzero⟩ :=
        whitneyClearFirst_factorization A hA hdet
      obtain ⟨hBtrailing, hBtrailingDet⟩ :=
        whitneyClearFirst_trailing A hA hdet
      have hBdetne : B.det ≠ 0 := by
        rw [hBdet]
        exact hdet
      have hB00ne : B 0 0 ≠ 0 := by
        intro hzero
        apply hBdetne
        rw [det_eq_entry_zero_zero_mul_trailing_of_firstColumn_zero B
          (fun i ↦ hBzero i.succ (Fin.succ_pos i)), hzero, zero_mul]
      have hBdiag : ∀ i, 0 < B i i := by
        intro i
        refine Fin.cases ?_ (fun k ↦ ?_) i
        · exact lt_of_le_of_ne (hB.nonneg 0 0) hB00ne.symm
        · simpa [B] using ih hBtrailing hBtrailingDet k
      have hLdiag : ∀ i, L i i = 1 :=
        (whitneyClearLowerAux_unitLower A (N + 1)).2
      intro i
      rw [hfactor, Matrix.mul_apply]
      have hterm : 0 < L i i * B i i := by
        rw [hLdiag i, one_mul]
        exact hBdiag i
      exact lt_of_lt_of_le hterm (Finset.single_le_sum
        (fun j _ ↦ mul_nonneg (hL.nonneg i j) (hB.nonneg j i))
        (Finset.mem_univ i))

private theorem IsTotallyNonneg.northeast_zero_of_southeast_zero {N : ℕ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) {i j k : Fin (N + 1)}
    (hij : i < j) (hjk : j < k) (hzero : A j k = 0)
    (hdiag : 0 < A j j) :
    A i k = 0 := by
  let rows : Fin 2 → Fin (N + 1) := ![i, j]
  let cols : Fin 2 → Fin (N + 1) := ![j, k]
  have hrows : StrictMono rows := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [rows]
  have hcols : StrictMono cols := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [cols]
  have hminor := hA hrows hcols
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, rows, cols,
    Matrix.cons_val_zero, Matrix.cons_val_one, hzero, mul_zero,
    zero_sub] at hminor
  nlinarith [hA.nonneg i k]

/-- Cyclically moving a nonnegative adjacent lower transvection across a
nonsingular TN factor preserves positivity of both adjacent diagonals. -/
private theorem adjacent_pos_rotate_transvection {N : ℕ}
    (D : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hD : D.IsTotallyNonneg) (hdet : D.det ≠ 0) (s : Fin N)
    (a : ℝ) (ha : 0 ≤ a)
    (hsuper : ∀ i : Fin N,
      0 < (Matrix.transvection s.succ s.castSucc a * D)
        i.castSucc i.succ)
    (hsub : ∀ i : Fin N,
      0 < (Matrix.transvection s.succ s.castSucc a * D)
        i.succ i.castSucc) :
    (∀ i : Fin N,
      0 < (D * Matrix.transvection s.succ s.castSucc a)
        i.castSucc i.succ) ∧
    ∀ i : Fin N,
      0 < (D * Matrix.transvection s.succ s.castSucc a)
        i.succ i.castSucc := by
  have hdiag := hD.diagonal_pos_of_det_ne_zero hdet
  constructor
  · intro i
    by_cases hi : i.castSucc = s.succ
    · have hsi : s.castSucc < i.castSucc := by
        rw [hi]
        exact s.castSucc_lt_succ
      have hik : i.castSucc < i.succ := i.castSucc_lt_succ
      by_cases hzero : D i.castSucc i.succ = 0
      · have hfar : D s.castSucc i.succ = 0 :=
          hD.northeast_zero_of_southeast_zero hsi hik hzero
            (hdiag i.castSucc)
        have hzero' : D s.succ i.succ = 0 := by
          rw [← hi]
          exact hzero
        have hcontra := hsuper i
        rw [hi, Matrix.transvection_mul_apply_same, hzero', hfar,
          mul_zero, add_zero] at hcontra
        exact (lt_irrefl 0 hcontra).elim
      · have hcol : i.succ ≠ s.castSucc :=
          ne_of_gt (hsi.trans hik)
        rw [Matrix.mul_transvection_apply_of_ne
          (i := s.succ) (j := s.castSucc) i.castSucc i.succ hcol]
        exact lt_of_le_of_ne (hD.nonneg i.castSucc i.succ)
          (Ne.symm hzero)
    · have hDsuper : 0 < D i.castSucc i.succ := by
        have h := hsuper i
        rw [Matrix.transvection_mul_apply_of_ne
          (i := s.succ) (j := s.castSucc) i.castSucc i.succ hi] at h
        exact h
      by_cases hcol : i.succ = s.castSucc
      · rw [hcol, Matrix.mul_transvection_apply_same]
        exact add_pos_of_pos_of_nonneg (by simpa only [hcol] using hDsuper)
          (mul_nonneg ha (hD.nonneg i.castSucc s.succ))
      · rw [Matrix.mul_transvection_apply_of_ne
          (i := s.succ) (j := s.castSucc) i.castSucc i.succ hcol]
        exact hDsuper
  · intro i
    by_cases hi : i.castSucc = s.castSucc
    · have hisucc : i.succ = s.succ := by
        apply Fin.ext
        simpa using congrArg Fin.val hi
      by_cases hazero : a = 0
      · have h := hsub i
        rw [hisucc, Matrix.transvection_mul_apply_same, hazero,
          zero_mul, add_zero] at h
        rw [hi, Matrix.mul_transvection_apply_same, hazero,
          zero_mul, add_zero]
        simpa only [hisucc, hi] using h
      · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hazero)
        rw [hi, Matrix.mul_transvection_apply_same, ← hisucc]
        exact add_pos_of_nonneg_of_pos (hD.nonneg i.succ s.castSucc)
          (mul_pos hapos (hdiag i.succ))
    · have hrow : i.succ ≠ s.succ := by
        intro h
        apply hi
        apply Fin.ext
        simpa using congrArg Fin.val h
      have hDsub : 0 < D i.succ i.castSucc := by
        have h := hsub i
        rw [Matrix.transvection_mul_apply_of_ne
          (i := s.succ) (j := s.castSucc) i.succ i.castSucc hrow] at h
        exact h
      rw [Matrix.mul_transvection_apply_of_ne
        (i := s.succ) (j := s.castSucc) i.succ i.castSucc hi]
      exact hDsub

private theorem whitneyClearColumnCycle_adjacent_pos {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) (c : Fin (N + 1))
    (hprefix : ∀ r k, k.val < c.val → k.val + 1 < r.val → A r k = 0)
    (hsuper : ∀ i : Fin N, 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < A i.succ i.castSucc) :
    ∀ t, t ≤ N - (c.val + 1) →
      (∀ i : Fin N,
        0 < (whitneyClearColumnAux A c t *
          whitneyClearColumnLowerAux A c t) i.castSucc i.succ) ∧
      ∀ i : Fin N,
        0 < (whitneyClearColumnAux A c t *
          whitneyClearColumnLowerAux A c t) i.succ i.castSucc := by
  intro t ht
  induction t with
  | zero =>
      simpa [whitneyClearColumnAux, whitneyClearColumnLowerAux] using
        And.intro hsuper hsub
  | succ t ih =>
      have htActive : t < N - (c.val + 1) := by lia
      obtain ⟨hB, hBdet, hBprefix, _⟩ :=
        whitneyClearColumnAux_spec A hA hdet c hprefix t htActive.le
      obtain ⟨hL, hfactor⟩ :=
        whitneyClearColumnLowerAux_spec A hA hdet c hprefix t htActive.le
      let s : Fin N := ⟨N - (t + 1), by lia⟩
      let B := whitneyClearColumnAux A c t
      let L := whitneyClearColumnLowerAux A c t
      rw [whitneyClearColumnAux, whitneyClearColumnLowerAux,
        dif_pos htActive, dif_pos htActive]
      dsimp only
      by_cases hzero : B s.succ c = 0
      · rw [if_pos hzero, if_pos hzero]
        exact ih htActive.le
      · rw [if_neg hzero, if_neg hzero]
        let B' := whitneyEliminateAt B s c
        let ratio := B s.succ c / B s.castSucc c
        let E := Matrix.transvection s.succ s.castSucc ratio
        let D := B' * L
        have hBdetne : B.det ≠ 0 := by
          rw [hBdet]
          exact hdet
        have htarget : 0 < B s.succ c :=
          lt_of_le_of_ne (hB.nonneg s.succ c) (Ne.symm hzero)
        have hsc : c.val + 1 < s.succ.val := by
          dsimp [s]
          lia
        have hpivot : 0 < B s.castSucc c := by
          have hpred := hB.column_pred_pos_of_det_ne_zero hBdetne c s.succ
            hsc hBprefix htarget
          simpa using hpred
        have hratio : 0 ≤ ratio := div_nonneg htarget.le hpivot.le
        obtain ⟨hB', hB'det, _, _⟩ :=
          whitneyClearColumnAux_spec A hA hdet c hprefix (t + 1) ht
        have hclear : whitneyClearColumnAux A c (t + 1) = B' := by
          rw [whitneyClearColumnAux, dif_pos htActive]
          dsimp only
          rw [if_neg hzero]
        have hB'TN : B'.IsTotallyNonneg := by
          rw [← hclear]
          exact hB'
        have hB'detEq : B'.det = A.det := by
          rw [← hclear]
          exact hB'det
        have hB'detne : B'.det ≠ 0 := by
          rw [hB'detEq]
          exact hdet
        have hLdet : L.det ≠ 0 := by
          intro hzeroL
          apply hdet
          rw [hfactor, Matrix.det_mul, hzeroL, zero_mul]
        have hD : D.IsTotallyNonneg :=
          (hB'TN.toRect.mul hL.toRect).toSquare
        have hDdet : D.det ≠ 0 := by
          dsimp only [D]
          rw [Matrix.det_mul]
          exact mul_ne_zero hB'detne hLdet
        have hBfactor : B = E * B' := by
          dsimp [E, B', ratio]
          rw [← whitneyRestoreFirst_eq_transvection_mul,
            whitneyRestoreFirst_eliminateAt]
        have hrotate : E * D = B * L := by
          calc
            E * D = (E * B') * L := by
              dsimp only [D]
              rw [Matrix.mul_assoc]
            _ = B * L := by rw [← hBfactor]
        have hold := ih htActive.le
        have hleftSuper : ∀ i : Fin N, 0 < (E * D) i.castSucc i.succ := by
          rw [hrotate]
          exact hold.1
        have hleftSub : ∀ i : Fin N, 0 < (E * D) i.succ i.castSucc := by
          rw [hrotate]
          exact hold.2
        have hrotated := adjacent_pos_rotate_transvection D hD hDdet s ratio
          hratio hleftSuper hleftSub
        change
          (∀ i : Fin N, 0 < (B' * (L * E)) i.castSucc i.succ) ∧
          ∀ i : Fin N, 0 < (B' * (L * E)) i.succ i.castSucc
        simpa only [D, Matrix.mul_assoc] using hrotated

/-- The Whitney column cycle preserves the oscillatory adjacent-entry
criterion in addition to its spectral and Hessenberg invariants. -/
theorem exists_whitneyClearColumn_adjacent_pos {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) (c : Fin (N + 1))
    (hprefix : ∀ r k, k.val < c.val → k.val + 1 < r.val → A r k = 0)
    (hsuper : ∀ i : Fin N, 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < A i.succ i.castSucc) :
    ∃ C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
      C.IsTotallyNonneg ∧ C.det ≠ 0 ∧ C.charpoly = A.charpoly ∧
        (C.submatrix Fin.succ Fin.succ).charpoly =
          (A.submatrix Fin.succ Fin.succ).charpoly ∧
        ((∀ i j, i.val + 1 < j.val → A i j = 0) →
          ∀ i j, i.val + 1 < j.val → C i j = 0) ∧
        (∀ r k, k.val ≤ c.val → k.val + 1 < r.val → C r k = 0) ∧
        (∀ i : Fin N, 0 < C i.castSucc i.succ) ∧
        ∀ i : Fin N, 0 < C i.succ i.castSucc := by
  let stages := N - (c.val + 1)
  let L := whitneyClearColumnLowerAux A c stages
  let B := whitneyClearColumnAux A c stages
  let C := B * L
  obtain ⟨hB, hBdet, hBprefix, hBtail⟩ :=
    whitneyClearColumnAux_spec A hA hdet c hprefix stages le_rfl
  obtain ⟨hL, hfactor⟩ :=
    whitneyClearColumnLowerAux_spec A hA hdet c hprefix stages le_rfl
  obtain ⟨hLcols, hLrowZero⟩ :=
    whitneyClearColumnLowerAux_prefix_block A c stages
  have hLcols' : ∀ i j, j.val ≤ c.val →
      L i j = (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) i j := hLcols
  have hLrowZero' : ∀ j,
      L (0 : Fin (N + 1)) j =
        (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) 0 j := hLrowZero
  have hLcolZero : ∀ i : Fin N, L i.succ 0 = 0 := by
    intro i
    rw [hLcols' i.succ 0 (Nat.zero_le c.val)]
    simp
  have hLrow : ∀ j : Fin N, L (0 : Fin (N + 1)) j.succ = 0 := by
    intro j
    rw [hLrowZero' j.succ]
    exact Matrix.one_apply_ne (ne_of_lt (Fin.succ_pos j))
  have hC : C.IsTotallyNonneg := (hB.toRect.mul hL.toRect).toSquare
  have hCdet : C.det ≠ 0 := by
    intro hzero
    apply hdet
    rw [hfactor, Matrix.det_mul]
    simp only [C, Matrix.det_mul] at hzero
    simpa only [mul_comm] using hzero
  have hCchar : C.charpoly = A.charpoly := by
    calc
      C.charpoly = (B * L).charpoly := rfl
      _ = (L * B).charpoly := Matrix.charpoly_mul_comm B L
      _ = A.charpoly := congrArg Matrix.charpoly hfactor.symm
  have hAtrailing : A.submatrix Fin.succ Fin.succ =
      L.submatrix Fin.succ Fin.succ * B.submatrix Fin.succ Fin.succ := by
    rw [hfactor,
      trailing_submatrix_mul_of_left_firstColumn_zero L B hLcolZero]
  have hCtrailing : C.submatrix Fin.succ Fin.succ =
      B.submatrix Fin.succ Fin.succ * L.submatrix Fin.succ Fin.succ := by
    change (B * L).submatrix Fin.succ Fin.succ = _
    exact trailing_submatrix_mul_of_right_firstRow_zero B L hLrow
  have htrailingChar : (C.submatrix Fin.succ Fin.succ).charpoly =
      (A.submatrix Fin.succ Fin.succ).charpoly := by
    rw [hAtrailing, hCtrailing, Matrix.charpoly_mul_comm]
  have hCcol : ∀ i j, j.val ≤ c.val → C i j = B i j := by
    intro i j hjc
    change (B * L) i j = B i j
    calc
      (B * L) i j =
          (B * (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)) i j := by
        simp only [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro x _
        rw [hLcols' x j hjc]
      _ = B i j := by rw [Matrix.mul_one]
  have hLtri : ∀ i j, i < j → L i j = 0 :=
    whitneyClearColumnLowerAux_lowerTriangular A c stages
  have hCupper : (∀ i j, i.val + 1 < j.val → A i j = 0) →
      ∀ i j, i.val + 1 < j.val → C i j = 0 := by
    intro hupper i j hij
    have hBupper := whitneyClearColumnAux_preserves_upperZeros A c hupper
      stages
    have hBupper' : ∀ i j, i.val + 1 < j.val → B i j = 0 := hBupper
    change (B * L) i j = 0
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hix : i.val + 1 < x.val
    · rw [hBupper' i x hix, zero_mul]
    · have hxj : x < j := Fin.lt_def.2 (by lia)
      rw [hLtri x j hxj, mul_zero]
  have hCadj := whitneyClearColumnCycle_adjacent_pos A hA hdet c hprefix
    hsuper hsub stages le_rfl
  refine ⟨C, hC, hCdet, hCchar, htrailingChar, hCupper, ?_, hCadj⟩
  intro r k hkc hkr
  rw [hCcol r k hkc]
  rcases hkc.eq_or_lt with hkcEq | hkcLt
  · have hk : k = c := Fin.ext hkcEq
    subst k
    apply hBtail r
    dsimp [stages]
    have hrBound := r.isLt
    lia
  · exact hBprefix r k hkcLt hkr

/-- Iterated Whitney cycling preserves the oscillatory adjacent-entry
criterion while producing an upper-Hessenberg matrix. -/
theorem exists_whitneyUpperHessenberg_adjacent_pos {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0)
    (hsuper : ∀ i : Fin N, 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < A i.succ i.castSucc) :
    ∃ H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
      H.IsTotallyNonneg ∧ H.det ≠ 0 ∧ H.charpoly = A.charpoly ∧
        (H.submatrix Fin.succ Fin.succ).charpoly =
          (A.submatrix Fin.succ Fin.succ).charpoly ∧
        ((∀ i j, i.val + 1 < j.val → A i j = 0) →
          ∀ i j, i.val + 1 < j.val → H i j = 0) ∧
        (∀ r k, k.val + 1 < r.val → H r k = 0) ∧
        (∀ i : Fin N, 0 < H i.castSucc i.succ) ∧
        ∀ i : Fin N, 0 < H i.succ i.castSucc := by
  have hsweep : ∀ t, t ≤ N →
      ∃ H : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
        H.IsTotallyNonneg ∧ H.det ≠ 0 ∧ H.charpoly = A.charpoly ∧
          (H.submatrix Fin.succ Fin.succ).charpoly =
            (A.submatrix Fin.succ Fin.succ).charpoly ∧
          ((∀ i j, i.val + 1 < j.val → A i j = 0) →
            ∀ i j, i.val + 1 < j.val → H i j = 0) ∧
          (∀ r k, k.val < t → k.val + 1 < r.val → H r k = 0) ∧
          (∀ i : Fin N, 0 < H i.castSucc i.succ) ∧
          ∀ i : Fin N, 0 < H i.succ i.castSucc := by
    intro t ht
    induction t with
    | zero =>
        refine ⟨A, hA, hdet, rfl, rfl, fun hupper ↦ hupper, ?_,
          hsuper, hsub⟩
        intro r k hk
        simp at hk
    | succ t ih =>
        have htN : t < N := by lia
        obtain ⟨B, hB, hBdet, hBchar, hBtrailing, hBupper,
            hBprefix, hBsuper, hBsub⟩ := ih htN.le
        let c : Fin (N + 1) := ⟨t, by lia⟩
        obtain ⟨C, hC, hCdet, hCchar, hCtrailing, hCupper,
            hCprefix, hCsuper, hCsub⟩ :=
          exists_whitneyClearColumn_adjacent_pos B hB hBdet c (by
            intro r k hkt hkr
            exact hBprefix r k hkt hkr) hBsuper hBsub
        refine ⟨C, hC, hCdet, hCchar.trans hBchar,
          hCtrailing.trans hBtrailing, ?_, ?_, hCsuper, hCsub⟩
        · intro hupper
          exact hCupper (hBupper hupper)
        · intro r k hkt hkr
          apply hCprefix r k
          · show k.val ≤ c.val
            dsimp [c]
            lia
          · exact hkr
  obtain ⟨H, hH, hHdet, hHchar, hHtrailing, hHupper,
      hHprefix, hHsuper, hHsub⟩ := hsweep N le_rfl
  refine ⟨H, hH, hHdet, hHchar, hHtrailing, hHupper, ?_,
    hHsuper, hHsub⟩
  intro r k hkr
  exact hHprefix r k (by have := r.isLt; lia) hkr

/-- A nonsingular TN matrix satisfying the oscillatory adjacent-entry
criterion is isospectral, together with its trailing principal section, to a
tridiagonal TN matrix satisfying the same criterion. -/
theorem exists_whitneyTridiagonal_adjacent_pos {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0)
    (hsuper : ∀ i : Fin N, 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < A i.succ i.castSucc) :
    ∃ T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ,
      T.IsTotallyNonneg ∧ T.det ≠ 0 ∧ T.charpoly = A.charpoly ∧
        (T.submatrix Fin.succ Fin.succ).charpoly =
          (A.submatrix Fin.succ Fin.succ).charpoly ∧
        (∀ r k, k.val + 1 < r.val → T r k = 0) ∧
        (∀ i j, i.val + 1 < j.val → T i j = 0) ∧
        (∀ i : Fin N, 0 < T i.castSucc i.succ) ∧
        ∀ i : Fin N, 0 < T i.succ i.castSucc := by
  obtain ⟨H, hH, hHdet, hHchar, hHtrailing, _, hHlower,
      hHsuper, hHsub⟩ :=
    exists_whitneyUpperHessenberg_adjacent_pos A hA hdet hsuper hsub
  have hHT : H.transpose.IsTotallyNonneg := hH.toRect.transpose.toSquare
  have hHTdet : H.transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact hHdet
  have hHTsuper : ∀ i : Fin N, 0 < H.transpose i.castSucc i.succ :=
    hHsub
  have hHTsub : ∀ i : Fin N, 0 < H.transpose i.succ i.castSucc :=
    hHsuper
  obtain ⟨T, hT, hTdet, hTchar, hTtrailing, hTupper, hTlower,
      hTsuper, hTsub⟩ :=
    exists_whitneyUpperHessenberg_adjacent_pos H.transpose hHT hHTdet
      hHTsuper hHTsub
  have hHTupper : ∀ i j, i.val + 1 < j.val → H.transpose i j = 0 := by
    intro i j hij
    exact hHlower j i hij
  refine ⟨T, hT, hTdet, ?_, ?_, hTlower, hTupper hHTupper,
    hTsuper, hTsub⟩
  · calc
      T.charpoly = H.transpose.charpoly := hTchar
      _ = H.charpoly := Matrix.charpoly_transpose H
      _ = A.charpoly := hHchar
  · calc
      (T.submatrix Fin.succ Fin.succ).charpoly =
          (H.transpose.submatrix Fin.succ Fin.succ).charpoly := hTtrailing
      _ = ((H.submatrix Fin.succ Fin.succ).transpose).charpoly := by
        rw [Matrix.transpose_submatrix]
      _ = (H.submatrix Fin.succ Fin.succ).charpoly :=
        Matrix.charpoly_transpose _
      _ = (A.submatrix Fin.succ Fin.succ).charpoly := hHtrailing

private noncomputable def tridiagonalScale {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : Fin (N + 1) → ℝ :=
  fun i ↦ Nat.rec (motive := fun k ↦ k < N + 1 → ℝ)
    (fun _ ↦ 1)
    (fun k previous hk ↦
      let j : Fin N := ⟨k, by lia⟩
      previous (by lia) *
        Real.sqrt (T j.succ j.castSucc / T j.castSucc j.succ))
    i.val i.isLt

@[simp] private theorem tridiagonalScale_zero {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    tridiagonalScale T 0 = 1 := rfl

private theorem tridiagonalScale_succ {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (i : Fin N) :
    tridiagonalScale T i.succ = tridiagonalScale T i.castSucc *
      Real.sqrt (T i.succ i.castSucc / T i.castSucc i.succ) := by
  rfl

private theorem tridiagonalScale_pos {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hsuper : ∀ i : Fin N, 0 < T i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < T i.succ i.castSucc) :
    ∀ i, 0 < tridiagonalScale T i := by
  intro i
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
      rw [tridiagonalScale_succ]
      exact mul_pos ih (Real.sqrt_pos.2 (div_pos (hsub i) (hsuper i)))

private noncomputable def symmetrizeTridiagonal {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  let d := tridiagonalScale T
  Matrix.diagonal (fun i ↦ (d i)⁻¹) * T * Matrix.diagonal d

private theorem symmetrizeTridiagonal_apply {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (i j : Fin (N + 1)) :
    symmetrizeTridiagonal T i j =
      (tridiagonalScale T i)⁻¹ * T i j * tridiagonalScale T j := by
  simp [symmetrizeTridiagonal]

private theorem symmetrizeTridiagonal_charpoly {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hd : ∀ i, tridiagonalScale T i ≠ 0) :
    (symmetrizeTridiagonal T).charpoly = T.charpoly := by
  let d := tridiagonalScale T
  let D := Matrix.diagonal d
  let Dinv := Matrix.diagonal (fun i ↦ (d i)⁻¹)
  have hcancel : D * Dinv = 1 := by
    dsimp only [D, Dinv]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d, hd i]
    · simp [hij]
  calc
    (symmetrizeTridiagonal T).charpoly = (Dinv * T * D).charpoly := rfl
    _ = (D * (Dinv * T)).charpoly := Matrix.charpoly_mul_comm (Dinv * T) D
    _ = ((D * Dinv) * T).charpoly := by rw [Matrix.mul_assoc]
    _ = T.charpoly := by rw [hcancel, Matrix.one_mul]

private theorem symmetrizeTridiagonal_trailing_charpoly {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hd : ∀ i, tridiagonalScale T i ≠ 0) :
    ((symmetrizeTridiagonal T).submatrix Fin.succ Fin.succ).charpoly =
      (T.submatrix Fin.succ Fin.succ).charpoly := by
  let d : Fin N → ℝ := fun i ↦ tridiagonalScale T i.succ
  let D := Matrix.diagonal d
  let Dinv := Matrix.diagonal (fun i ↦ (d i)⁻¹)
  have hmatrix : (symmetrizeTridiagonal T).submatrix Fin.succ Fin.succ =
      Dinv * T.submatrix Fin.succ Fin.succ * D := by
    ext i j
    simp [D, Dinv, d, symmetrizeTridiagonal_apply]
  have hcancel : D * Dinv = 1 := by
    dsimp only [D, Dinv]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d, hd i.succ]
    · simp [hij]
  rw [hmatrix]
  calc
    (Dinv * T.submatrix Fin.succ Fin.succ * D).charpoly =
        (D * (Dinv * T.submatrix Fin.succ Fin.succ)).charpoly :=
      Matrix.charpoly_mul_comm _ _
    _ = ((D * Dinv) * T.submatrix Fin.succ Fin.succ).charpoly := by
      rw [Matrix.mul_assoc]
    _ = (T.submatrix Fin.succ Fin.succ).charpoly := by
      rw [hcancel, Matrix.one_mul]

private theorem symmetrizeTridiagonal_adjacent {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hsuper : ∀ i : Fin N, 0 < T i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < T i.succ i.castSucc) (i : Fin N) :
    symmetrizeTridiagonal T i.castSucc i.succ =
      symmetrizeTridiagonal T i.succ i.castSucc := by
  have hdpos := tridiagonalScale_pos T hsuper hsub i.castSucc
  have hratio : 0 < T i.succ i.castSucc / T i.castSucc i.succ :=
    div_pos (hsub i) (hsuper i)
  have hsqrt : 0 < Real.sqrt
      (T i.succ i.castSucc / T i.castSucc i.succ) :=
    Real.sqrt_pos.2 hratio
  have hsquare : Real.sqrt
      (T i.succ i.castSucc / T i.castSucc i.succ) ^ 2 =
        T i.succ i.castSucc / T i.castSucc i.succ :=
    Real.sq_sqrt hratio.le
  rw [symmetrizeTridiagonal_apply, symmetrizeTridiagonal_apply,
    tridiagonalScale_succ]
  field_simp [hdpos.ne', hsqrt.ne', (hsuper i).ne']
  rw [hsquare]
  field_simp [(hsuper i).ne']

private theorem symmetrizeTridiagonal_isHermitian {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hlower : ∀ r k, k.val + 1 < r.val → T r k = 0)
    (hupper : ∀ i j, i.val + 1 < j.val → T i j = 0)
    (hsuper : ∀ i : Fin N, 0 < T i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < T i.succ i.castSucc) :
    (symmetrizeTridiagonal T).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial]
  rcases lt_trichotomy i j with hij | rfl | hji
  · by_cases hadj : i.val + 1 = j.val
    · let k : Fin N := ⟨i.val, by have := j.isLt; lia⟩
      have hi : k.castSucc = i := Fin.ext rfl
      have hj : k.succ = j := Fin.ext hadj
      rw [← hi, ← hj]
      exact (symmetrizeTridiagonal_adjacent T hsuper hsub k).symm
    · have hgap : i.val + 1 < j.val := by lia
      rw [symmetrizeTridiagonal_apply, symmetrizeTridiagonal_apply,
        hupper i j hgap, hlower j i hgap]
      ring
  · rfl
  · by_cases hadj : j.val + 1 = i.val
    · let k : Fin N := ⟨j.val, by have := i.isLt; lia⟩
      have hj : k.castSucc = j := Fin.ext rfl
      have hi : k.succ = i := Fin.ext hadj
      rw [← hi, ← hj]
      exact symmetrizeTridiagonal_adjacent T hsuper hsub k
    · have hgap : j.val + 1 < i.val := by lia
      rw [symmetrizeTridiagonal_apply, symmetrizeTridiagonal_apply,
        hupper j i hgap, hlower i j hgap]
      ring

private theorem det_tridiagonal_first_rec {R : Type*} [CommRing R] {N : ℕ}
    (A : Matrix (Fin (N + 2)) (Fin (N + 2)) R)
    (hcol : ∀ i : Fin N, A i.succ.succ 0 = 0)
    (hrow : ∀ j : Fin N, A 0 j.succ.succ = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det -
      A 1 0 * A 0 1 *
        ((A.submatrix Fin.succ Fin.succ).submatrix
          Fin.succ Fin.succ).det := by
  have hoff : (A.submatrix (1 : Fin (N + 2)).succAbove Fin.succ).det =
      A 0 1 * ((A.submatrix Fin.succ Fin.succ).submatrix
        Fin.succ Fin.succ).det := by
    let B := A.submatrix (1 : Fin (N + 2)).succAbove Fin.succ
    have hBrow : ∀ j : Fin N, B 0 j.succ = 0 := by
      intro j
      simpa [B, Matrix.submatrix] using hrow j
    have hB00 : B 0 0 = A 0 1 := by
      simp [B, Matrix.submatrix]
    have hBtail : B.submatrix Fin.succ Fin.succ =
        (A.submatrix Fin.succ Fin.succ).submatrix
          Fin.succ Fin.succ := by
      ext i j
      simp [B, Matrix.submatrix]
    change B.det = _
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp_rw [hBrow]
    rw [hB00]
    simp only [Fin.val_zero, pow_zero, one_mul]
    rw [Fin.succAbove_zero, hBtail]
    simp
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  simp_rw [hcol]
  simp only [Nat.succ_eq_add_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    Std.le_refl, List.Nat.eq_of_le_zero, pow_zero, one_mul,
    Fin.succAbove_zero, Fin.succ_zero_eq_one, Nat.one_mod, pow_one,
    neg_mul, Fin.val_succ, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, Matrix.submatrix_submatrix]
  rw [hoff]
  rw [Matrix.submatrix_submatrix]
  ring

private theorem charmatrix_trailing {R : Type*} [CommRing R] {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    A.charmatrix.submatrix Fin.succ Fin.succ =
      (A.submatrix Fin.succ Fin.succ).charmatrix := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.submatrix_apply, Matrix.charmatrix_apply_eq]
  · rw [Matrix.submatrix_apply,
      Matrix.charmatrix_apply_ne _ _ _
        (fun h ↦ hij (Fin.ext (by simpa using congrArg Fin.val h))),
      Matrix.charmatrix_apply_ne _ _ _ hij, Matrix.submatrix_apply]

private theorem charpoly_tridiagonal_rec {N : ℕ}
    (T : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ)
    (hlower : ∀ r k, k.val + 1 < r.val → T r k = 0)
    (hupper : ∀ i j, i.val + 1 < j.val → T i j = 0) :
    T.charpoly =
      (Polynomial.X - Polynomial.C (T 0 0)) *
          (T.submatrix Fin.succ Fin.succ).charpoly -
        Polynomial.C (T 0 1 * T 1 0) *
          ((T.submatrix Fin.succ Fin.succ).submatrix
            Fin.succ Fin.succ).charpoly := by
  let M := T.charmatrix
  have hcol : ∀ i : Fin N, M i.succ.succ 0 = 0 := by
    intro i
    have hgap : (0 : Fin (N + 2)).val + 1 < i.succ.succ.val := by
      simp only [Fin.val_zero, Fin.val_succ]
      lia
    have hzero := hlower i.succ.succ 0 hgap
    change T.charmatrix i.succ.succ 0 = 0
    rw [Matrix.charmatrix_apply_ne _ _ _
      (ne_of_gt (Fin.succ_pos i.succ)), hzero, map_zero,
      neg_zero]
  have hrow : ∀ j : Fin N, M 0 j.succ.succ = 0 := by
    intro j
    have hgap : (0 : Fin (N + 2)).val + 1 < j.succ.succ.val := by
      simp only [Fin.val_zero, Fin.val_succ]
      lia
    have hzero := hupper 0 j.succ.succ hgap
    change T.charmatrix 0 j.succ.succ = 0
    rw [Matrix.charmatrix_apply_ne _ _ _
      (ne_of_lt (Fin.succ_pos j.succ)), hzero, map_zero,
      neg_zero]
  rw [Matrix.charpoly, det_tridiagonal_first_rec M hcol hrow]
  dsimp only [M]
  rw [charmatrix_trailing T,
    charmatrix_trailing (T.submatrix Fin.succ Fin.succ)]
  rw [Matrix.charmatrix_apply_eq,
    Matrix.charmatrix_apply_ne T 1 0 one_ne_zero,
    Matrix.charmatrix_apply_ne T 0 1 zero_ne_one]
  simp only [Matrix.charpoly, map_mul]
  ring

private theorem charpoly_tridiagonal_no_common_root {N : ℕ}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hlower : ∀ r k, k.val + 1 < r.val → T r k = 0)
    (hupper : ∀ i j, i.val + 1 < j.val → T i j = 0)
    (hsuper : ∀ i : Fin N, 0 < T i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < T i.succ i.castSucc) :
    ∀ x : ℝ, ¬(T.charpoly.IsRoot x ∧
      (T.submatrix Fin.succ Fin.succ).charpoly.IsRoot x) := by
  induction N with
  | zero =>
      intro x hroots
      have hzero := hroots.2.eq_zero
      simp [Matrix.charpoly, Matrix.charmatrix] at hzero
  | succ N ih =>
      intro x hroots
      let B := T.submatrix Fin.succ Fin.succ
      have hBlower : ∀ r k, k.val + 1 < r.val → B r k = 0 := by
        intro r k hrk
        exact hlower r.succ k.succ (by simpa [B] using hrk)
      have hBupper : ∀ i j, i.val + 1 < j.val → B i j = 0 := by
        intro i j hij
        exact hupper i.succ j.succ (by simpa [B] using hij)
      have hBsuper : ∀ i : Fin N, 0 < B i.castSucc i.succ := by
        intro i
        simpa [B, Matrix.submatrix] using hsuper i.succ
      have hBsub : ∀ i : Fin N, 0 < B i.succ i.castSucc := by
        intro i
        simpa [B, Matrix.submatrix] using hsub i.succ
      have hrec := congrArg (Polynomial.eval x)
        (charpoly_tridiagonal_rec T hlower hupper)
      have hprod : (T 0 1 * T 1 0) *
          Polynomial.eval x
            ((T.submatrix Fin.succ Fin.succ).submatrix
              Fin.succ Fin.succ).charpoly = 0 := by
        simp only [Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_X, Polynomial.eval_C, hroots.1.eq_zero,
          hroots.2.eq_zero] at hrec
        linarith
      have hcoeff : T 0 1 * T 1 0 ≠ 0 :=
        mul_ne_zero (hsuper 0).ne' (hsub 0).ne'
      have htailRoot :
          ((T.submatrix Fin.succ Fin.succ).submatrix
            Fin.succ Fin.succ).charpoly.IsRoot x :=
        Polynomial.IsRoot.def.2 ((mul_eq_zero.mp hprod).resolve_left hcoeff)
      exact ih B hBlower hBupper hBsuper hBsub x ⟨hroots.2, htailRoot⟩

/-- Strict trailing-principal interlacing for the classical oscillatory
criterion. The `Interlaces` component supplies weak interlacing and splitness;
the two root-multiplicity conclusions together with root-disjointness make
every interlacing inequality strict. All roots of the ambient characteristic
polynomial are positive. -/
theorem IsTotallyNonneg.trailing_charpoly_strictInterlaces {N : ℕ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0)
    (hsuper : ∀ i : Fin N, 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < A i.succ i.castSucc) :
    RealRooted.Interlaces
        (A.submatrix Fin.succ Fin.succ).charpoly A.charpoly ∧
      (∀ x : ℝ, A.charpoly.IsRoot x →
        A.charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, (A.submatrix Fin.succ Fin.succ).charpoly.IsRoot x →
        (A.submatrix Fin.succ Fin.succ).charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, ¬(A.charpoly.IsRoot x ∧
        (A.submatrix Fin.succ Fin.succ).charpoly.IsRoot x)) ∧
      ∀ x ∈ A.charpoly.roots, 0 < x := by
  obtain ⟨T, hT, hTdet, hTchar, hTtrailing, hTlower, hTupper,
      hTsuper, hTsub⟩ :=
    exists_whitneyTridiagonal_adjacent_pos A hA hdet hsuper hsub
  let S := symmetrizeTridiagonal T
  have hdpos := tridiagonalScale_pos T hTsuper hTsub
  have hdne : ∀ i, tridiagonalScale T i ≠ 0 := fun i ↦ (hdpos i).ne'
  have hS : S.IsHermitian :=
    symmetrizeTridiagonal_isHermitian T hTlower hTupper hTsuper hTsub
  have hSchar : S.charpoly = T.charpoly :=
    symmetrizeTridiagonal_charpoly T hdne
  have hStrailing : (S.submatrix Fin.succ Fin.succ).charpoly =
      (T.submatrix Fin.succ Fin.succ).charpoly :=
    symmetrizeTridiagonal_trailing_charpoly T hdne
  have hInterS : RealRooted.Interlaces
      (S.submatrix Fin.succ Fin.succ).charpoly S.charpoly := by
    simpa only [RealRooted.Challenges.CauchyInterlacing.PrincipalSubmatrix,
      Fin.succAbove_zero] using
      RealRooted.Challenges.CauchyInterlacing.principalSubmatrix_charpoly_interlaces
        S hS 0
  have hInter : RealRooted.Interlaces
      (A.submatrix Fin.succ Fin.succ).charpoly A.charpoly := by
    rw [← hTchar, ← hTtrailing, ← hSchar, ← hStrailing]
    exact hInterS
  have hNoCommonT := charpoly_tridiagonal_no_common_root T hTlower hTupper
    hTsuper hTsub
  have hNoCommon : ∀ x : ℝ, ¬(A.charpoly.IsRoot x ∧
      (A.submatrix Fin.succ Fin.succ).charpoly.IsRoot x) := by
    intro x hroots
    apply hNoCommonT x
    constructor
    · rw [hTchar]
      exact hroots.1
    · rw [hTtrailing]
      exact hroots.2
  have hPrec : RealRooted.Prec
      (A.submatrix Fin.succ Fin.succ).charpoly A.charpoly :=
    hInter.toPrec
  have hFullSimple : ∀ x : ℝ, A.charpoly.IsRoot x →
      A.charpoly.rootMultiplicity x = 1 := by
    intro x hx
    have hTrailingNotRoot :
        ¬(A.submatrix Fin.succ Fin.succ).charpoly.IsRoot x := by
      intro hxTrailing
      exact hNoCommon x ⟨hx, hxTrailing⟩
    have hTrailingMult :
        (A.submatrix Fin.succ Fin.succ).charpoly.rootMultiplicity x = 0 :=
      Polynomial.rootMultiplicity_eq_zero hTrailingNotRoot
    have hbound := (RealRooted.rootMultiplicity_bounds_of_prec hPrec x).2
    have hpos := (Polynomial.rootMultiplicity_pos A.charpoly_monic.ne_zero).2 hx
    lia
  have hTrailingSimple : ∀ x : ℝ,
      (A.submatrix Fin.succ Fin.succ).charpoly.IsRoot x →
        (A.submatrix Fin.succ Fin.succ).charpoly.rootMultiplicity x = 1 := by
    intro x hx
    have hFullNotRoot : ¬A.charpoly.IsRoot x := by
      intro hxFull
      exact hNoCommon x ⟨hxFull, hx⟩
    have hFullMult : A.charpoly.rootMultiplicity x = 0 :=
      Polynomial.rootMultiplicity_eq_zero hFullNotRoot
    have hbound := (RealRooted.rootMultiplicity_bounds_of_prec hPrec x).1
    have hpos := (Polynomial.rootMultiplicity_pos
      (A.submatrix Fin.succ Fin.succ).charpoly_monic.ne_zero).2 hx
    lia
  refine ⟨hInter, hFullSimple, hTrailingSimple, hNoCommon, ?_⟩
  intro x hx
  have hxRoot : A.charpoly.IsRoot x :=
    (Polynomial.mem_roots A.charpoly_monic.ne_zero).mp hx
  have hxNonneg : 0 ≤ x := hA.nonneg_of_isRoot_charpoly hxRoot
  have hxNe : x ≠ 0 := by
    intro hxZero
    subst x
    have hcoeff : A.charpoly.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact hxRoot.eq_zero
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, hcoeff, mul_zero]
  exact lt_of_le_of_ne hxNonneg (Ne.symm hxNe)

/-- Simultaneously reversing the rows and columns of a finite totally
nonnegative matrix preserves total nonnegativity. -/
theorem IsTotallyNonneg.finRev {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsTotallyNonneg) :
    (Matrix.reindex Fin.revPerm Fin.revPerm A).IsTotallyNonneg := by
  intro n rows cols hrows hcols
  let rows' : Fin n → Fin N := fun i ↦ (rows i.rev).rev
  let cols' : Fin n → Fin N := fun i ↦ (cols i.rev).rev
  have hrows' : StrictMono rows' := by
    intro i j hij
    apply Fin.rev_lt_rev.mpr
    exact hrows (Fin.rev_lt_rev.mpr hij)
  have hcols' : StrictMono cols' := by
    intro i j hij
    apply Fin.rev_lt_rev.mpr
    exact hcols (Fin.rev_lt_rev.mpr hij)
  rw [← Matrix.det_submatrix_equiv_self Fin.revPerm]
  change 0 ≤ (A.submatrix rows' cols').det
  exact hA hrows' hcols'

/-- Strict leading-principal interlacing for the classical oscillatory
criterion. This is the leading-section orientation of
`IsTotallyNonneg.trailing_charpoly_strictInterlaces`. -/
theorem IsTotallyNonneg.leading_charpoly_strictInterlaces {N : ℕ}
    {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0)
    (hsuper : ∀ i : Fin N, 0 < A i.castSucc i.succ)
    (hsub : ∀ i : Fin N, 0 < A i.succ i.castSucc) :
    RealRooted.Interlaces
        (A.submatrix Fin.castSucc Fin.castSucc).charpoly A.charpoly ∧
      (∀ x : ℝ, A.charpoly.IsRoot x →
        A.charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, (A.submatrix Fin.castSucc Fin.castSucc).charpoly.IsRoot x →
        (A.submatrix Fin.castSucc Fin.castSucc).charpoly.rootMultiplicity x = 1) ∧
      (∀ x : ℝ, ¬(A.charpoly.IsRoot x ∧
        (A.submatrix Fin.castSucc Fin.castSucc).charpoly.IsRoot x)) ∧
      ∀ x ∈ A.charpoly.roots, 0 < x := by
  let B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
    Matrix.reindex Fin.revPerm Fin.revPerm A
  have hB : B.IsTotallyNonneg := by
    exact hA.finRev
  have hBdet : B.det ≠ 0 := by
    simpa [B] using hdet
  have hBsuper : ∀ i : Fin N, 0 < B i.castSucc i.succ := by
    intro i
    simpa [B, Matrix.submatrix, Fin.rev_castSucc, Fin.rev_succ] using hsub i.rev
  have hBsub : ∀ i : Fin N, 0 < B i.succ i.castSucc := by
    intro i
    simpa [B, Matrix.submatrix, Fin.rev_castSucc, Fin.rev_succ] using hsuper i.rev
  have hstrict := hB.trailing_charpoly_strictInterlaces hBdet hBsuper hBsub
  have hBchar : B.charpoly = A.charpoly := by
    simpa [B] using Matrix.charpoly_reindex Fin.revPerm A
  have hBtail : (B.submatrix Fin.succ Fin.succ).charpoly =
      (A.submatrix Fin.castSucc Fin.castSucc).charpoly := by
    rw [← Matrix.charpoly_reindex Fin.revPerm
      (A.submatrix Fin.castSucc Fin.castSucc)]
    congr 1
    ext i j
    simp [B, Matrix.submatrix, Matrix.reindex_apply,
      Fin.rev_succ]
  simpa only [hBchar, hBtail] using hstrict

end Matrix
