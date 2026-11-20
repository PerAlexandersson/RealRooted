/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Basic.Real.Star
import Mathlib.Algebra.Order.Star.Real
public import RealRooted.Mathlib.LinearAlgebra.Matrix.GantmacherKrein
import RealRooted.Mathlib.LinearAlgebra.Matrix.Oscillatory
import RealRooted.Mathlib.LinearAlgebra.Matrix.Charpoly.Submatrix
public import Mathlib.Data.Fin.Rev
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Transvection
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
public import Mathlib.Analysis.Real.Sqrt
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Charpoly
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.PrimitivityCriteria
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg
import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Border determinants, ordered minors, and continuants

Border insertion, determinant signs, and Plücker identities for naturally
ordered minors. Shared implementation lemmas remain private; the elimination
layer imports them internally with `import all`.
-/

@[expose] public section

namespace Matrix

open scoped BigOperators

section WhitneyDeterminants

variable {R : Type*} [CommRing R]

/-- Adjoin a row and a column at specified positions. -/
private def borderAt {q : ℕ} (A : Matrix (Fin q) (Fin q) R)
    (rp cp : Fin (q + 1)) (b x : Fin q → R) (a : R) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) R :=
  rp.insertNth (cp.insertNth a x) (fun i ↦ cp.insertNth (b i) (A i))

private lemma insertNth_apply_eq_cons_cycleRange {q : ℕ} {α : Type*}
    (p : Fin (q + 1)) (a : α) (x : Fin q → α) (i : Fin (q + 1)) :
    (@Fin.insertNth q (fun _ ↦ α) p a x) i =
      (@Fin.cons q (fun _ ↦ α) a x) (p.cycleRange i) := by
  simp

omit [CommRing R] in
private lemma borderAt_submatrix {q : ℕ} {ι κ : Type*}
    (M : Matrix ι κ R) (rows : Fin q → ι) (cols : Fin q → κ)
    (rp cp : Fin (q + 1)) (row : ι) (col : κ) :
    borderAt (M.submatrix rows cols) rp cp
        (fun i ↦ M (rows i) col) (fun j ↦ M row (cols j)) (M row col) =
      M.submatrix (rp.insertNth row rows) (cp.insertNth col cols) := by
  ext i j
  refine Fin.succAboveCases rp ?_ (fun _ ↦ ?_) i <;>
    refine Fin.succAboveCases cp ?_ (fun _ ↦ ?_) j <;> simp [borderAt]

omit [CommRing R] in
private lemma updateRow_submatrix {q : ℕ} {ι κ : Type*}
    [DecidableEq (Fin q)] (M : Matrix ι κ R)
    (rows : Fin q → ι) (cols : Fin q → κ) (r : Fin q) (row : ι) :
    (M.submatrix rows cols).updateRow r (fun j ↦ M row (cols j)) =
      M.submatrix (Function.update rows r row) cols := by
  ext i j
  by_cases hi : i = r <;> simp [Matrix.updateRow, Function.update, hi]

private lemma strictMono_update_at {q : ℕ} {ι : Type*} [LinearOrder ι]
    (f : Fin q → ι) (p : Fin q) (x : ι) (hf : StrictMono f)
    (hleft : ∀ i, i < p → f i < x)
    (hright : ∀ i, p < i → x < f i) :
    StrictMono (Function.update f p x) := by
  intro i j hij
  have := hf hij
  by_cases hi : i = p <;> by_cases hj : j = p <;> subst_vars <;>
    simp_all [Function.update]

private lemma strictMono_pair {ι : Type*} [Preorder ι] {i j : ι} (hij : i < j) :
    StrictMono ![i, j] := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

/-- The five adjacent deletion/insertion identities used to recognize every
matrix in Whitney's hard branch as a naturally ordered minor. -/
private theorem whitney_adjacent_selector_identities {q : ℕ} {ι : Type*}
    (rows : Fin (q + 1) → ι) (r : Fin q) (pivot prior changed : ι)
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
    · simp [base, replaced, Fin.removeNth,
        Fin.succAbove_castSucc_of_lt _ _ hir,
        Fin.succAbove_succ_of_le _ _ hir.le, Function.update,
        ne_of_lt hir, ne_of_lt (Fin.castSucc_lt_succ_iff.2 hir.le)]
    · simp [Fin.removeNth, Function.update, hprior]
    · simp [base, replaced, Fin.removeNth,
        Fin.succAbove_castSucc_of_le _ _ hri.le,
        Fin.succAbove_succ_of_lt _ _ hri, Function.update, ne_of_gt hri]
  have hE : Function.update base r changed = r.castSucc.removeNth rows := by
    ext i
    rcases lt_trichotomy i r with hir | rfl | hri
    · simp [base, replaced, Fin.removeNth,
        Fin.succAbove_castSucc_of_lt _ _ hir, Function.update,
        ne_of_lt hir, ne_of_lt (Fin.castSucc_lt_succ_iff.2 hir.le)]
    · simp [Fin.removeNth, Function.update, hchanged]
    · simp [base, replaced, Fin.removeNth,
        Fin.succAbove_castSucc_of_le _ _ hri.le, Function.update, ne_of_gt hri]
  have hDA : r.succ.insertNth changed (Function.update base r prior) = rows :=
    Fin.insertNth_eq_iff.2 ⟨hchanged.symm, hP⟩
  have hQ : r.succ.insertNth changed base =
      Function.update rows r.castSucc pivot := by
    apply Fin.insertNth_eq_iff.2
    constructor
    · simp [Function.update, hpositions.symm, hchanged]
    · ext i
      rcases lt_trichotomy i r with hir | rfl | hri
      · simp [base, replaced, Fin.removeNth,
          Fin.succAbove_castSucc_of_lt _ _ hir,
          Fin.succAbove_succ_of_le _ _ hir.le, Function.update,
          ne_of_lt hir, ne_of_lt (Fin.castSucc_lt_succ_iff.2 hir.le)]
      · simp [base, replaced, Fin.removeNth, Function.update]
      · simp [base, replaced, Fin.removeNth,
          Fin.succAbove_castSucc_of_le _ _ hri.le,
          Fin.succAbove_succ_of_lt _ _ hri, Function.update, ne_of_gt hri,
          ne_of_gt (r.castSucc_lt_succ.trans (Fin.succ_lt_succ_iff.2 hri))]
  have hDC : r.castSucc.insertNth prior base = replaced := by
    apply Fin.insertNth_eq_iff.2
    constructor
    · simp [replaced, hpositions, hprior]
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
    rw [show q + q = 2 * q by lia, pow_mul]; simp
  rw [hat, hdet, hlast, hdet]
  simp only [Fin.val_last, hlastSign]; ring

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
    change A i j = A i j; rfl
  have hminor1 : M.submatrix (1 : Fin (q + 2)).succAbove Fin.succ =
      A.updateRow 0 x := by
    ext i j
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · change x j = (A.updateRow 0 x) 0 j
      simp
    · change A i.succ j = (A.updateRow 0 x) i.succ j
      simp
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
  simp [M, borderAt]; ring

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

/-! ## Tridiagonal determinant recurrence -/

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
    rw [Fin.succAbove_zero, hBtail]; simp
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  simp_rw [hcol]
  simp only [Nat.succ_eq_add_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    Std.le_refl, Nat.eq_zero_of_le_zero, pow_zero, one_mul,
    Fin.succAbove_zero, Fin.succ_zero_eq_one, Nat.one_mod, pow_one,
    neg_mul, Fin.val_succ, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, Matrix.submatrix_submatrix]
  rw [hoff]
  rw [Matrix.submatrix_submatrix]; ring

/-- The characteristic polynomial of a tridiagonal matrix satisfies the
continuant recurrence obtained by deleting its first row and column. -/
theorem charpoly_tridiagonal_rec {R : Type*} [CommRing R] {N : ℕ}
    (T : Matrix (Fin (N + 2)) (Fin (N + 2)) R)
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
      simp only [Fin.val_zero, Fin.val_succ]; lia
    have hzero := hlower i.succ.succ 0 hgap
    change T.charmatrix i.succ.succ 0 = 0
    rw [Matrix.charmatrix_apply_ne _ _ _
      (ne_of_gt (Fin.succ_pos i.succ)), hzero, map_zero,
      neg_zero]
  have hrow : ∀ j : Fin N, M 0 j.succ.succ = 0 := by
    intro j
    have hgap : (0 : Fin (N + 2)).val + 1 < j.succ.succ.val := by
      simp only [Fin.val_zero, Fin.val_succ]; lia
    have hzero := hupper 0 j.succ.succ hgap
    change T.charmatrix 0 j.succ.succ = 0
    rw [Matrix.charmatrix_apply_ne _ _ _
      (ne_of_lt (Fin.succ_pos j.succ)), hzero, map_zero,
      neg_zero]
  rw [Matrix.charpoly, det_tridiagonal_first_rec M hcol hrow]
  dsimp only [M]
  rw [charmatrix_submatrix_self T Fin.succ (Fin.succ_injective (N + 1)),
    charmatrix_submatrix_self (T.submatrix Fin.succ Fin.succ) Fin.succ
      (Fin.succ_injective N)]
  rw [Matrix.charmatrix_apply_eq,
    Matrix.charmatrix_apply_ne T 1 0 one_ne_zero,
    Matrix.charmatrix_apply_ne T 0 1 zero_ne_one]
  simp only [Matrix.charpoly, map_mul]; ring

end Matrix
