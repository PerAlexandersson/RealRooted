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
import RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Lemmas
public import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg
import RealRooted.Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Border
import all RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Border

/-!
# Whitney elimination and restoration

One-step Whitney–Neville elimination and restoration, preservation of total
nonnegativity, and determinant invariance.
-/

@[expose] public section

namespace Matrix

open scoped BigOperators

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
      simp [whitneyEliminateAt, M, v, Matrix.updateRow_apply, hi, hrow]
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
  change (A.submatrix rows cols).det + _ = _; ring

private theorem submatrix_whitneyEliminateAt_eq_of_not_mem {m n q : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m)
    (c : Fin (n + 1)) (rows : Fin q → Fin (m + 1))
    (cols : Fin q → Fin (n + 1)) (hu : ∀ i, rows i ≠ s.succ) :
    (whitneyEliminateAt A s c).submatrix rows cols =
      A.submatrix rows cols := by
  ext i j
  simp [whitneyEliminateAt, Matrix.updateRow_apply, hu i]

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
      simp [whitneyEliminateAt, hc, Matrix.updateRow_apply, hne, htail _ hgt]
    · have hzero : A (rows k.succ) (cols 0) = 0 :=
        hleft (rows k.succ) (le_trans (Fin.le_def.mpr (by simp)) hgt.le)
          _ hcolLt
      simp [whitneyEliminateAt, Matrix.updateRow_apply, hne, hzero]

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
    · simp [augRows, hrow0]
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
  have hborderNonneg : 0 ≤ (borderAt M 0 0 b x (A s.castSucc c)).det := by
    simpa [hborder] using hA haugRows haugCols
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
    field_simp [hpivot.ne']; nlinarith [hplucker, hsmallEq]
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
      (M.submatrix r.succAbove j.succAbove).det = 0 :=
    fun j => le_antisymm (h j) (hminor j)
  rw [Matrix.det_succ_row M r] at hdet; simp [hzero] at hdet

/-- Replacing the selected lower row by the adjacent pivot row preserves its order. -/
private theorem whitney_replaced_rows_strictMono {m q : ℕ}
    (rows : Fin (q + 1) → Fin (m + 1)) (r : Fin q) (s : Fin m)
    (hrows : StrictMono rows) (hp : rows r.succ = s.succ)
    (hs : ∀ i, rows i ≠ s.castSucc) :
    StrictMono (Function.update rows r.succ s.castSucc) := by
  apply strictMono_update_at rows r.succ s.castSucc hrows
  · intro i hi
    have hiu : rows i < s.succ := by simpa [hp] using hrows hi
    have hle : rows i ≤ s.castSucc := by
      apply Fin.le_iff_val_le_val.2
      change (rows i).val < s.val + 1 at hiu
      exact Nat.lt_succ_iff.mp hiu
    exact lt_of_le_of_ne hle (hs i)
  · intro i hi
    exact lt_trans s.castSucc_lt_succ (by rw [← hp]; exact hrows hi)

/-- Replacing the row immediately before the selected lower row preserves its order. -/
private theorem whitney_prior_rows_strictMono {m q : ℕ}
    (rows : Fin (q + 1) → Fin (m + 1)) (r : Fin q) (s : Fin m)
    (hrows : StrictMono rows) (hp : rows r.succ = s.succ)
    (hs : ∀ i, rows i ≠ s.castSucc) :
    StrictMono (Function.update rows r.castSucc s.castSucc) := by
  apply strictMono_update_at rows r.castSucc s.castSucc hrows
  · intro i hi
    have hir : rows i < rows r.castSucc := hrows hi
    have hprior : rows r.castSucc < s.castSucc := by
      have hlt : rows r.castSucc < s.succ := by
        simpa [hp] using hrows r.castSucc_lt_succ
      have hle : rows r.castSucc ≤ s.castSucc := by
        apply Fin.le_iff_val_le_val.2
        change (rows r.castSucc).val < s.val + 1 at hlt
        exact Nat.lt_succ_iff.mp hlt
      exact lt_of_le_of_ne hle (hs r.castSucc)
    exact hir.trans hprior
  · intro i hi
    have hindex : r.succ ≤ i := by
      apply Fin.le_iff_val_le_val.2
      change r.val < i.val at hi
      exact Nat.succ_le_iff.2 hi
    exact lt_of_lt_of_le (by simp [hp]) (hrows.monotone hindex)

/-- The bordered Plücker identity rewritten entirely in terms of ordered minors of `A`. -/
private theorem whitney_submatrix_plucker {m n q : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ)
    (rows : Fin (q + 1) → Fin (m + 1)) (cols : Fin (q + 1) → Fin (n + 1))
    (r : Fin q) (s : Fin m) (baseRows : Fin q → Fin (m + 1))
    (baseCols : Fin q → Fin (n + 1)) (replaced qrows : Fin (q + 1) → Fin (m + 1))
    (j : Fin (q + 1)) (hbaseCols : baseCols = j.removeNth cols)
    (hM0 : 0 < (A.submatrix baseRows baseCols).det)
    (hP : Function.update baseRows r (rows r.castSucc) = r.succ.removeNth rows)
    (hE : Function.update baseRows r s.succ = r.castSucc.removeNth rows)
    (hDA : r.succ.insertNth s.succ
      (Function.update baseRows r (rows r.castSucc)) = rows)
    (hQ : r.succ.insertNth s.succ baseRows = qrows)
    (hDC : r.castSucc.insertNth (rows r.castSucc) baseRows = replaced) :
    (A.submatrix baseRows baseCols).det * (A.submatrix rows cols).det =
      (A.submatrix (r.succ.removeNth rows) baseCols).det *
          (A.submatrix qrows cols).det +
        (A.submatrix (r.castSucc.removeNth rows) baseCols).det *
          (A.submatrix replaced cols).det := by
  let M0 := A.submatrix baseRows baseCols
  let b : Fin q → ℝ := fun i ↦ A (baseRows i) (cols j)
  let x : Fin q → ℝ := fun a ↦ A (rows r.castSucc) (baseCols a)
  let y : Fin q → ℝ := fun a ↦ A s.succ (baseCols a)
  let alpha := A (rows r.castSucc) (cols j)
  let beta := A s.succ (cols j)
  have hsurj : Function.Surjective M0.vecMul := by
    apply Matrix.vecMul_surjective_iff_isUnit.2
    exact (Matrix.isUnit_iff_isUnit_det M0).2 (isUnit_iff_ne_zero.2 hM0.ne')
  obtain ⟨u, hu⟩ := hsurj x
  obtain ⟨v, hv⟩ := hsurj y
  have hPdet : (M0.updateRow r x).det =
      (A.submatrix (r.succ.removeNth rows) baseCols).det := by
    rw [updateRow_submatrix, hP]
  have hEdet : (M0.updateRow r y).det =
      (A.submatrix (r.castSucc.removeNth rows) baseCols).det := by
    rw [updateRow_submatrix, hE]
  have hDAdet : (borderAt (M0.updateRow r x) r.succ j
      (Function.update b r alpha) y beta).det = (A.submatrix rows cols).det := by
    rw [updateRow_submatrix]
    have hb : Function.update b r alpha =
        fun i ↦ A ((Function.update baseRows r (rows r.castSucc)) i) (cols j) := by
      ext i
      by_cases hi : i = r <;> simp [b, alpha, Function.update, hi]
    rw [hb, borderAt_submatrix, hDA, hbaseCols, j.insertNth_self_removeNth cols]
  have hQdet : (borderAt M0 r.succ j b y beta).det =
      (A.submatrix qrows cols).det := by
    rw [borderAt_submatrix, hQ, hbaseCols, j.insertNth_self_removeNth cols]
  have hDCdet : (borderAt M0 r.castSucc j b x alpha).det =
      (A.submatrix replaced cols).det := by
    rw [borderAt_submatrix, hDC, hbaseCols, j.insertNth_self_removeNth cols]
  have hswap : (borderAt M0 r.succ j b x alpha).det =
      -(A.submatrix replaced cols).det := by
    rw [det_borderAt_pred_insert M0 r.succ (by simp) j b x alpha,
      Fin.pred_succ, hDCdet]
  have hplucker := det_borderAt_plucker M0 r r.succ j b x y u v alpha beta hu hv
  rw [hDAdet, hPdet, hQdet, hEdet, hswap] at hplucker
  linarith

/-- Removing the changed row and restoring the pivot selector recovers the base rows. -/
private theorem whitney_base_rows_recover {m q : ℕ}
    (rows : Fin (q + 1) → Fin (m + 1)) (r : Fin q) (s : Fin m)
    (hp : rows r.succ = s.succ) :
    let replaced := Function.update rows r.succ s.castSucc
    let baseRows := r.castSucc.removeNth replaced
    Function.update (r.castSucc.removeNth rows) r s.castSucc = baseRows := by
  let replaced := Function.update rows r.succ s.castSucc
  let baseRows := r.castSucc.removeNth replaced
  obtain ⟨_, hE, _, _, _⟩ := whitney_adjacent_selector_identities rows r
    s.castSucc (rows r.castSucc) s.succ hp rfl
  change Function.update baseRows r s.succ = r.castSucc.removeNth rows at hE
  have hbase : baseRows r = s.castSucc := by
    simp [baseRows, replaced, Fin.removeNth, Function.update]
  rw [← hE, Function.update_idem]
  exact Function.update_eq_self_iff.2 hbase.symm

/-- The induction hypothesis gives the smaller eliminated minor identity used in Whitney's
hard branch. -/
private theorem whitney_smaller_minor_identity {m n q : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m) (c : Fin (n + 1))
    (rows : Fin (q + 1) → Fin (m + 1)) (baseCols : Fin q → Fin (n + 1))
    (r : Fin q) (hrows : StrictMono rows) (hp : rows r.succ = s.succ)
    (hpivot : A s.castSucc c ≠ 0) :
    let replaced := Function.update rows r.succ s.castSucc
    let baseRows := r.castSucc.removeNth replaced
    A s.castSucc c * ((whitneyEliminateAt A s c).submatrix
        (r.castSucc.removeNth rows) baseCols).det =
      A s.castSucc c * (A.submatrix (r.castSucc.removeNth rows) baseCols).det -
        A s.succ c * (A.submatrix baseRows baseCols).det := by
  let replaced := Function.update rows r.succ s.castSucc
  let baseRows := r.castSucc.removeNth replaced
  rw [det_submatrix_whitneyEliminateAt A s c (r.castSucc.removeNth rows) baseCols
    (hrows.comp (Fin.strictMono_succAbove r.castSucc)) r,
    whitney_base_rows_recover rows r s hp]
  · field_simp [hpivot]
  · simp [hp, Fin.removeNth]

/-- The noninitial hard minor in Whitney elimination is nonnegative. -/
private theorem det_submatrix_whitneyEliminateAt_nonneg_of_later_row {m n q : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m) (c : Fin (n + 1))
    (hA : A.IsTotallyNonnegRect) (hpivot : 0 < A s.castSucc c)
    (rows : Fin (q + 1) → Fin (m + 1)) (cols : Fin (q + 1) → Fin (n + 1))
    (hrows : StrictMono rows) (hcols : StrictMono cols) (p : Fin (q + 1))
    (hp : rows p = s.succ) (hs : ∀ i, rows i ≠ s.castSucc) (hp0 : p ≠ 0)
    (ih : ∀ (rows : Fin q → Fin (m + 1)) (cols : Fin q → Fin (n + 1)),
      StrictMono rows → StrictMono cols →
        0 ≤ ((whitneyEliminateAt A s c).submatrix rows cols).det) :
    0 ≤ ((whitneyEliminateAt A s c).submatrix rows cols).det := by
  let r : Fin q := p.pred hp0
  have hrp : r.succ = p := Fin.succ_pred p hp0
  have hp' : rows r.succ = s.succ := by rw [hrp]; exact hp
  let prior := rows r.castSucc
  let replaced := Function.update rows r.succ s.castSucc
  let qrows := Function.update rows r.castSucc s.castSucc
  let baseRows := r.castSucc.removeNth replaced
  have hreplaced : StrictMono replaced := whitney_replaced_rows_strictMono rows r s hrows hp' hs
  have hqrows : StrictMono qrows := whitney_prior_rows_strictMono rows r s hrows hp' hs
  have hbaseRows : StrictMono baseRows :=
    hreplaced.comp (Fin.strictMono_succAbove r.castSucc)
  obtain ⟨hProws, hErows, hDArows, hQrows, hDCrows⟩ :=
    whitney_adjacent_selector_identities rows r s.castSucc prior s.succ hp' rfl
  have hDCnonneg : 0 ≤ (A.submatrix replaced cols).det := hA hreplaced hcols
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
      exact hA (hreplaced.comp (Fin.strictMono_succAbove r.castSucc))
        (hcols.comp (Fin.strictMono_succAbove j))
    obtain ⟨j, hD0pos⟩ :=
      exists_pos_deleted_minor_of_det_pos MC r.castSucc hdeleted hDCpos
    let baseCols := j.removeNth cols
    let M0 := A.submatrix baseRows baseCols
    have hM0det : 0 < M0.det := by exact hD0pos
    have hplucker := whitney_submatrix_plucker A rows cols r s baseRows baseCols
      replaced qrows j rfl hM0det hProws hErows hDArows hQrows hDCrows
    have hPnonneg : 0 ≤ (A.submatrix (r.succ.removeNth rows) baseCols).det :=
      hA (hrows.comp (Fin.strictMono_succAbove r.succ))
        (hcols.comp (Fin.strictMono_succAbove j))
    have hQnonneg : 0 ≤ (A.submatrix qrows cols).det := hA hqrows hcols
    have hsmall : 0 ≤ ((whitneyEliminateAt A s c).submatrix
        (r.castSucc.removeNth rows) baseCols).det :=
      ih _ _ (hrows.comp (Fin.strictMono_succAbove r.castSucc))
        (hcols.comp (Fin.strictMono_succAbove j))
    have hsmallEq :=
      whitney_smaller_minor_identity A s c rows baseCols r hrows hp' hpivot.ne'
    rw [det_submatrix_whitneyEliminateAt A s c rows cols hrows p hp,
      show Function.update rows p s.castSucc = replaced by rw [← hrp]]
    exact whitney_hard_minor_nonneg hpivot hM0det hPnonneg hQnonneg hDCnonneg
      hsmall hplucker hsmallEq

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
          · exact det_submatrix_whitneyEliminateAt_nonneg_of_later_row A s c hA hpivot
              rows cols hrows hcols p hp hs hp0 ih
      · simp only [not_exists] at hu
        rw [submatrix_whitneyEliminateAt_eq_of_not_mem A s c rows cols hu]
        exact hA hrows hcols

/-- Whitney's one-row elimination preserves total nonnegativity when the
eliminated entry is followed by a zero tail in the first column. -/
theorem IsTotallyNonnegRect.whitneyEliminateFirst {m n : ℕ}
    {A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsTotallyNonnegRect) (s : Fin m)
    (hpivot : 0 < A s.castSucc 0)
    (htail : ∀ i, s.succ < i → A i 0 = 0) :
    (whitneyEliminateFirst A s).IsTotallyNonnegRect :=
  hA.whitneyEliminateAt_nonneg s 0 hpivot htail fun _ _ j hj ↦ absurd hj (Fin.not_lt_zero j)

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
        simp [M, v, Matrix.updateRow_apply, hrp, hr]
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
      simp [Matrix.whitneyRestoreFirst, Matrix.updateRow_apply, hu i]
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
    simp [Matrix.whitneyRestoreFirst, Matrix.updateRow_apply, hi]

/-- A nonnegative adjacent lower transvection is totally nonnegative. -/
theorem isTotallyNonneg_transvection_succ_castSucc {m : ℕ}
    (s : Fin m) (c : ℝ) (hc : 0 ≤ c) :
    (Matrix.transvection s.succ s.castSucc c).IsTotallyNonneg := by
  have hrestore :=
    (show (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).IsTotallyNonneg by simp).toRect
      |>.whitneyRestoreFirst_nonneg s c hc
  rw [whitneyRestoreFirst_eq_transvection_mul, Matrix.mul_one] at hrestore
  exact hrestore.toSquare

private theorem trailing_submatrix_mul_of_first_product_zero {m : ℕ}
    (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hzero : ∀ i j : Fin m, A i.succ 0 * B 0 j.succ = 0) :
    (A * B).submatrix Fin.succ Fin.succ =
      A.submatrix Fin.succ Fin.succ * B.submatrix Fin.succ Fin.succ := by
  ext i j
  change (A * B) i.succ j.succ =
    (A.submatrix Fin.succ Fin.succ *
      B.submatrix Fin.succ Fin.succ) i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [Fin.sum_univ_succ]; simp [hzero]

private theorem whitneyRestoreFirst_eliminateAt_aux {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m)
    (c : Fin (n + 1)) :
    Matrix.whitneyRestoreFirst (whitneyEliminateAt A s c) s
      (A s.succ c / A s.castSucc c) = A := by
  ext i j
  by_cases hi : i = s.succ <;>
    simp [Matrix.whitneyRestoreFirst, whitneyEliminateAt, hi,
      Fin.ne_of_lt s.castSucc_lt_succ]

/-- Restoring with the pivot ratio exactly reverses one Whitney elimination
step. -/
theorem whitneyRestoreFirst_eliminate {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m) :
    Matrix.whitneyRestoreFirst (whitneyEliminateFirst A s) s
      (A s.succ 0 / A s.castSucc 0) = A := by
  simpa only [whitneyEliminateFirst] using whitneyRestoreFirst_eliminateAt_aux A s 0

/-- Restoring with the selected-column pivot ratio reverses the corresponding
Whitney elimination. -/
theorem whitneyRestoreFirst_eliminateAt {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (s : Fin m)
    (c : Fin (n + 1)) :
    Matrix.whitneyRestoreFirst (whitneyEliminateAt A s c) s
      (A s.succ c / A s.castSucc c) = A :=
  whitneyRestoreFirst_eliminateAt_aux A s c

private theorem det_whitneyEliminateAt_aux {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (s : Fin m)
    (c : Fin (m + 1)) :
    (whitneyEliminateAt A s c).det = A.det := by
  let ratio := A s.succ c / A s.castSucc c
  have hmatrix : whitneyEliminateAt A s c =
      A.updateRow s.succ (A s.succ + (-ratio) • A s.castSucc) := by
    ext i j
    by_cases hi : i = s.succ <;>
      simp [whitneyEliminateAt, ratio, Matrix.updateRow_apply, hi]; ring
  rw [hmatrix, Matrix.det_updateRow_add_smul_self]
  exact Fin.ne_of_gt s.castSucc_lt_succ

/-- A Whitney row operation does not change the determinant. -/
theorem det_whitneyEliminateFirst {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (s : Fin m) :
    (whitneyEliminateFirst A s).det = A.det := by
  simpa only [whitneyEliminateFirst] using det_whitneyEliminateAt_aux A s 0

/-- A Whitney row operation in any selected column preserves determinant. -/
theorem det_whitneyEliminateAt {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (s : Fin m)
    (c : Fin (m + 1)) :
    (whitneyEliminateAt A s c).det = A.det :=
  det_whitneyEliminateAt_aux A s c

/-- Under an already-cleared prefix, a zero in a column of a nonsingular TN
matrix forces the rest of that column to vanish. -/
private theorem IsTotallyNonneg.column_zero_tail_of_det_ne_zero
    {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0)
    {c i : Fin (N + 1)} (hleft : ∀ k, k < c → A i k = 0)
    (hi : A i c = 0) : ∀ j, i < j → A j c = 0 := by
  intro j hij
  by_contra hj
  have hjpos : 0 < A j c := lt_of_le_of_ne (hA.nonneg j c) (Ne.symm hj)
  have hrow : ∀ k, A i k = 0 := by
    intro k
    rcases lt_trichotomy k c with hkc | rfl | hck
    · exact hleft k hkc
    · exact hi
    · let rows : Fin 2 → Fin (N + 1) := ![i, j]
      let cols : Fin 2 → Fin (N + 1) := ![c, k]
      have hrows : StrictMono rows := strictMono_pair hij
      have hcols : StrictMono cols := strictMono_pair hck
      have hminor := hA hrows hcols
      simp only [Matrix.det_fin_two, Matrix.submatrix_apply, rows, cols,
        Matrix.cons_val_zero, Matrix.cons_val_one] at hminor
      rw [hi, zero_mul, zero_sub] at hminor; nlinarith [hA.nonneg i k]
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
  · have htail := hA.column_zero_tail_of_det_ne_zero hdet
      (fun k hk ↦ (Fin.not_lt_zero k hk).elim) hzero i
    exact (hi.ne' (htail (Fin.castSucc_pred_lt hi0))).elim
  · exact lt_of_le_of_ne hnonneg (Ne.symm hzero)

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
  have hnonneg := hA.nonneg p c
  by_cases hzero : A p c = 0
  · have hleft : ∀ k, k < c → A p k = 0 := by
      intro k hkc
      apply hprefix p k (Fin.lt_def.mp hkc)
      have hpval : p.val + 1 = i.val := by
        dsimp [p]
        lia
      lia
    have htail := hA.column_zero_tail_of_det_ne_zero hdet hleft hzero i
    have hpi : p < i := by
      apply Fin.lt_def.2
      dsimp [p]
      lia
    exact (hi.ne' (htail hpi)).elim
  · exact lt_of_le_of_ne hnonneg (Ne.symm hzero)


end WhitneyElimination

end Matrix
