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
public import RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Elimination
import all RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Elimination

/-!
# Whitney column sweeps and tridiagonal reduction

Iterated column sweeps, triangular factorizations, and reduction to upper
Hessenberg and tridiagonal matrices.
-/

@[expose] public section

namespace Matrix

open scoped BigOperators

section WhitneyElimination

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
      exact ⟨hA, rfl, hprefix,
        fun i hi ↦ (Nat.not_lt_of_ge (Nat.le_of_lt_succ i.isLt) hi).elim⟩
  | succ t ih =>
      have htActive : t < N - (c.val + 1) := by lia
      obtain ⟨hB, hBdet, hBprefix, hBtail⟩ := ih htActive.le
      let s : Fin N := ⟨N - (t + 1), by lia⟩
      let B := whitneyClearColumnAux A c t
      have hsval : s.succ.val = N - t := by simp [s]; lia
      have hsc : c.val + 1 < s.succ.val := by rw [hsval]; lia
      have hBdetne : B.det ≠ 0 := by rw [hBdet]; exact hdet
      rw [whitneyClearColumnAux, dite_eq_left htActive]
      dsimp only
      by_cases hzero : B s.succ c = 0
      · rw [ite_eq_left hzero]
        refine ⟨hB, hBdet, hBprefix, ?_⟩
        intro i hi
        by_cases his : i = s.succ
        · simpa [his] using hzero
        · apply hBtail i
          have hle : s.succ.val ≤ i.val := by
            rw [hsval]; lia
          rw [← hsval]
          exact lt_of_le_of_ne hle (fun h ↦ his (Fin.ext h.symm))
      · rw [ite_eq_right hzero]
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
          have hsi' := Fin.le_def.mp hsi
          rw [Fin.val_castSucc] at hsi'
          rw [Fin.val_succ] at hsc
          lia
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
              dsimp [s] at hkr ⊢; lia
            change whitneyEliminateAt B s c s.succ k = 0
            simp [whitneyEliminateAt, htargetZero, hpivotZero]
          · change whitneyEliminateAt B s c r k = 0
            simpa [whitneyEliminateAt, hrs] using hBprefix r k hkc hkr
        · intro i hi
          by_cases his : i = s.succ
          · subst i
            change whitneyEliminateAt B s c s.succ c = 0
            simp only [whitneyEliminateAt, Matrix.updateRow_self]
            field_simp [hpivot.ne']; ring
          · have hit : s.succ < i := by
              apply Fin.lt_def.2
              rw [hsval]
              have hv : i.val ≠ s.succ.val := fun h ↦ his (Fin.ext h)
              lia
            change whitneyEliminateAt B s c i c = 0
            simpa [whitneyEliminateAt, his] using htail i hit

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
          (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ).IsTotallyNonneg := by simp
      exact ⟨hone, by simp [whitneyClearColumnLowerAux, whitneyClearColumnAux]⟩
  | succ t ih =>
      have htActive : t < N - (c.val + 1) := by lia
      obtain ⟨hL, hfactor⟩ := ih htActive.le
      obtain ⟨hB, hBdet, hBprefix, hBtail⟩ :=
        whitneyClearColumnAux_spec A hA hdet c hprefix t htActive.le
      let s : Fin N := ⟨N - (t + 1), by lia⟩
      let B := whitneyClearColumnAux A c t
      let L := whitneyClearColumnLowerAux A c t
      have hsval : s.succ.val = N - t := by simp [s]; lia
      have hsc : c.val + 1 < s.succ.val := by rw [hsval]; lia
      have hBdetne : B.det ≠ 0 := by rw [hBdet]; exact hdet
      have hclear : whitneyClearColumnAux A c (t + 1) =
          if B s.succ c = 0 then B else whitneyEliminateAt B s c := by
        rw [whitneyClearColumnAux, dite_eq_left htActive]
      have hlower : whitneyClearColumnLowerAux A c (t + 1) =
          if B s.succ c = 0 then L
          else L * Matrix.transvection s.succ s.castSucc
            (B s.succ c / B s.castSucc c) := by
        rw [whitneyClearColumnLowerAux, dite_eq_left htActive]
      rw [hclear, hlower]
      by_cases hzero : B s.succ c = 0
      · rw [ite_eq_left hzero, ite_eq_left hzero]
        exact ⟨hL, hfactor⟩
      · rw [ite_eq_right hzero, ite_eq_right hzero]
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
        rw [whitneyClearColumnLowerAux, dite_eq_left htActive]
        by_cases hzero : B s.succ c = 0
        · rw [ite_eq_left hzero]
          exact ih
        · rw [ite_eq_right hzero]
          have hcs : c.val < s.castSucc.val := by
            dsimp [s]; lia
          constructor
          · intro i j hjc
            have hne : j ≠ s.castSucc := by rintro rfl; lia
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
      · rw [whitneyClearColumnLowerAux, dite_eq_right htActive]
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
        rw [whitneyClearColumnAux, dite_eq_left htActive]
        by_cases hzero : B s.succ c = 0
        · rw [ite_eq_left hzero]
          exact ih i j hij
        · rw [ite_eq_right hzero]
          by_cases his : i = s.succ
          · rw [his] at hij ⊢
            have htarget : B s.succ j = 0 := ih s.succ j hij
            have hpivot : B s.castSucc j = 0 := by
              apply ih
              dsimp [s] at hij ⊢; lia
            change whitneyEliminateAt B s c s.succ j = 0
            simp [whitneyEliminateAt, htarget, hpivot]
          · change whitneyEliminateAt B s c i j = 0
            simpa [whitneyEliminateAt, his] using ih i j hij
      · rw [whitneyClearColumnAux, dite_eq_right htActive]
        exact ih i j hij

private theorem whitneyClearColumnLowerAux_lowerTriangular {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (c : Fin (N + 1)) :
    ∀ t i j, i < j → whitneyClearColumnLowerAux A c t i j = 0 := by
  intro t
  induction t with
  | zero => exact fun _ _ hij ↦ Matrix.one_apply_ne (ne_of_lt hij)
  | succ t ih =>
      intro i j hij
      by_cases htActive : t < N - (c.val + 1)
      · let s : Fin N := ⟨N - (t + 1), by lia⟩
        let B := whitneyClearColumnAux A c t
        let L := whitneyClearColumnLowerAux A c t
        rw [whitneyClearColumnLowerAux, dite_eq_left htActive]
        by_cases hzero : B s.succ c = 0
        · rw [ite_eq_left hzero]
          exact ih i j hij
        · rw [ite_eq_right hzero]
          by_cases hj : j = s.castSucc
          · rw [hj] at hij ⊢
            rw [Matrix.mul_transvection_apply_same
              (i := s.succ) (j := s.castSucc)]
            rw [ih i s.castSucc hij]
            have his : i < s.succ := hij.trans s.castSucc_lt_succ
            rw [ih i s.succ his]; ring
          · rw [Matrix.mul_transvection_apply_of_ne
              (i := s.succ) (j := s.castSucc) i j hj]
            exact ih i j hij
      · rw [whitneyClearColumnLowerAux, dite_eq_right htActive]
        exact ih i j hij

/-- The explicit Whitney cycle `whitneyClearColumnAux * whitneyClearColumnLowerAux` with
`N - (c + 1)` stages has the properties stated in `exists_whitneyClearColumn`. -/
private theorem whitneyClearColumn_spec {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) (c : Fin (N + 1))
    (hprefix : ∀ r k, k.val < c.val → k.val + 1 < r.val → A r k = 0) :
    let C := whitneyClearColumnAux A c (N - (c.val + 1)) *
      whitneyClearColumnLowerAux A c (N - (c.val + 1))
    C.IsTotallyNonneg ∧ C.det ≠ 0 ∧ C.charpoly = A.charpoly ∧
        (C.submatrix Fin.succ Fin.succ).charpoly =
          (A.submatrix Fin.succ Fin.succ).charpoly ∧
        ((∀ i j, i.val + 1 < j.val → A i j = 0) →
          ∀ i j, i.val + 1 < j.val → C i j = 0) ∧
        ∀ r k, k.val ≤ c.val → k.val + 1 < r.val → C r k = 0 := by
  intro C
  let stages := N - (c.val + 1)
  let L := whitneyClearColumnLowerAux A c stages
  let B := whitneyClearColumnAux A c stages
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
      trailing_submatrix_mul_of_first_product_zero L B
        (fun i _ ↦ by rw [hLcolZero i, zero_mul])]
  have hCtrailing : C.submatrix Fin.succ Fin.succ =
      B.submatrix Fin.succ Fin.succ * L.submatrix Fin.succ Fin.succ := by
    change (B * L).submatrix Fin.succ Fin.succ = _
    exact trailing_submatrix_mul_of_first_product_zero B L
      (fun _ j ↦ by rw [hLrow j, mul_zero])
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
  refine ⟨hC, hCdet, hCchar, htrailingChar, hCupper, ?_⟩
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
        ∀ r k, k.val ≤ c.val → k.val + 1 < r.val → C r k = 0 :=
  ⟨_, whitneyClearColumn_spec A hA hdet c hprefix⟩

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
        exact ⟨A, hA, hdet, rfl, rfl, id, fun _ _ hk _ ↦ (by simp_all)⟩
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
        · exact fun hupper ↦ hCupper (hBupper hupper)
        · intro r k hkt hkr
          apply hCprefix r k
          · dsimp [c]
            lia
          · assumption
  obtain ⟨H, hH, hHdet, hHchar, hHtrailing, hHupper, hHprefix⟩ :=
    hsweep N le_rfl
  refine ⟨H, hH, hHdet, hHchar, hHtrailing, hHupper, ?_⟩
  intro r k hkr
  exact hHprefix r k (by have := r.isLt; lia) hkr

private theorem charpoly_transpose_submatrix_succ {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    (A.transpose.submatrix Fin.succ Fin.succ).charpoly =
      (A.submatrix Fin.succ Fin.succ).charpoly := by
  calc
    _ = ((A.submatrix Fin.succ Fin.succ).transpose).charpoly := by
      rw [Matrix.transpose_submatrix]
    _ = _ := Matrix.charpoly_transpose _

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
  have hHTdet : H.transpose.det ≠ 0 := by simpa using hHdet
  obtain ⟨T, hT, hTdet, hTchar, hTtrailing, hTupper, hTlower⟩ :=
    exists_whitneyUpperHessenberg H.transpose hHT hHTdet
  have hHTupper : ∀ i j, i.val + 1 < j.val → H.transpose i j = 0 :=
    fun i j hij => hHlower j i hij
  exact ⟨T, hT, hTdet,
    hTchar.trans ((Matrix.charpoly_transpose H).trans hHchar),
    hTtrailing.trans ((charpoly_transpose_submatrix_succ H).trans hHtrailing),
    hTlower, hTupper hHTupper⟩

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
      obtain ⟨hB, hBdet, hBtail⟩ := ih htN.le
      let s : Fin N := ⟨N - (t + 1), by lia⟩
      let B := whitneyClearFirstAux A t
      have hsval : s.succ.val = N - t := by simp [s]; lia
      have hBdetne : B.det ≠ 0 := by rw [hBdet]; exact hdet
      rw [whitneyClearFirstAux, dite_eq_left htN]
      dsimp only
      by_cases hzero : B s.succ 0 = 0
      · rw [ite_eq_left hzero]
        refine ⟨hB, hBdet, ?_⟩
        intro i hi
        by_cases his : i = s.succ
        · simpa [his] using hzero
        · apply hBtail i
          rw [← hsval]
          have hv : i.val ≠ s.succ.val := fun h ↦ his (Fin.ext h)
          lia
      · rw [ite_eq_right hzero]
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
          simp [whitneyEliminateFirst, whitneyEliminateAt, hpivot.ne']
        · have hit : s.succ < i := by
            apply Fin.lt_def.2
            rw [hsval]
            have hv : i.val ≠ s.succ.val := fun h ↦ his (Fin.ext h)
            lia
          change (whitneyEliminateFirst B s) i 0 = 0
          simp [whitneyEliminateFirst, whitneyEliminateAt, his, htail i hit]

private theorem whitneyClearLowerAux_spec {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hA : A.IsTotallyNonneg) (hdet : A.det ≠ 0) :
    ∀ t, t ≤ N →
      (whitneyClearLowerAux A t).IsTotallyNonneg ∧
      A = whitneyClearLowerAux A t * whitneyClearFirstAux A t := by
  intro t ht
  induction t with
  | zero =>
      have hone : (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ).IsTotallyNonneg := by simp
      exact ⟨hone, by simp [whitneyClearLowerAux, whitneyClearFirstAux]⟩
  | succ t ih =>
      have htN : t < N := by lia
      obtain ⟨hL, hfactor⟩ := ih htN.le
      obtain ⟨hB, hBdet, _⟩ :=
        whitneyClearFirstAux_spec A hA hdet t htN.le
      let s : Fin N := ⟨N - (t + 1), by lia⟩
      let B := whitneyClearFirstAux A t
      let L := whitneyClearLowerAux A t
      have hBdetne : B.det ≠ 0 := by rw [hBdet]; exact hdet
      have hclear : whitneyClearFirstAux A (t + 1) =
          if B s.succ 0 = 0 then B else whitneyEliminateFirst B s := by
        rw [whitneyClearFirstAux, dite_eq_left htN]
      have hlower : whitneyClearLowerAux A (t + 1) =
          if B s.succ 0 = 0 then L
          else L * Matrix.transvection s.succ s.castSucc
            (B s.succ 0 / B s.castSucc 0) := by
        rw [whitneyClearLowerAux, dite_eq_left htN]
      rw [hclear, hlower]
      by_cases hzero : B s.succ 0 = 0
      · rw [ite_eq_left hzero, ite_eq_left hzero]
        exact ⟨hL, hfactor⟩
      · rw [ite_eq_right hzero, ite_eq_right hzero]
        have htarget : 0 < B s.succ 0 :=
          lt_of_le_of_ne (hB.nonneg s.succ 0) (Ne.symm hzero)
        have hpivot : 0 < B s.castSucc 0 := by
          have hpred := hB.firstColumn_pred_pos_of_det_ne_zero
            hBdetne s.succ (by simp) htarget
          simpa using hpred
        have hratio : 0 ≤ B s.succ 0 / B s.castSucc 0 :=
          div_nonneg htarget.le hpivot.le
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
      constructor <;> intro i <;>
        simp [whitneyClearLowerAux, ne_of_lt (Fin.succ_pos i)]
  | succ t ih =>
      have htN : t < N := by lia
      obtain ⟨hcol, hrow⟩ := ih htN
      let s : Fin N := ⟨N - (t + 1), by lia⟩
      have hs : s.castSucc ≠ (0 : Fin (N + 1)) := by
        apply Fin.ne_of_gt
        dsimp [s]
        lia
      by_cases hzero : whitneyClearFirstAux A t s.succ 0 = 0
      · rw [whitneyClearLowerAux, dite_eq_left htN, ite_eq_left hzero]
        exact ⟨hcol, hrow⟩
      · rw [whitneyClearLowerAux, dite_eq_left htN, ite_eq_right hzero]
        let E := Matrix.transvection s.succ s.castSucc
          (whitneyClearFirstAux A t s.succ 0 /
            whitneyClearFirstAux A t s.castSucc 0)
        have hEcol : ∀ i : Fin N, E i.succ 0 = 0 := fun i ↦ by
          simp [E, Matrix.transvection, Matrix.single, hs]
        have hErow : ∀ j : Fin N, E 0 j.succ = 0 := fun j ↦ by
          simp [E, Matrix.transvection, Matrix.single, ne_of_lt (Fin.succ_pos j)]
        constructor
        · intro i
          change (whitneyClearLowerAux A t * E) i.succ 0 = 0
          simp only [Matrix.mul_apply]
          rw [Fin.sum_univ_succ, hcol i, zero_mul]
          simp [hEcol]
        · intro j
          change (whitneyClearLowerAux A t * E) 0 j.succ = 0
          simp only [Matrix.mul_apply]
          rw [Fin.sum_univ_succ, hErow j, mul_zero]
          simp [hrow]

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
  have hLcolZero : ∀ i : Fin (n + 1), L i.succ 0 = 0 := fun i ↦ by
    simpa [L] using hLcol i
  have hLrowZero : ∀ j : Fin (n + 1), L 0 j.succ = 0 := fun j ↦ by
    simpa [L] using hLrow j
  have hAtrailing : A.submatrix Fin.succ Fin.succ =
      L.submatrix Fin.succ Fin.succ * B.submatrix Fin.succ Fin.succ := by
    rw [hfactor,
      trailing_submatrix_mul_of_first_product_zero L B
        (fun i _ ↦ by rw [hLcolZero i, zero_mul])]
  have hCtrailing : C.submatrix Fin.succ Fin.succ =
      B.submatrix Fin.succ Fin.succ * L.submatrix Fin.succ Fin.succ := by
    change (B * L).submatrix Fin.succ Fin.succ = _
    exact trailing_submatrix_mul_of_first_product_zero B L
      (fun _ j ↦ by rw [hLrowZero j, mul_zero])
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
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]; simp [hzero]

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


end WhitneyElimination

end Matrix
