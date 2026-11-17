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
public import RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Reduction
import all RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Reduction
import RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Elimination
import all RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Elimination
import RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Border
import all RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Border

/-!
# Positive adjacent entries in Whitney reduction

Diagonal positivity, primitivity, and Whitney reductions that preserve
positive adjacent entries.
-/

public section

namespace Matrix

open scoped BigOperators

section WhitneyElimination

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
  have hrows : StrictMono rows := strictMono_pair hij
  have hcols : StrictMono cols := strictMono_pair hi0
  have hminor := hA hrows hcols
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, rows, cols,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hminor
  have hj0 : 0 ≤ A j 0 := hA.nonneg j 0
  rw [hi, zero_mul, zero_sub] at hminor; nlinarith [hdiag i]

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
    have hlt : (i.pred hi0).castSucc < i :=
      Fin.castSucc_pred_lt hi0
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
  have hpair : StrictMono pair := strictMono_pair i.castSucc_lt_succ
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
      exact ⟨fun _ _ hij ↦ Matrix.one_apply_ne (ne_of_lt hij), Matrix.one_apply_eq⟩
  | succ t ih =>
      by_cases htActive : t < N
      · let s : Fin N := ⟨N - (t + 1), by lia⟩
        let B := whitneyClearFirstAux A t
        let L := whitneyClearLowerAux A t
        rw [whitneyClearLowerAux, dite_eq_left htActive]
        by_cases hzero : B s.succ 0 = 0
        · rw [ite_eq_left hzero]
          exact ih
        · rw [ite_eq_right hzero]
          constructor
          · intro i j hij
            by_cases hj : j = s.castSucc
            · rw [hj] at hij ⊢
              rw [Matrix.mul_transvection_apply_same
                (i := s.succ) (j := s.castSucc)]
              rw [ih.1 i s.castSucc hij]
              have his : i < s.succ := hij.trans s.castSucc_lt_succ
              rw [ih.1 i s.succ his]; ring
            · rw [Matrix.mul_transvection_apply_of_ne
                (i := s.succ) (j := s.castSucc) i j hj]
              exact ih.1 i j hij
          · intro i
            by_cases hi : i = s.castSucc
            · subst i
              rw [Matrix.mul_transvection_apply_same
                (i := s.succ) (j := s.castSucc)]
              rw [ih.2 s.castSucc, ih.1 s.castSucc s.succ
                s.castSucc_lt_succ]; ring
            · rw [Matrix.mul_transvection_apply_of_ne
                (i := s.succ) (j := s.castSucc) i i hi]
              exact ih.2 i
      · rw [whitneyClearLowerAux, dite_eq_right htActive]
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
      have hterm : 0 < L i i * B i i := by simpa [hLdiag] using hBdiag i
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
  have hrows : StrictMono rows := strictMono_pair hij
  have hcols : StrictMono cols := strictMono_pair hjk
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
    · have hsi : s.castSucc < i.castSucc := by simp [hi]
      have hik : i.castSucc < i.succ := i.castSucc_lt_succ
      by_cases hzero : D i.castSucc i.succ = 0
      · have hfar : D s.castSucc i.succ = 0 :=
          hD.northeast_zero_of_southeast_zero hsi hik hzero
            (hdiag i.castSucc)
        have hzero' : D s.succ i.succ = 0 := by simpa [hi] using hzero
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
        dite_eq_left htActive, dite_eq_left htActive]
      dsimp only
      by_cases hzero : B s.succ c = 0
      · rw [ite_eq_left hzero, ite_eq_left hzero]
        exact ih htActive.le
      · rw [ite_eq_right hzero, ite_eq_right hzero]
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
          dsimp [s]; lia
        have hpivot : 0 < B s.castSucc c := by
          have hpred := hB.column_pred_pos_of_det_ne_zero hBdetne c s.succ
            hsc hBprefix htarget
          simpa using hpred
        have hratio : 0 ≤ ratio := div_nonneg htarget.le hpivot.le
        obtain ⟨hB', hB'det, _, _⟩ :=
          whitneyClearColumnAux_spec A hA hdet c hprefix (t + 1) ht
        have hclear : whitneyClearColumnAux A c (t + 1) = B' := by
          rw [whitneyClearColumnAux, dite_eq_left htActive]
          dsimp only
          rw [ite_eq_right hzero]
        have hB'TN : B'.IsTotallyNonneg := by simpa [hclear] using hB'
        have hB'detEq : B'.det = A.det := by simpa [hclear] using hB'det
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
          simpa [hrotate] using hold.1
        have hleftSub : ∀ i : Fin N, 0 < (E * D) i.succ i.castSucc := by
          simpa [hrotate] using hold.2
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
  obtain ⟨hC, hCdet, hCchar, htrailingChar, hCupper, hCprefix⟩ :=
    whitneyClearColumn_spec A hA hdet c hprefix
  exact ⟨_, hC, hCdet, hCchar, htrailingChar, hCupper, hCprefix,
    whitneyClearColumnCycle_adjacent_pos A hA hdet c hprefix hsuper hsub _ le_rfl⟩

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
        exact ⟨A, hA, hdet, rfl, rfl, id, fun _ _ hk _ ↦ (by simp_all),
          hsuper, hsub⟩
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
        · exact fun hupper ↦ hCupper (hBupper hupper)
        · intro r k hkt hkr
          apply hCprefix r k
          · dsimp [c]
            lia
          · assumption
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
  have hHTdet : H.transpose.det ≠ 0 := by simpa using hHdet
  have hHTsuper : ∀ i : Fin N, 0 < H.transpose i.castSucc i.succ :=
    hHsub
  have hHTsub : ∀ i : Fin N, 0 < H.transpose i.succ i.castSucc :=
    hHsuper
  obtain ⟨T, hT, hTdet, hTchar, hTtrailing, hTupper, hTlower,
      hTsuper, hTsub⟩ :=
    exists_whitneyUpperHessenberg_adjacent_pos H.transpose hHT hHTdet
      hHTsuper hHTsub
  have hHTupper : ∀ i j, i.val + 1 < j.val → H.transpose i j = 0 :=
    fun i j hij => hHlower j i hij
  exact ⟨T, hT, hTdet,
    hTchar.trans ((Matrix.charpoly_transpose H).trans hHchar),
    hTtrailing.trans ((charpoly_transpose_submatrix_succ H).trans hHtrailing),
    hTlower, hTupper hHTupper, hTsuper, hTsub⟩

end Matrix
