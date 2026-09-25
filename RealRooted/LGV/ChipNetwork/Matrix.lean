/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import RealRooted.LGV.ChipNetwork.Paths
import RealRooted.LGV.PathMatrix

/-!
# Matrix entries of finite lower-bidiagonal chip networks

This file identifies a single chip stage with its lower-bidiagonal transfer
matrix.  Longer word and interval identities are built from this local bridge.
-/

namespace RealRooted
namespace LGV
namespace ChipNetwork

open Quiver

noncomputable section

/-- The transfer matrix of one stage in a finite chip strip. -/
def chipMatrix {R : Type*} [Zero R]
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R) (s : Fin S) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  fun i j ↦
    if i = j then diagonal s i
    else if hsub : i.val = j.val + 1 then
      subdiagonal s ⟨j.val, by lia⟩
    else 0

@[simp]
theorem chipMatrix_apply {R : Type*} [Zero R]
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R) (s : Fin S)
    (i j : Fin (N + 1)) :
    chipMatrix diagonal subdiagonal s i j =
      if i = j then diagonal s i
      else if hsub : i.val = j.val + 1 then
        subdiagonal s ⟨j.val, by lia⟩
      else 0 := by
  rfl

/-- The weighted arrow sum across one stage is the corresponding chip-matrix
entry. -/
theorem edgeSumMatrix_apply_stage {R : Type*} [Semiring R]
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R) (s : Fin S)
    (i j : Fin (N + 1)) :
    Quiver.Path.edgeSumMatrix (edgeWeight diagonal subdiagonal)
        (s.castSucc, i) (s.succ, j) =
      chipMatrix diagonal subdiagonal s i j := by
  classical
  rw [Quiver.Path.edgeSumMatrix, chipMatrix_apply]
  change (∑ e : Arrow S N (s.castSucc, i) (s.succ, j),
      edgeWeight diagonal subdiagonal e) = _
  by_cases hij : i = j
  · subst j
    simp only
    let _ : Unique (Arrow S N (s.castSucc, i) (s.succ, i)) :=
      { default := stay s i
        uniq := fun _ ↦ Subsingleton.elim _ _ }
    rw [Fintype.sum_unique]
    rfl
  · simp only [hij]
    by_cases hsub : i.val = j.val + 1
    · simp only [hsub]
      have hjlt : j.val < N := by
        have hi := i.isLt
        lia
      let lower : Fin N := j.castLT hjlt
      have hi : i = lower.succ := Fin.ext hsub
      subst i
      let _ : Unique
          (Arrow S N (s.castSucc, lower.succ) (s.succ, j)) :=
        { default := drop s lower
          uniq := fun _ ↦ Subsingleton.elim _ _ }
      rw [Fintype.sum_unique]
      rfl
    · simp only [hsub]
      let _ : IsEmpty
          (Arrow S N (s.castSucc, i) (s.succ, j)) := ⟨by
        intro e
        rcases e with e | e
        · rcases e with ⟨⟨stage, level⟩, hv, hw⟩
          apply hij
          have hsource := congrArg Prod.snd hv
          have htarget := congrArg Prod.snd hw
          exact hsource.trans htarget.symm
        · rcases e with ⟨⟨stage, level⟩, hv, hw⟩
          apply hsub
          have hsource := congrArg (fun x ↦ x.2.val) hv
          have htarget := congrArg (fun x ↦ x.2.val) hw
          change i.val = level.val + 1 at hsource
          change j.val = level.val at htarget
          lia⟩
      simp

/-- The transfer matrix at a natural-number stage, extended by zero outside
the finite strip. -/
def chipMatrixNat {R : Type*} [Zero R]
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R) (s : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  if hs : s < S then chipMatrix diagonal subdiagonal ⟨s, hs⟩ else 0

/-- Ordered transfer product for `n` consecutive stages beginning at `a`. -/
def intervalProduct {R : Type*} [Semiring R]
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R) (a : ℕ) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) R
  | 0 => 1
  | n + 1 => intervalProduct diagonal subdiagonal a n *
      chipMatrixNat diagonal subdiagonal (a + n)

@[simp]
theorem intervalProduct_zero {R : Type*} [Semiring R]
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R) (a : ℕ) :
    intervalProduct diagonal subdiagonal a 0 = 1 :=
  rfl

theorem intervalProduct_succ {R : Type*} [Semiring R]
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R) (a n : ℕ) :
    intervalProduct diagonal subdiagonal a (n + 1) =
      intervalProduct diagonal subdiagonal a n *
        chipMatrixNat diagonal subdiagonal (a + n) :=
  rfl

/-- The full edge-sum matrix has a nonzero block only between consecutive
stages, where that block is the corresponding chip matrix. -/
theorem edgeSumMatrix_apply {R : Type*} [Semiring R]
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R)
    (a b : Fin (S + 1)) (i j : Fin (N + 1)) :
    Quiver.Path.edgeSumMatrix (edgeWeight diagonal subdiagonal)
        (a, i) (b, j) =
      if b.val = a.val + 1 then
        chipMatrixNat diagonal subdiagonal a.val i j
      else 0 := by
  classical
  by_cases hab : b.val = a.val + 1
  · rw [ite_eq_left hab]
    have ha : a.val < S := by
      have hb := b.isLt
      lia
    let s : Fin S := ⟨a.val, ha⟩
    have hasa : s.castSucc = a := Fin.ext rfl
    have hsb : s.succ = b := Fin.ext (by simpa [s] using hab.symm)
    calc
      Quiver.Path.edgeSumMatrix (edgeWeight diagonal subdiagonal)
          (a, i) (b, j) =
          Quiver.Path.edgeSumMatrix (edgeWeight diagonal subdiagonal)
            (s.castSucc, i) (s.succ, j) := by rw [hasa, hsb]
      _ = chipMatrix diagonal subdiagonal s i j :=
        edgeSumMatrix_apply_stage diagonal subdiagonal s i j
      _ = chipMatrixNat diagonal subdiagonal a.val i j := by
        simp [chipMatrixNat, s, ha]
  · rw [ite_eq_right hab, Quiver.Path.edgeSumMatrix]
    change (∑ e : Arrow S N (a, i) (b, j),
      edgeWeight diagonal subdiagonal e) = 0
    let _ : IsEmpty (Arrow S N (a, i) (b, j)) := ⟨by
      intro e
      apply hab
      exact arrow_stage_succ e⟩
    simp

/-- Powers of the full edge-sum matrix are the ordered products of their
successive chip blocks. -/
theorem edgeSumMatrix_pow_apply {R : Type*} [Semiring R]
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R)
    (a b : Fin (S + 1)) (i j : Fin (N + 1)) (n : ℕ)
    (hbound : a.val + n ≤ S) :
    (Quiver.Path.edgeSumMatrix (edgeWeight diagonal subdiagonal) ^ n)
        (a, i) (b, j) =
      if b.val = a.val + n then
        intervalProduct diagonal subdiagonal a.val n i j
      else 0 := by
  classical
  induction n generalizing b j with
  | zero =>
      simp only [pow_zero, Matrix.one_apply, Nat.add_zero]
      by_cases hab : b = a
      · subst b
        by_cases hij : i = j
        · subst j
          simp [intervalProduct]
        · have hpair : (a, i) ≠ (a, j) := fun h ↦
            hij (congrArg Prod.snd h)
          rw [ite_eq_right hpair, ite_eq_left rfl, intervalProduct_zero,
            Matrix.one_apply, ite_eq_right hij]
      · have hval : b.val ≠ a.val := fun h ↦ hab (Fin.ext h)
        have hpair : (a, i) ≠ (b, j) := fun h ↦
          hab (congrArg Prod.fst h).symm
        rw [ite_eq_right hpair, ite_eq_right hval]
  | succ n ih =>
      have hprev : a.val + n ≤ S := by lia
      let c : Fin (S + 1) := ⟨a.val + n, by lia⟩
      rw [pow_succ, Matrix.mul_apply]
      simp_rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single c]
      · simp_rw [ih c _ hprev, edgeSumMatrix_apply]
        simp only [c]
        by_cases hb : b.val = a.val + (n + 1)
        · rw [ite_eq_left hb]
          have hc : b.val = c.val + 1 := by simpa [c, Nat.add_assoc] using hb
          simp only [hc, ite_eq_left]
          rw [intervalProduct_succ, Matrix.mul_apply]
          congr 1
          funext k
          have hnS : a.val + n < S := by lia
          simp [chipMatrixNat, c, hnS]
        · rw [ite_eq_right hb]
          apply Finset.sum_eq_zero
          intro k _hk
          simp [hb, Nat.add_assoc]
      · intro c' _hc' hne
        have hval : c'.val ≠ a.val + n := by
          intro heq
          exact hne (Fin.ext (by simpa [c] using heq))
        simp [ih c' _ hprev, hval]
      · simp

/-- The finite total weight of all chip paths between two vertices. -/
def pathWeightSum {R : Type*} [Semiring R]
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R)
    (a b : Fin (S + 1)) (i j : Fin (N + 1)) : R := by
  let _ := Quiver.Path.fintypeOfRank (stageRank S N) stageRank_decreases
    (a, i) (b, j)
  exact ∑ p : Quiver.Path (a, i) (b, j),
    Quiver.Path.weight (edgeWeight diagonal subdiagonal) p

/-- The total weight of all paths across an interval is the corresponding
entry of the ordered chip product. -/
theorem pathWeightSum_eq_intervalProduct {R : Type*} [Semiring R]
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R)
    (a b : Fin (S + 1)) (i j : Fin (N + 1)) (n : ℕ)
    (hstage : b.val = a.val + n) :
    pathWeightSum diagonal subdiagonal a b i j =
      intervalProduct diagonal subdiagonal a.val n i j := by
  classical
  let _ := Quiver.Path.fintypeOfRank (stageRank S N) stageRank_decreases
    (a, i) (b, j)
  unfold pathWeightSum
  calc
    (∑ p : Quiver.Path (a, i) (b, j),
        Quiver.Path.weight (edgeWeight diagonal subdiagonal) p) =
        ∑ p : Quiver.Path.ExactLength (a, i) (b, j) n,
          Quiver.Path.weight (edgeWeight diagonal subdiagonal) p.1 := by
      symm
      refine Fintype.sum_equiv
        (equivExactLengthOfStageEq (a, i) (b, j) n hstage).symm _ _ ?_
      rintro ⟨p, hp⟩
      rfl
    _ = (Quiver.Path.edgeSumMatrix (edgeWeight diagonal subdiagonal) ^ n)
        (a, i) (b, j) :=
      Quiver.Path.sum_weight_exactLength_eq_edgeSumMatrix_pow
        (edgeWeight diagonal subdiagonal) (a, i) (b, j) n
    _ = intervalProduct diagonal subdiagonal a.val n i j := by
      rw [edgeSumMatrix_pow_apply diagonal subdiagonal a b i j n (by
        have hb := b.isLt
        lia), ite_eq_left hstage]

/-- There are no weighted chip paths to an earlier stage. -/
theorem pathWeightSum_eq_zero_of_stage_lt {R : Type*} [Semiring R]
    (diagonal : Fin S → Fin (N + 1) → R)
    (subdiagonal : Fin S → Fin N → R)
    (a b : Fin (S + 1)) (i j : Fin (N + 1))
    (hstage : b.val < a.val) :
    pathWeightSum diagonal subdiagonal a b i j = 0 := by
  classical
  unfold pathWeightSum
  let _ : IsEmpty (Quiver.Path (a, i) (b, j)) :=
    ⟨fun p ↦ not_nonempty_path_of_stage_lt
      (v := (a, i)) (w := (b, j)) (by simpa [stage] using hstage) ⟨p⟩⟩
  simp

end

end ChipNetwork
end LGV
end RealRooted
