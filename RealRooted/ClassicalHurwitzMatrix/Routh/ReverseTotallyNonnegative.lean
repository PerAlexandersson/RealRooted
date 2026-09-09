import RealRooted.ClassicalHurwitzMatrix.Routh
import RealRooted.Mathlib.LinearAlgebra.Matrix.OscillatoryInterlacing.Core

/-!
# Reverse total nonnegativity for the Routh reduction

This file proves that total nonnegativity of a Routh-expanded Hurwitz matrix
descends to the original Hurwitz matrix when its initial coefficient `a 0` is
nonzero.  Total nonnegativity makes this pivot positive.  The proof performs a
finite sequence of Whitney eliminations and
then embeds each finite minor into a sufficiently large eliminated section.

The Whitney dependency is intentionally isolated here so that the lighter
forward Routh API does not import the oscillatory-matrix development.
-/

namespace Matrix

private noncomputable def routhEliminatePrefix {N : ℕ}
    (A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ) :
    ℕ → Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ
  | 0 => A
  | t + 1 =>
      if ht : t < N then
        whitneyEliminateAt (routhEliminatePrefix A t)
          ⟨2 * t + 1, by lia⟩ ⟨t + 1, by lia⟩
      else
        routhEliminatePrefix A t

private theorem routhEliminatePrefix_succ {N t : ℕ}
    (A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (ht : t < N) :
    routhEliminatePrefix A (t + 1) =
      whitneyEliminateAt (routhEliminatePrefix A t)
        ⟨2 * t + 1, by lia⟩ ⟨t + 1, by lia⟩ := by
  rw [routhEliminatePrefix]
  simp only [dif_pos ht]

private theorem routhExpand_hurwitz_eliminate_pair (c : ℝ) (a : ℕ → ℝ)
    (ha0 : a 0 ≠ 0) (k j : ℕ) :
    routhExpand c (hurwitz a) (2 * k + 2) j -
        (routhExpand c (hurwitz a) (2 * k + 2) (k + 1) /
          routhExpand c (hurwitz a) (2 * k + 1) (k + 1)) *
          routhExpand c (hurwitz a) (2 * k + 1) j =
      hurwitz a (2 * k + 3) j := by
  have htarget (l : ℕ) :
      routhExpand c (hurwitz a) (2 * k + 2) l =
        c * hurwitz a (2 * k + 2) l + hurwitz a (2 * k + 3) l := by
    simpa only [show 2 * k + 2 = 2 * (k + 1) by lia,
      show 2 * (k + 1) + 1 = 2 * k + 3 by lia] using
      routhExpand_even_apply c (hurwitz a) (k + 1) l
  have hsource (l : ℕ) :
      routhExpand c (hurwitz a) (2 * k + 1) l =
        hurwitz a (2 * k + 2) l :=
    routhExpand_odd_apply c (hurwitz a) k l
  have hpivot : hurwitz a (2 * k + 2) (k + 1) = a 0 := by
    rw [hurwitz_apply, if_pos (by lia)]
    congr 1
    lia
  have htargetPivot : hurwitz a (2 * k + 3) (k + 1) = 0 := by
    rw [hurwitz_apply, if_neg (by lia)]
  rw [htarget, htarget, hsource, hsource, hpivot, htargetPivot]
  field_simp [ha0]
  ring

private theorem routhExpand_hurwitz_eq_zero_of_two_mul_lt (c : ℝ)
    (a : ℕ → ℝ) {i j : ℕ} (hij : 2 * j < i) :
    routhExpand c (hurwitz a) i j = 0 := by
  rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hi : i = 2 * k := by lia
    rw [hi, routhExpand_even_apply]
    rw [hurwitz_apply_eq_zero_of_two_mul_lt a (by lia),
      hurwitz_apply_eq_zero_of_two_mul_lt a (by lia)]
    ring
  · have hi : i = 2 * k + 1 := by lia
    rw [hi, routhExpand_odd_apply]
    exact hurwitz_apply_eq_zero_of_two_mul_lt a (by lia)

private theorem routhEliminatePrefix_hurwitz_apply {N : ℕ} (c : ℝ)
    (a : ℕ → ℝ) (ha0 : a 0 ≠ 0) :
    ∀ t ≤ N, ∀ i j : Fin (2 * N + 1),
      routhEliminatePrefix
          ((routhExpand c (hurwitz a)).submatrix Fin.val Fin.val) t i j =
        if 0 < i.val ∧ i.val ≤ 2 * t then
          hurwitz a (i.val + 1) j.val
        else
          routhExpand c (hurwitz a) i.val j.val := by
  intro t ht
  induction t with
  | zero =>
      intro i j
      rw [routhEliminatePrefix]
      simp only [submatrix_apply]
      rw [if_neg (by lia)]
  | succ t ih =>
      have htN : t < N := by lia
      intro i j
      rw [routhEliminatePrefix_succ _ htN]
      by_cases hi : i.val = 2 * t + 2
      · have hiFin : i = (⟨2 * t + 2, by lia⟩ : Fin (2 * N + 1)) :=
          Fin.ext hi
        subst i
        rw [whitneyEliminateAt]
        rw [show (⟨2 * t + 2, by lia⟩ : Fin (2 * N + 1)) =
            (⟨2 * t + 1, by lia⟩ : Fin (2 * N)).succ by rfl,
          updateRow_self]
        rw [ih htN.le, ih htN.le, ih htN.le, ih htN.le]
        simp only [Fin.val_succ, Fin.val_castSucc]
        rw [if_neg (by lia), if_neg (by lia), if_neg (by lia),
          if_neg (by lia), if_pos (by lia)]
        simpa only [show 2 * t + 1 + 1 = 2 * t + 2 by lia,
          show 2 * t + 1 + 1 + 1 = 2 * t + 3 by lia] using
          routhExpand_hurwitz_eliminate_pair c a ha0 t j.val
      · have hiFin : i ≠ (⟨2 * t + 2, by lia⟩ : Fin (2 * N + 1)) := by
          intro h
          exact hi (Fin.ext_iff.mp h)
        have hiSucc : i ≠ (⟨2 * t + 1, by lia⟩ : Fin (2 * N)).succ := by
          intro h
          apply hi
          simpa using congrArg Fin.val h
        rw [whitneyEliminateAt, updateRow_ne hiSucc]
        rw [ih htN.le]
        by_cases hisource : i.val = 2 * t + 1
        · have hiodd : i.val = 2 * t + 1 := hisource
          rw [if_neg (by lia), if_pos (by lia)]
          rw [hiodd, routhExpand_odd_apply]
        · have hiff :
              (0 < i.val ∧ i.val ≤ 2 * (t + 1)) ↔
                (0 < i.val ∧ i.val ≤ 2 * t) := by
            constructor <;> intro h
            · constructor
              · exact h.1
              · lia
            · exact ⟨h.1, by lia⟩
          by_cases hold : 0 < i.val ∧ i.val ≤ 2 * t
          · rw [if_pos hold, if_pos (hiff.mpr hold)]
          · rw [if_neg hold, if_neg (fun hnew => hold (hiff.mp hnew))]

private theorem routhEliminatePrefix_hurwitz_isTotallyNonneg {N : ℕ}
    (c : ℝ) (a : ℕ → ℝ) (ha0 : 0 < a 0)
    (h : (routhExpand c (hurwitz a)).IsTotallyNonneg) :
    ∀ t ≤ N,
      (routhEliminatePrefix (N := N)
        ((routhExpand c (hurwitz a)).submatrix Fin.val Fin.val) t).IsTotallyNonneg := by
  intro t ht
  induction t with
  | zero =>
      exact h.submatrix Fin.val_strictMono Fin.val_strictMono
  | succ t ih =>
      have htN : t < N := by lia
      let A := routhEliminatePrefix (N := N)
        ((routhExpand c (hurwitz a)).submatrix Fin.val Fin.val) t
      let s : Fin (2 * N) := ⟨2 * t + 1, by lia⟩
      let p : Fin (2 * N + 1) := ⟨t + 1, by lia⟩
      have hpivot : 0 < A s.castSucc p := by
        dsimp only [A]
        rw [routhEliminatePrefix_hurwitz_apply c a ha0.ne' t htN.le]
        rw [if_neg (by simp [s])]
        change 0 < routhExpand c (hurwitz a) (2 * t + 1) (t + 1)
        rw [routhExpand_odd_apply, hurwitz_apply, if_pos (by lia)]
        rw [show 2 * (t + 1) - (2 * t + 2) = 0 by lia]
        exact ha0
      have htail : ∀ i, s.succ < i → A i p = 0 := by
        intro i hi
        have hiVal : 2 * t + 2 < i.val := by
          have hi' := Fin.lt_def.mp hi
          change 2 * t + 1 + 1 < i.val at hi'
          lia
        dsimp only [A]
        rw [routhEliminatePrefix_hurwitz_apply c a ha0.ne' t htN.le]
        rw [if_neg (by intro hcond; lia)]
        apply routhExpand_hurwitz_eq_zero_of_two_mul_lt
        change 2 * (t + 1) < i.val
        lia
      have hleft : ∀ i, s.castSucc ≤ i → ∀ j, j < p → A i j = 0 := by
        intro i hi j hj
        have hiVal : 2 * t + 1 ≤ i.val := by
          have hi' := Fin.le_def.mp hi
          change 2 * t + 1 ≤ i.val at hi'
          exact hi'
        have hjVal : j.val < t + 1 := by
          have hj' := Fin.lt_def.mp hj
          change j.val < t + 1 at hj'
          exact hj'
        dsimp only [A]
        rw [routhEliminatePrefix_hurwitz_apply c a ha0.ne' t htN.le]
        rw [if_neg (by intro hcond; lia)]
        apply routhExpand_hurwitz_eq_zero_of_two_mul_lt
        lia
      rw [routhEliminatePrefix_succ _ htN]
      exact ((ih htN.le).toRect.whitneyEliminateAt_nonneg
        s p hpivot htail hleft).toSquare

/-- Total nonnegativity of a Routh-expanded Hurwitz matrix descends through the
Routh row operation when the initial pivot is nonzero. -/
theorem IsTotallyNonneg.hurwitz_of_routhExpand
    {c : ℝ} {a : ℕ → ℝ}
    (h : (routhExpand c (hurwitz a)).IsTotallyNonneg)
    (ha0 : a 0 ≠ 0) : (hurwitz a).IsTotallyNonneg := by
  have ha0pos : 0 < a 0 := by
    have hnonneg := h.nonneg 1 1
    rw [show (1 : ℕ) = 2 * 0 + 1 by rfl, routhExpand_odd_apply,
      hurwitz_apply, if_pos (by lia)] at hnonneg
    simpa using lt_of_le_of_ne hnonneg ha0.symm
  intro n rows cols hrows hcols
  cases n with
  | zero => simp
  | succ q =>
      let N := max (rows (Fin.last q)) (cols (Fin.last q)) + 1
      let rows' : Fin (q + 1) → Fin (2 * N + 1) := fun i =>
        ⟨rows i + 1, by
          have hir : rows i ≤ rows (Fin.last q) :=
            hrows.monotone (Fin.le_last i)
          have hrmax : rows (Fin.last q) ≤
              max (rows (Fin.last q)) (cols (Fin.last q)) :=
            Nat.le_max_left _ _
          dsimp only [N]
          lia⟩
      let cols' : Fin (q + 1) → Fin (2 * N + 1) := fun j =>
        ⟨cols j + 1, by
          have hjc : cols j ≤ cols (Fin.last q) :=
            hcols.monotone (Fin.le_last j)
          have hcmax : cols (Fin.last q) ≤
              max (rows (Fin.last q)) (cols (Fin.last q)) :=
            Nat.le_max_right _ _
          dsimp only [N]
          lia⟩
      have hrows' : StrictMono rows' := by
        intro i j hij
        exact Nat.add_lt_add_right (hrows hij) 1
      have hcols' : StrictMono cols' := by
        intro i j hij
        exact Nat.add_lt_add_right (hcols hij) 1
      have hfinal :=
        routhEliminatePrefix_hurwitz_isTotallyNonneg c a ha0pos h N le_rfl
      have hminor := hfinal hrows' hcols'
      have hmatrix :
          (routhEliminatePrefix
              ((routhExpand c (hurwitz a)).submatrix Fin.val Fin.val) N).submatrix
              rows' cols' =
            (hurwitz a).submatrix rows cols := by
        ext i j
        simp only [submatrix_apply]
        rw [routhEliminatePrefix_hurwitz_apply c a ha0 N le_rfl]
        rw [if_pos (by
          have hir : rows i ≤ rows (Fin.last q) :=
            hrows.monotone (Fin.le_last i)
          have hrmax : rows (Fin.last q) ≤
              max (rows (Fin.last q)) (cols (Fin.last q)) :=
            Nat.le_max_left _ _
          simp only [rows', N]
          constructor
          · lia
          · lia)]
        simpa only [rows', cols', Fin.val_mk, Nat.add_assoc,
          Nat.reduceAdd] using hurwitz_add_two_add_one a (rows i) (cols j)
      rw [← hmatrix]
      exact hminor

open Polynomial
open RealRooted

/-- Full Hurwitz total nonnegativity is preserved by the canonical Routh
reduction when the eliminated odd constant coefficient is positive. -/
theorem IsTotallyNonneg.hurwitz_routhReducedPolynomial
    {c : ℝ} {odd even : ℝ[X]}
    (h : (hurwitz (oddEvenPolynomial odd even).coeff).IsTotallyNonneg)
    (hodd : 0 < odd.coeff 0)
    (h0 : even.coeff 0 = c * odd.coeff 0) :
    (hurwitz (routhReducedPolynomial c odd even).coeff).IsTotallyNonneg := by
  rw [hurwitz_oddEvenPolynomial_eq_routhExpand c odd even h0] at h
  apply h.hurwitz_of_routhExpand
  rw [routhReducedPolynomial, show (0 : ℕ) = 2 * 0 by rfl,
    coeff_oddEvenPolynomial_even]
  exact hodd.ne'

/-- Ratio-specialized full Hurwitz total nonnegativity for the canonical Routh
reduction. -/
theorem IsTotallyNonneg.hurwitz_routhReducedPolynomial_ratio
    {odd even : ℝ[X]}
    (h : (hurwitz (oddEvenPolynomial odd even).coeff).IsTotallyNonneg)
    (hodd : 0 < odd.coeff 0) :
    (hurwitz (routhReducedPolynomial
      (routhCoefficient odd even) odd even).coeff).IsTotallyNonneg := by
  exact h.hurwitz_routhReducedPolynomial hodd
    (routhCoefficient_mul_coeff_zero odd even hodd.ne')

end Matrix
