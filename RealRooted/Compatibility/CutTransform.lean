import RealRooted.Compatibility.Basic

/-!
# The finite P/Q cut transform

This module packages the prefix/strict-suffix transform used by terminal-state
recurrences.  It records only the exact algebra and boundary behavior; no
compatibility-preservation claim is made here.
-/

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted

/-- The inclusive left part of a finite cut. -/
def cutPrefix {R : Type*} [AddCommMonoid R] {m : ℕ}
    (P : Fin m → R) (j : Fin m) : R :=
  ∑ i : Fin m, if i ≤ j then P i else 0

/-- The strict right part of a finite cut. -/
def cutStrictSuffix {R : Type*} [AddCommMonoid R] {m : ℕ}
    (Q : Fin m → R) (j : Fin m) : R :=
  ∑ i : Fin m, if j < i then Q i else 0

/-- The unmarked output of the polynomial `P/Q` cut transform. -/
def cutTransformP {m : ℕ} (P Q : Fin m → ℝ[X]) (j : Fin m) : ℝ[X] :=
  cutPrefix P j + cutStrictSuffix Q j

/-- The marked output of the polynomial `P/Q` cut transform. -/
def cutTransformQ {m : ℕ} (P Q : Fin m → ℝ[X]) (j : Fin m) : ℝ[X] :=
  X * cutPrefix P j + cutStrictSuffix Q j

/-- The two cut outputs differ only by marking the inclusive prefix. -/
theorem cutTransformQ_sub_cutTransformP {m : ℕ}
    (P Q : Fin m → ℝ[X]) (j : Fin m) :
    cutTransformQ P Q j - cutTransformP P Q j =
      (X - 1) * cutPrefix P j := by
  unfold cutTransformP cutTransformQ
  ring

/-- The empty family has zero aggregate output. -/
@[simp]
theorem sum_cutTransformP_empty (P Q : Fin 0 → ℝ[X]) :
    (∑ j : Fin 0, cutTransformP P Q j) = 0 := by
  simp

/-- The empty family has zero marked aggregate output. -/
@[simp]
theorem sum_cutTransformQ_empty (P Q : Fin 0 → ℝ[X]) :
    (∑ j : Fin 0, cutTransformQ P Q j) = 0 := by
  simp

/-- The inclusive prefix at the first cut consists of its first entry. -/
@[simp]
theorem cutPrefix_zero {R : Type*} [AddCommMonoid R] {m : ℕ}
    (P : Fin (m + 1) → R) :
    cutPrefix P 0 = P 0 := by
  unfold cutPrefix
  rw [Fin.sum_univ_succ]
  simp

/-- The strict suffix at the first cut is the tail indexed by `Fin.succ`. -/
@[simp]
theorem cutStrictSuffix_zero {R : Type*} [AddCommMonoid R] {m : ℕ}
    (Q : Fin (m + 1) → R) :
    cutStrictSuffix Q 0 = ∑ i : Fin m, Q i.succ := by
  unfold cutStrictSuffix
  rw [Fin.sum_univ_succ]
  simp

theorem cutTransformP_zero {m : ℕ} (P Q : Fin (m + 1) → ℝ[X]) :
    cutTransformP P Q 0 = P 0 + ∑ i : Fin m, Q i.succ := by
  simp [cutTransformP]

theorem cutTransformQ_zero {m : ℕ} (P Q : Fin (m + 1) → ℝ[X]) :
    cutTransformQ P Q 0 = X * P 0 + ∑ i : Fin m, Q i.succ := by
  simp [cutTransformQ]

/-- At the last cut every entry belongs to the inclusive prefix. -/
@[simp]
theorem cutPrefix_last {R : Type*} [AddCommMonoid R] {m : ℕ}
    (P : Fin (m + 1) → R) :
    cutPrefix P (Fin.last m) = ∑ i : Fin (m + 1), P i := by
  apply Fintype.sum_congr
  intro i
  simp [Fin.le_last]

/-- The strict suffix at the last cut is empty. -/
@[simp]
theorem cutStrictSuffix_last {R : Type*} [AddCommMonoid R] {m : ℕ}
    (Q : Fin (m + 1) → R) :
    cutStrictSuffix Q (Fin.last m) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  simp [not_lt_of_ge (Fin.le_last i)]

theorem cutTransformP_last {m : ℕ} (P Q : Fin (m + 1) → ℝ[X]) :
    cutTransformP P Q (Fin.last m) = ∑ i : Fin (m + 1), P i := by
  simp [cutTransformP]

theorem cutTransformQ_last {m : ℕ} (P Q : Fin (m + 1) → ℝ[X]) :
    cutTransformQ P Q (Fin.last m) = X * ∑ i : Fin (m + 1), P i := by
  simp [cutTransformQ]

/-- A one-coordinate transform has no strict suffix. -/
@[simp]
theorem cutTransformP_one (P Q : Fin 1 → ℝ[X]) :
    cutTransformP P Q 0 = P 0 := by
  simpa using cutTransformP_zero (m := 0) P Q

/-- The marked one-coordinate output is `X` times its input. -/
@[simp]
theorem cutTransformQ_one (P Q : Fin 1 → ℝ[X]) :
    cutTransformQ P Q 0 = X * P 0 := by
  simpa using cutTransformQ_zero (m := 0) P Q

end RealRooted
