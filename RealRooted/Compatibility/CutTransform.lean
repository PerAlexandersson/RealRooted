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

/-- Ordered compatibility data adapted to the finite `P/Q` cut transform.

The `P` family is read in reverse order, the `Q` family in forward order,
and every `P` coordinate precedes every `Q` coordinate.  Diagonal instances
of the ordered fields also certify that every member splits. -/
structure OrderedCutCompatible {m : ℕ}
    (P Q : Fin m → ℝ[X]) : Prop where
  p_pos : ∀ i, HasPosLeadingCoeff (P i)
  p_nonneg : ∀ i, HasNonnegCoeffs (P i)
  q_pos : ∀ i, HasPosLeadingCoeff (Q i)
  q_nonneg : ∀ i, HasNonnegCoeffs (Q i)
  pp_reverse : ∀ ⦃i j⦄, i ≤ j → Compatible (P j) (P i)
  xpp_reverse : ∀ ⦃i j⦄, i ≤ j → Compatible (X * P j) (P i)
  pq : ∀ i j, Compatible (P i) (Q j)
  xpq : ∀ i j, Compatible (X * P i) (Q j)
  qq_forward : ∀ ⦃i j⦄, i ≤ j → Compatible (Q i) (Q j)
  xqq_forward : ∀ ⦃i j⦄, i ≤ j → Compatible (X * Q i) (Q j)

namespace OrderedCutCompatible

/-- Every `P` member is nonzero and splits. -/
theorem p_splits {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) (i : Fin m) :
    P i ≠ 0 ∧ (P i).Splits :=
  (h.pp_reverse le_rfl).isRealRooted_left (h.p_pos i)

/-- Every `Q` member is nonzero and splits. -/
theorem q_splits {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) (i : Fin m) :
    Q i ≠ 0 ∧ (Q i).Splits :=
  (h.qq_forward le_rfl).isRealRooted_left (h.q_pos i)

/-- The commuted forward `P/P` relation. -/
theorem pp_forward {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) ⦃i j : Fin m⦄ (hij : i ≤ j) :
    Compatible (P i) (P j) :=
  (h.pp_reverse hij).comm

/-- The commuted reverse `Q/Q` relation. -/
theorem qq_reverse {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) ⦃i j : Fin m⦄ (hij : i ≤ j) :
    Compatible (Q j) (Q i) :=
  (h.qq_forward hij).comm

/-- Multiplying both members preserves the reverse `P/P` relation. -/
theorem xp_xp_reverse {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) ⦃i j : Fin m⦄ (hij : i ≤ j) :
    Compatible (X * P j) (X * P i) :=
  (h.pp_reverse hij).X_mul

/-- Multiplying both members preserves the forward `Q/Q` relation. -/
theorem xq_xq_forward {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) ⦃i j : Fin m⦄ (hij : i ≤ j) :
    Compatible (X * Q i) (X * Q j) :=
  (h.qq_forward hij).X_mul

/-- The ordered invariant is vacuous for an empty family. -/
theorem empty (P Q : Fin 0 → ℝ[X]) : OrderedCutCompatible P Q where
  p_pos i := Fin.elim0 i
  p_nonneg i := Fin.elim0 i
  q_pos i := Fin.elim0 i
  q_nonneg i := Fin.elim0 i
  pp_reverse {i} := Fin.elim0 i
  xpp_reverse {i} := Fin.elim0 i
  pq i := Fin.elim0 i
  xpq i := Fin.elim0 i
  qq_forward {i} := Fin.elim0 i
  xqq_forward {i} := Fin.elim0 i

/-- For a singleton family, only the two cross relations are genuine input;
the diagonal ordered relations follow from endpoint splitness. -/
theorem singleton (P Q : Fin 1 → ℝ[X])
    (hp_pos : HasPosLeadingCoeff (P 0))
    (hp_nonneg : HasNonnegCoeffs (P 0))
    (hq_pos : HasPosLeadingCoeff (Q 0))
    (hq_nonneg : HasNonnegCoeffs (Q 0))
    (hpq : Compatible (P 0) (Q 0))
    (hxpq : Compatible (X * P 0) (Q 0)) :
    OrderedCutCompatible P Q := by
  have hp_splits := hpq.isRealRooted_left hp_pos
  have hq_splits := hpq.isRealRooted_right hq_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [Fin.eq_zero i] using hp_pos
  · intro i
    simpa [Fin.eq_zero i] using hp_nonneg
  · intro i
    simpa [Fin.eq_zero i] using hq_pos
  · intro i
    simpa [Fin.eq_zero i] using hq_nonneg
  · intro i j _
    simpa [Fin.eq_zero i, Fin.eq_zero j] using
      Compatible.self_of_splits hp_splits.2
  · intro i j _
    simpa [Fin.eq_zero i, Fin.eq_zero j] using
      (Compatible.self_X_mul_of_splits hp_splits.2).comm
  · intro i j
    simpa [Fin.eq_zero i, Fin.eq_zero j] using hpq
  · intro i j
    simpa [Fin.eq_zero i, Fin.eq_zero j] using hxpq
  · intro i j _
    simpa [Fin.eq_zero i, Fin.eq_zero j] using
      Compatible.self_of_splits hq_splits.2
  · intro i j _
    simpa [Fin.eq_zero i, Fin.eq_zero j] using
      (Compatible.self_X_mul_of_splits hq_splits.2).comm

end OrderedCutCompatible

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
