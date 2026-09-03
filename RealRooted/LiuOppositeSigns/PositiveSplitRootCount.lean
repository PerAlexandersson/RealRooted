import RealRooted.LiuOppositeSigns.RootDeletion

/-!
# Positive-split root-count pairs

This module packages positive-leading split polynomial pairs with Liu-compatible
root counts. It also contains their degree estimates and the transport of this
package across common-root deletion.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace LiuOppositeSigns

structure PositiveSplitRootCountPair (p q : ℝ[X]) : Prop where
  left_pos : HasPosLeadingCoeff p
  right_pos : HasPosLeadingCoeff q
  left_splits : p.Splits
  right_splits : q.Splits
  count : RootCountCompatible p q

namespace PositiveSplitRootCountPair

theorem comp_X_add_C {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q) (r : ℝ) :
    PositiveSplitRootCountPair (p.comp (X + C r)) (q.comp (X + C r)) :=
  ⟨h.left_pos.comp_X_add_C r, h.right_pos.comp_X_add_C r,
    (isRealRooted_comp_X_add_C h.left_pos.ne_zero h.left_splits r).2,
    (isRealRooted_comp_X_add_C h.right_pos.ne_zero h.right_splits r).2,
    h.count.comp_X_add_C r⟩

theorem symm {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q) :
    PositiveSplitRootCountPair q p :=
  ⟨h.right_pos, h.left_pos, h.right_splits, h.left_splits, h.count.symm⟩

theorem of_rootCountAbove_bounds_of_nonRoot {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hbound : ∀ x : ℝ, ¬ p.IsRoot x → ¬ q.IsRoot x →
      ((p.roots.filter (x < ·)).card : ℤ) -
          (q.roots.filter (x < ·)).card ≤ 1 ∧
        ((q.roots.filter (x < ·)).card : ℤ) -
          (p.roots.filter (x < ·)).card ≤ 1) :
    PositiveSplitRootCountPair p q :=
  ⟨hp_pos, hq_pos, hp_splits, hq_splits,
    RootCountCompatible.of_rootCountAbove_bounds_of_nonRoot
      hp_pos.ne_zero hq_pos.ne_zero hbound⟩

theorem of_natDegree_le_one {p q : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hpdeg : p.natDegree ≤ 1) (hqdeg : q.natDegree ≤ 1) :
    PositiveSplitRootCountPair p q :=
  ⟨hp_pos, hq_pos, hp_splits, hq_splits,
    RootCountCompatible.of_natDegree_le_one hp_splits hq_splits hpdeg hqdeg⟩

theorem natDegree_abs_sub_le_one {p q : ℝ[X]}
    (h : PositiveSplitRootCountPair p q) :
    |((p.natDegree : ℤ) - (q.natDegree : ℤ))| ≤ 1 :=
  h.count.natDegree_abs_sub_le_one h.left_splits h.right_splits

/-- The x-subtraction pencil has degree at most one more than the left endpoint
polynomial under Liu's root-count-compatible positive split hypotheses. -/
theorem natDegree_X_mul_sub_C_mul_le_left_natDegree_add_one {p q : ℝ[X]}
    (h : PositiveSplitRootCountPair p q) (μ : ℝ) :
    (X * p - C μ * q).natDegree ≤ p.natDegree + 1 := by
  have hleft : (X * p).natDegree ≤ p.natDegree + 1 := by
    rw [Polynomial.natDegree_X_mul h.left_pos.ne_zero]
  have hq_le : q.natDegree ≤ p.natDegree + 1 := by
    have hgap := h.natDegree_abs_sub_le_one
    rw [abs_le] at hgap
    have hq_le_int : (q.natDegree : ℤ) ≤ (p.natDegree : ℤ) + 1 := by linarith
    exact_mod_cast hq_le_int
  have hright : (C μ * q).natDegree ≤ p.natDegree + 1 :=
    (Polynomial.natDegree_C_mul_le μ q).trans hq_le
  simpa using Polynomial.natDegree_sub_le_of_le hleft hright

/-- In the right-successor case, the x-subtraction pencil has degree at most
the right endpoint degree. -/
theorem natDegree_X_mul_sub_C_mul_le_right_natDegree_of_right_natDegree_eq_left_add_one
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q)
    (hdeg : q.natDegree = p.natDegree + 1) (μ : ℝ) :
    (X * p - C μ * q).natDegree ≤ q.natDegree := by
  have hleft : (X * p).natDegree ≤ q.natDegree := by
    rw [Polynomial.natDegree_X_mul h.left_pos.ne_zero, hdeg]
  have hright : (C μ * q).natDegree ≤ q.natDegree :=
    Polynomial.natDegree_C_mul_le μ q
  simpa using Polynomial.natDegree_sub_le_of_le hleft hright

/-- Top coefficient of the x-subtraction pencil in the right-successor degree
case. -/
theorem coeff_X_mul_sub_C_mul_right_natDegree_of_right_natDegree_eq_left_add_one
    {p q : ℝ[X]} (hdeg : q.natDegree = p.natDegree + 1) (μ : ℝ) :
    (X * p - C μ * q).coeff q.natDegree =
      p.leadingCoeff - μ * q.leadingCoeff := by
  have hX : (X * p).coeff q.natDegree = p.leadingCoeff := by
    rw [hdeg, coeff_X_mul]
    rw [coeff_natDegree]
  have hC : (C μ * q).coeff q.natDegree = μ * q.leadingCoeff := by
    rw [coeff_C_mul, coeff_natDegree]
  rw [coeff_sub, hX, hC]

/-- In the right-successor case, non-cancellation of the top coefficient keeps
the x-subtraction pencil at the right endpoint degree. -/
theorem natDegree_X_mul_sub_C_mul_eq_right_natDegree_of_right_natDegree_eq_left_add_one
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q)
    (hdeg : q.natDegree = p.natDegree + 1) {μ : ℝ}
    (hcoeff : p.leadingCoeff - μ * q.leadingCoeff ≠ 0) :
    (X * p - C μ * q).natDegree = q.natDegree := by
  refine le_antisymm
    (h.natDegree_X_mul_sub_C_mul_le_right_natDegree_of_right_natDegree_eq_left_add_one
      hdeg μ) ?_
  apply le_natDegree_of_ne_zero
  simpa [coeff_X_mul_sub_C_mul_right_natDegree_of_right_natDegree_eq_left_add_one
    hdeg μ] using hcoeff

/-- Leading coefficient of the x-subtraction pencil in the non-cancelling
right-successor case. -/
theorem leadingCoeff_X_mul_sub_C_mul_of_right_natDegree_eq_left_add_one
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q)
    (hdeg : q.natDegree = p.natDegree + 1) {μ : ℝ}
    (hcoeff : p.leadingCoeff - μ * q.leadingCoeff ≠ 0) :
    (X * p - C μ * q).leadingCoeff =
      p.leadingCoeff - μ * q.leadingCoeff := by
  rw [leadingCoeff,
    h.natDegree_X_mul_sub_C_mul_eq_right_natDegree_of_right_natDegree_eq_left_add_one
      hdeg hcoeff,
    coeff_X_mul_sub_C_mul_right_natDegree_of_right_natDegree_eq_left_add_one
      hdeg μ]

/-- Positive top coefficient gives positive leading coefficient for the
right-successor x-subtraction pencil. -/
theorem hasPosLeadingCoeff_X_mul_sub_C_mul_of_right_natDegree_eq_left_add_one
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q)
    (hdeg : q.natDegree = p.natDegree + 1) {μ : ℝ}
    (hcoeff : 0 < p.leadingCoeff - μ * q.leadingCoeff) :
    HasPosLeadingCoeff (X * p - C μ * q) := by
  unfold HasPosLeadingCoeff
  rw [h.leadingCoeff_X_mul_sub_C_mul_of_right_natDegree_eq_left_add_one
    hdeg (ne_of_gt hcoeff)]
  exact hcoeff

/-- Negative top coefficient gives positive leading coefficient after negating
the right-successor x-subtraction pencil. -/
theorem hasPosLeadingCoeff_neg_X_mul_sub_C_mul_of_right_natDegree_eq_left_add_one
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q)
    (hdeg : q.natDegree = p.natDegree + 1) {μ : ℝ}
    (hcoeff : p.leadingCoeff - μ * q.leadingCoeff < 0) :
    HasPosLeadingCoeff (-(X * p - C μ * q)) := by
  exact hasPosLeadingCoeff_neg <|
    by
      rw [h.leadingCoeff_X_mul_sub_C_mul_of_right_natDegree_eq_left_add_one
        hdeg (ne_of_lt hcoeff)]
      exact hcoeff

/-- In the right-successor case, cancellation of the top coefficient drops the
x-subtraction pencil below the right endpoint degree. -/
theorem natDegree_X_mul_sub_C_mul_lt_right_natDegree_of_right_natDegree_eq_left_add_one
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q)
    (hdeg : q.natDegree = p.natDegree + 1) {μ : ℝ}
    (hcoeff : p.leadingCoeff - μ * q.leadingCoeff = 0) :
    (X * p - C μ * q).natDegree < q.natDegree := by
  have hle :=
    h.natDegree_X_mul_sub_C_mul_le_right_natDegree_of_right_natDegree_eq_left_add_one
      hdeg μ
  refine lt_of_le_of_ne hle ?_
  intro hnat
  have htop_zero :
      (X * p - C μ * q).coeff q.natDegree = 0 := by
    simpa [coeff_X_mul_sub_C_mul_right_natDegree_of_right_natDegree_eq_left_add_one
      hdeg μ] using hcoeff
  have hP_ne : X * p - C μ * q ≠ 0 := by
    intro hzero
    have hqdeg_zero : q.natDegree = 0 := by
      rw [← hnat, hzero]
      rfl
    have hq_pos : 0 < q.natDegree := by
      rw [hdeg]
      exact Nat.succ_pos _
    exact (Nat.ne_of_gt hq_pos) hqdeg_zero
  have htop_ne :
      (X * p - C μ * q).coeff q.natDegree ≠ 0 := by
    rw [← hnat, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hP_ne
  exact htop_ne htop_zero

/-- If the right endpoint has degree at most the left endpoint, then the
`X * p` term controls the leading term of the x-subtraction pencil. -/
theorem posLeadingCoeff_and_natDegree_X_mul_sub_C_mul_of_right_natDegree_le
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q)
    (hqdeg : q.natDegree ≤ p.natDegree) (μ : ℝ) :
    HasPosLeadingCoeff (X * p - C μ * q) ∧
      (X * p - C μ * q).natDegree = p.natDegree + 1 := by
  have hXp_deg : (X * p).natDegree = p.natDegree + 1 :=
    Polynomial.natDegree_X_mul h.left_pos.ne_zero
  have hC_deg_lt : (C μ * q).natDegree < (X * p).natDegree := by
    have hC_le : (C μ * q).natDegree ≤ q.natDegree :=
      Polynomial.natDegree_C_mul_le μ q
    rw [hXp_deg]
    exact hC_le.trans_lt (hqdeg.trans_lt (Nat.lt_succ_self _))
  have hnegC_deg_lt : (-(C μ * q)).natDegree < (X * p).natDegree := by simpa using hC_deg_lt
  constructor
  · simpa [sub_eq_add_neg] using
      hasPosLeadingCoeff_add_of_natDegree_lt_left
        (p := X * p) (q := -(C μ * q)) hnegC_deg_lt h.left_pos.X_mul
  · simpa [hXp_deg, sub_eq_add_neg] using
      natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff
        (p := X * p) (q := -(C μ * q)) hnegC_deg_lt h.left_pos.X_mul

theorem rootCountAbove_bounds_of_nonRoot {p q : ℝ[X]}
    (h : PositiveSplitRootCountPair p q) {x : ℝ}
    (hpx : ¬ p.IsRoot x) (hqx : ¬ q.IsRoot x) :
    ((p.roots.filter (x < ·)).card : ℤ) -
        (q.roots.filter (x < ·)).card ≤ 1 ∧
      ((q.roots.filter (x < ·)).card : ℤ) -
        (p.roots.filter (x < ·)).card ≤ 1 :=
  h.count.rootCountAbove_bounds_of_nonRoot
    h.left_pos.ne_zero h.right_pos.ne_zero hpx hqx

theorem card_right_roots_filter_gt_le_one_of_left_largest_root
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q) {a : ℝ}
    (ha : IsLargestRoot p a) :
    (q.roots.filter (a < ·)).card ≤ 1 := by
  have hbound :=
    rootCountAbove_diff_le_one_of_nonRoot_isRoot
      h.left_pos.ne_zero h.right_pos.ne_zero
      (fun x hpx hqx => h.rootCountAbove_bounds_of_nonRoot hpx hqx) a
  have hp_zero : (p.roots.filter (a < ·)).card = 0 :=
    rootCountAbove_eq_zero_of_forall_roots_le fun r hr => ha.roots_le r hr
  have hq_le_int : ((q.roots.filter (a < ·)).card : ℤ) ≤ 1 := by simpa [hp_zero] using hbound.2
  exact_mod_cast hq_le_int

theorem left_natDegree_add_card_right_roots_filter_lt_le_right_natDegree_add_one
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q) {a : ℝ}
    (hroots_ge : ∀ r ∈ p.roots, a ≤ r) :
    p.natDegree + (q.roots.filter (fun r => r < a)).card ≤
      q.natDegree + 1 := by
  let lower := (q.roots.filter (fun r => r < a)).card
  let upper := rootCountAtOrAbove q a
  have hp_count : rootCountAtOrAbove p a = p.natDegree := by
    have hfilter : p.roots.filter (fun r => a ≤ r) = p.roots :=
      Multiset.filter_eq_self.mpr hroots_ge
    simp [rootCountAtOrAbove, hfilter, card_roots_of_splits h.left_splits]
  have hpart : lower + upper = q.natDegree := by
    have hcard := congrArg Multiset.card
      (Multiset.filter_add_not (p := fun r : ℝ => r < a) q.roots)
    have hnot : q.roots.filter (fun r : ℝ => ¬ r < a) =
        q.roots.filter (fun r : ℝ => a ≤ r) := by
      apply Multiset.filter_congr
      intro r _hr
      simp [not_lt]
    rw [Multiset.card_add] at hcard
    simpa [lower, upper, rootCountAtOrAbove, hnot, card_roots_of_splits h.right_splits]
      using hcard
  have hbound : ((p.natDegree : ℤ) - upper) ≤ 1 := by
    simpa [hp_count, upper] using (h.count.bounds a).1
  have hpart_int : (lower : ℤ) + upper = q.natDegree := by exact_mod_cast hpart
  have hmain : (p.natDegree : ℤ) + lower ≤ q.natDegree + 1 := by linarith
  exact_mod_cast hmain

theorem card_right_roots_filter_lt_eq_zero_of_left_roots_ge_of_left_natDegree_eq_right_add_one
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q) {a : ℝ}
    (hroots_ge : ∀ r ∈ p.roots, a ≤ r)
    (hdeg : p.natDegree = q.natDegree + 1) :
    (q.roots.filter (fun r => r < a)).card = 0 := by
  have hbound :=
    h.left_natDegree_add_card_right_roots_filter_lt_le_right_natDegree_add_one
      hroots_ge
  have hlower_le : (q.roots.filter (fun r => r < a)).card ≤ 0 := by lia
  exact Nat.eq_zero_of_le_zero hlower_le

theorem card_right_roots_filter_lt_le_one_of_left_roots_ge_of_natDegree_eq
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q) {a : ℝ}
    (hroots_ge : ∀ r ∈ p.roots, a ≤ r)
    (hdeg : p.natDegree = q.natDegree) :
    (q.roots.filter (fun r => r < a)).card ≤ 1 := by
  have hbound :=
    h.left_natDegree_add_card_right_roots_filter_lt_le_right_natDegree_add_one
      hroots_ge
  lia

theorem card_right_roots_filter_lt_le_two_of_roots_ge_of_right_successor
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q) {a : ℝ}
    (hroots_ge : ∀ r ∈ p.roots, a ≤ r)
    (hdeg : q.natDegree = p.natDegree + 1) :
    (q.roots.filter (fun r => r < a)).card ≤ 2 := by
  have hbound :=
    h.left_natDegree_add_card_right_roots_filter_lt_le_right_natDegree_add_one
      hroots_ge
  lia

theorem sameDegreeRootCountAboveNonRoot {p q : ℝ[X]}
    (h : PositiveSplitRootCountPair p q)
    (_hdeg : q.natDegree = p.natDegree) :
    ∀ x : ℝ, ¬ p.IsRoot x → ¬ q.IsRoot x →
      ((p.roots.filter (x < ·)).card : ℤ) -
          (q.roots.filter (x < ·)).card ≤ 1 ∧
        ((q.roots.filter (x < ·)).card : ℤ) -
          (p.roots.filter (x < ·)).card ≤ 1 :=
  fun _ hpx hqx => h.rootCountAbove_bounds_of_nonRoot hpx hqx

theorem succDegreeRootCountAboveNonRoot {p q : ℝ[X]}
    (h : PositiveSplitRootCountPair p q)
    (_hdeg : q.natDegree = p.natDegree + 1) :
    ∀ x : ℝ, ¬ p.IsRoot x → ¬ q.IsRoot x →
      ((p.roots.filter (x < ·)).card : ℤ) -
          (q.roots.filter (x < ·)).card ≤ 1 ∧
        ((q.roots.filter (x < ·)).card : ℤ) -
          (p.roots.filter (x < ·)).card ≤ 1 :=
  fun _ hpx hqx => h.rootCountAbove_bounds_of_nonRoot hpx hqx

end PositiveSplitRootCountPair

/-- Deleting a common root from both endpoints preserves the positive-split
root-count pair structure. -/
theorem PositiveSplitRootCountPair.deleteRootFactor_commonRoot {p q : ℝ[X]}
    (h : PositiveSplitRootCountPair p q) {r : ℝ}
    (hp : p.IsRoot r) (hq : q.IsRoot r) :
    PositiveSplitRootCountPair (deleteRootFactor p r)
      (deleteRootFactor q r) := by
  have hp_delete_pos : HasPosLeadingCoeff (deleteRootFactor p r) := by
    simpa [HasPosLeadingCoeff,
      leadingCoeff_deleteRootFactor_of_isRoot h.left_pos.ne_zero hp]
      using h.left_pos
  have hq_delete_pos : HasPosLeadingCoeff (deleteRootFactor q r) := by
    simpa [HasPosLeadingCoeff,
      leadingCoeff_deleteRootFactor_of_isRoot h.right_pos.ne_zero hq]
      using h.right_pos
  exact
    ⟨hp_delete_pos, hq_delete_pos,
      deleteRootFactor_splits_of_isRoot h.left_splits hp,
      deleteRootFactor_splits_of_isRoot h.right_splits hq,
      h.count.deleteRootFactor_commonRoot
        h.left_pos.ne_zero h.right_pos.ne_zero hp hq⟩

/-- Deleting a common root from both endpoints of a positive-split pair
preserves the left-successor degree relation. -/
theorem PositiveSplitRootCountPair.natDegree_deleteRootFactor_left_eq_right_add_one
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q) {r : ℝ}
    (hq : q.IsRoot r) (hdeg : p.natDegree = q.natDegree + 1) :
    (deleteRootFactor p r).natDegree =
      (deleteRootFactor q r).natDegree + 1 := by
  have hq_pos : 0 < q.natDegree :=
    natDegree_pos_of_isRoot h.right_pos.ne_zero hq
  exact natDegree_deleteRootFactor_left_eq_right_add_one_of_natDegree_eq
    hdeg hq_pos

/-- Deleting a common root from both endpoints of a positive-split pair
preserves the right-successor degree relation. -/
theorem PositiveSplitRootCountPair.natDegree_deleteRootFactor_right_eq_left_add_one
    {p q : ℝ[X]} (h : PositiveSplitRootCountPair p q) {r : ℝ}
    (hp : p.IsRoot r) (hdeg : q.natDegree = p.natDegree + 1) :
    (deleteRootFactor q r).natDegree =
      (deleteRootFactor p r).natDegree + 1 := by
  have hp_pos : 0 < p.natDegree :=
    natDegree_pos_of_isRoot h.left_pos.ne_zero hp
  exact natDegree_deleteRootFactor_right_eq_left_add_one_of_natDegree_eq
    hdeg hp_pos

/-- Deleting a common root from both endpoints of a positive-split pair
preserves the same-degree relation. -/
theorem PositiveSplitRootCountPair.natDegree_deleteRootFactor_eq
    {p q : ℝ[X]} (_h : PositiveSplitRootCountPair p q) {r : ℝ}
    (hdeg : p.natDegree = q.natDegree) :
    (deleteRootFactor p r).natDegree =
      (deleteRootFactor q r).natDegree :=
  natDegree_deleteRootFactor_eq_of_natDegree_eq hdeg

end LiuOppositeSigns
end RealRooted
