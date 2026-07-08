import RealRooted.Basic
import RealRooted.RootOrderBridge
import Mathlib.Tactic

/-!
# Succ-degree root crossing

This module records a small checked base case for the succ-degree
root-crossing target and a concrete warning example for the stronger fixed
orientation route.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Degree-one analytic core of the succ-degree root-crossing target.

For a linear factor with root `α` and a quadratic with ordered roots
`γ ≤ β`, if every strictly positive linear combination is real-rooted, then
the smaller quadratic root lies to the left of the linear root. -/
theorem root_le_of_posCombo_deg1
    {α β γ : ℝ} (hβγ : γ ≤ β)
    (hsplit : ∀ lam μ : ℝ, 0 < lam → 0 < μ →
      (C lam * (X - C α) + C μ * ((X - C β) * (X - C γ))).Splits) :
    γ ≤ α := by
  contrapose! hsplit
  refine ⟨β + γ - 2 * α, 1, ?_, ?_, ?_⟩ <;> try linarith
  rw [Polynomial.splits_iff_card_roots]
  erw [Polynomial.natDegree_add_eq_right_of_natDegree_lt]
  · erw [Polynomial.natDegree_C_mul] <;> norm_num
    erw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _)
        (Polynomial.X_sub_C_ne_zero _), Polynomial.natDegree_X_sub_C,
      Polynomial.natDegree_X_sub_C]
    exact ne_of_lt
      (lt_of_le_of_lt
        (Multiset.card_le_card <|
          show Polynomial.roots _ ≤ 0 from by
            exact Multiset.le_zero.mpr <| by
              exact Multiset.eq_zero_of_forall_notMem fun r hr => by
                norm_num at hr
                nlinarith [sq_nonneg (r - α)])
        (by norm_num))
  · rw [Polynomial.natDegree_C_mul, Polynomial.natDegree_C_mul] <;> norm_num
    · rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _)
        (Polynomial.X_sub_C_ne_zero _), Polynomial.natDegree_X_sub_C,
        Polynomial.natDegree_X_sub_C]
      norm_num
    · linarith

/-- Every strictly positive combination of `f = 2 * X + 1` and
`g = (X + 1) * (X + 2)` is real-rooted.

The example is useful because the root `-1 / 2` of `f` lies to the right of
both roots of `g`; positive-combination real-rootedness alone does not force
the fixed succ-degree orientation `Prec f g`. -/
theorem posCombo_deg1_all_splits :
    ∀ lam μ : ℝ, 0 < lam → 0 < μ →
      (C lam * (C 2 * X + C 1) + C μ * ((X + C 1) * (X + C 2))).Splits := by
  intro lam μ hlam hμ
  have h_discriminant : (2 * lam + 3 * μ)^2 - 4 * μ * (lam + 2 * μ) > 0 := by
    nlinarith
  rw [Polynomial.splits_iff_card_roots]
  rw [show
      C lam * (C 2 * X + C 1) + C μ * ((X + C 1) * (X + C 2)) =
        C μ *
          ((X -
              C ((-(2 * lam + 3 * μ) +
                    Real.sqrt ((2 * lam + 3 * μ)^2 - 4 * μ * (lam + 2 * μ))) /
                  (2 * μ))) *
            (X -
              C ((-(2 * lam + 3 * μ) -
                    Real.sqrt ((2 * lam + 3 * μ)^2 - 4 * μ * (lam + 2 * μ))) /
                  (2 * μ)))) from ?_]
  · rw [Polynomial.roots_mul, Polynomial.roots_mul]
    · rw [Polynomial.natDegree_mul', Polynomial.natDegree_mul'] <;> aesop
    · exact mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _)
    · exact mul_ne_zero (Polynomial.C_ne_zero.mpr hμ.ne')
        (mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _))
  · refine Polynomial.funext fun x => ?_
    norm_num
    ring_nf
    norm_num [hμ.ne', hlam.ne']
    ring_nf
    grind

private lemma roots_X_add_one_mul_X_add_two_le_neg_one :
    ∀ r ∈ (((X + C 1) * (X + C 2) : ℝ[X]).roots), r ≤ -1 := by
  intro r hr
  rw [Polynomial.mem_roots] at hr
  · norm_num at hr ⊢
    rcases hr with hr | hr <;> linarith
  · exact mul_ne_zero (by simpa using Polynomial.X_add_C_ne_zero (1 : ℝ))
      (by simpa using Polynomial.X_add_C_ne_zero (2 : ℝ))

private lemma neg_half_mem_roots_two_mul_X_add_one :
    (-1 / 2 : ℝ) ∈ ((C 2 * X + C 1 : ℝ[X]).roots) := by
  rw [Polynomial.mem_roots]
  · norm_num
  · intro h
    have hc := congrArg (fun p : ℝ[X] => p.coeff 1) h
    norm_num [Polynomial.coeff_one] at hc

/-- The explicit positive-combination example is not in the fixed succ-degree
orientation `Prec f g`. -/
theorem not_prec_deg1_example :
    ¬ Prec (C 2 * X + C 1 : ℝ[X]) ((X + C 1) * (X + C 2)) := by
  intro hprec
  have hle : (-1 / 2 : ℝ) ≤ -1 :=
    roots_le_of_prec_right hprec roots_X_add_one_mul_X_add_two_le_neg_one
      (-1 / 2) neg_half_mem_roots_two_mul_X_add_one
  linarith

/-- Interval-endpoint form of the succ-degree root-crossing data.

Given two finite multisets of reals with `N.card = M.card + 1` whose lower
counting functions satisfy the asymmetric succ-degree gaps
(`#{M ≤ x} ≤ #{N ≤ x}` and `#{N ≤ x} ≤ #{M ≤ x} + 2` at every threshold `x`),
each interior slot of the descending sorted `M`-list is bracketed by two
descending `N`-slots two apart: the `j`-th largest element of `M` lies in the
closed interval between the `(j+1)`-th largest and the `(j-1)`-th largest
elements of `N`.

This repackages the two one-sided conclusions of
`succRootCrossing_of_count_le_two` into a single per-slot bracketing statement,
which is the convenient interval-endpoint datum for the succ-degree
Chudnovsky--Seymour route. -/
theorem succ_interval_endpoint_of_count_le_two
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2) :
    ∀ j, 1 ≤ j → j < d →
      ((N.sort (· ≤ ·)).reverse).getD (j + 1) 0 ≤
          ((M.sort (· ≤ ·)).reverse).getD j 0 ∧
      ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
          ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0 := by
  obtain ⟨h1, h2⟩ := succRootCrossing_of_count_le_two hM hN hcount
  intro j hj1 hj2
  have hup := h2 j hj1 hj2
  have hlow := h1 (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) hj2
  rw [Nat.add_sub_cancel] at hlow
  exact ⟨hlow, hup⟩

/-- The bottom endpoint consequence of the succ-degree lower-count bound. -/
theorem succDegree_smallest_root_le_of_count_le_two
    {M N : Multiset ℝ} {d : ℕ} (hd : 1 ≤ d)
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2) :
    ((N.sort (· ≤ ·)).reverse).getD d 0 ≤
      ((M.sort (· ≤ ·)).reverse).getD (d - 1) 0 :=
  (succRootCrossing_of_count_le_two hM hN hcount).1 d hd le_rfl

/-- The bottom endpoint consequence of the succ-degree upper-count bound. -/
theorem succDegree_smallest_root_le_of_count_gt_diff_le_one
    {M N : Multiset ℝ} {d : ℕ} (hd : 1 ≤ d)
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount : ∀ x : ℝ,
      ((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
      ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1) :
    ((N.sort (· ≤ ·)).reverse).getD d 0 ≤
      ((M.sort (· ≤ ·)).reverse).getD (d - 1) 0 :=
  (succRootCrossing_of_count_gt_diff_le_one hM hN hcount).1 d hd le_rfl

/-- Combined bottom endpoint consequence of the succ-degree count alternatives. -/
theorem succDegree_smallest_root_le_of_count
    {M N : Multiset ℝ} {d : ℕ} (hd : 1 ≤ d)
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount :
      (∀ x : ℝ,
        ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
        ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2) ∨
      (∀ x : ℝ,
        ((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
        ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1)) :
    ((N.sort (· ≤ ·)).reverse).getD d 0 ≤
      ((M.sort (· ≤ ·)).reverse).getD (d - 1) 0 := by
  rcases hcount with hcount | hcount
  · exact succDegree_smallest_root_le_of_count_le_two hd hM hN hcount
  · exact succDegree_smallest_root_le_of_count_gt_diff_le_one hd hM hN hcount

/-- Interval-endpoint form of the succ-degree root-crossing data, from the
upper-threshold count bound.

Given two finite multisets of reals with `N.card = M.card + 1` whose upper
counting functions differ by at most one at every threshold `x`, each interior
slot of the descending sorted `M`-list is bracketed by two descending `N`-slots
two apart.

This is the upper-threshold analogue of `succ_interval_endpoint_of_count_le_two`,
built on `succRootCrossing_of_count_gt_diff_le_one`. -/
theorem succ_interval_endpoint_of_count_gt_diff_le_one
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount : ∀ x : ℝ,
      ((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
      ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1) :
    ∀ j, 1 ≤ j → j < d →
      ((N.sort (· ≤ ·)).reverse).getD (j + 1) 0 ≤
          ((M.sort (· ≤ ·)).reverse).getD j 0 ∧
      ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
          ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0 := by
  obtain ⟨h1, h2⟩ := succRootCrossing_of_count_gt_diff_le_one hM hN hcount
  intro j hj1 hj2
  have hup := h2 j hj1 hj2
  have hlow := h1 (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) hj2
  rw [Nat.add_sub_cancel] at hlow
  exact ⟨hlow, hup⟩

/-- Combined interval-endpoint form of the succ-degree count alternatives. -/
theorem succ_interval_endpoint_of_count
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount :
      (∀ x : ℝ,
        ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
        ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2) ∨
      (∀ x : ℝ,
        ((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
        ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1)) :
    ∀ j, 1 ≤ j → j < d →
      ((N.sort (· ≤ ·)).reverse).getD (j + 1) 0 ≤
          ((M.sort (· ≤ ·)).reverse).getD j 0 ∧
      ((M.sort (· ≤ ·)).reverse).getD j 0 ≤
          ((N.sort (· ≤ ·)).reverse).getD (j - 1) 0 := by
  intro j hj1 hj2
  rcases hcount with hcount | hcount
  · exact succ_interval_endpoint_of_count_le_two hM hN hcount j hj1 hj2
  · exact succ_interval_endpoint_of_count_gt_diff_le_one hM hN hcount j hj1 hj2

/-- `Set.Icc` packaging of the upper-threshold succ-degree interval endpoint.

Under the same hypotheses as `succ_interval_endpoint_of_count_gt_diff_le_one`,
each interior slot of the descending sorted `M`-list lies in the closed
interval whose endpoints are the two surrounding descending `N`-slots. -/
theorem succ_slot_mem_Icc_of_count_gt_diff_le_one
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount : ∀ x : ℝ,
      ((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
      ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1) :
    ∀ j, 1 ≤ j → j < d →
      ((M.sort (· ≤ ·)).reverse).getD j 0 ∈
        Set.Icc (((N.sort (· ≤ ·)).reverse).getD (j + 1) 0)
          (((N.sort (· ≤ ·)).reverse).getD (j - 1) 0) := by
  intro j hj1 hj2
  rw [Set.mem_Icc]
  exact succ_interval_endpoint_of_count_gt_diff_le_one hM hN hcount j hj1 hj2

/-- Lower-threshold `Set.Icc` membership form of
`succ_interval_endpoint_of_count_le_two`. -/
theorem succ_slot_mem_Icc_of_count_le_two
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2) :
    ∀ j, 1 ≤ j → j < d →
      ((M.sort (· ≤ ·)).reverse).getD j 0 ∈
        Set.Icc (((N.sort (· ≤ ·)).reverse).getD (j + 1) 0)
          (((N.sort (· ≤ ·)).reverse).getD (j - 1) 0) := by
  intro j hj1 hj2
  rw [Set.mem_Icc]
  exact succ_interval_endpoint_of_count_le_two hM hN hcount j hj1 hj2

/-- Nonempty-interval form of the upper-threshold succ-degree endpoint data. -/
theorem succ_interval_Icc_nonempty_of_count_gt_diff_le_one
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount : ∀ x : ℝ,
      ((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
      ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1) :
    ∀ j, 1 ≤ j → j < d →
      (Set.Icc (((N.sort (· ≤ ·)).reverse).getD (j + 1) 0)
          (((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)).Nonempty := by
  intro j hj1 hj2
  exact ⟨_, succ_slot_mem_Icc_of_count_gt_diff_le_one hM hN hcount j hj1 hj2⟩

/-- Nonempty-interval form of the lower-threshold succ-degree endpoint data. -/
theorem succ_interval_Icc_nonempty_of_count_le_two
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount : ∀ x : ℝ,
      ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
      ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2) :
    ∀ j, 1 ≤ j → j < d →
      (Set.Icc (((N.sort (· ≤ ·)).reverse).getD (j + 1) 0)
          (((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)).Nonempty := by
  intro j hj1 hj2
  exact ⟨_, succ_slot_mem_Icc_of_count_le_two hM hN hcount j hj1 hj2⟩

/-- Combined nonempty-interval form of the succ-degree endpoint data. -/
theorem succ_interval_Icc_nonempty_of_count
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount :
      (∀ x : ℝ,
        ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
        ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2) ∨
      (∀ x : ℝ,
        ((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
        ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1)) :
    ∀ j, 1 ≤ j → j < d →
      (Set.Icc (((N.sort (· ≤ ·)).reverse).getD (j + 1) 0)
          (((N.sort (· ≤ ·)).reverse).getD (j - 1) 0)).Nonempty := by
  intro j hj1 hj2
  rcases hcount with h | h
  · exact succ_interval_Icc_nonempty_of_count_le_two hM hN h j hj1 hj2
  · exact succ_interval_Icc_nonempty_of_count_gt_diff_le_one hM hN h j hj1 hj2

/-- Combined explicit-witness form of the succ-degree endpoint data. -/
theorem succ_slot_mem_Icc_of_count
    {M N : Multiset ℝ} {d : ℕ}
    (hM : M.card = d) (hN : N.card = d + 1)
    (hcount :
      (∀ x : ℝ,
        ((M.filter (· ≤ x)).card : ℤ) - (N.filter (· ≤ x)).card ≤ 0 ∧
        ((N.filter (· ≤ x)).card : ℤ) - (M.filter (· ≤ x)).card ≤ 2) ∨
      (∀ x : ℝ,
        ((M.filter (x < ·)).card : ℤ) - (N.filter (x < ·)).card ≤ 1 ∧
        ((N.filter (x < ·)).card : ℤ) - (M.filter (x < ·)).card ≤ 1)) :
    ∀ j, 1 ≤ j → j < d →
      ((M.sort (· ≤ ·)).reverse).getD j 0 ∈
        Set.Icc (((N.sort (· ≤ ·)).reverse).getD (j + 1) 0)
          (((N.sort (· ≤ ·)).reverse).getD (j - 1) 0) := by
  intro j hj1 hj2
  rcases hcount with h | h
  · exact succ_slot_mem_Icc_of_count_le_two hM hN h j hj1 hj2
  · exact succ_slot_mem_Icc_of_count_gt_diff_le_one hM hN h j hj1 hj2

end RealRooted
