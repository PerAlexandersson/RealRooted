module

import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.SplitEndpoints
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.UpperTail
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.GapCounts
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.RootFilters
public import RealRooted.LiuOppositeSigns.NoCommonRoots
public import RealRooted.LiuOppositeSigns.PositiveSplitRootCount
import RealRooted.WagnerRightSum.Sign
import RealRooted.Mathlib.Algebra.Polynomial.Splits

/-!
# Liu x-subtraction left-successor degree endpoint.
-/

public section

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns
/-- The lower exterior root credit in the left-successor degree case.
Its sign follows from the parity of the right degree. -/
private lemma one_le_lower_tail_of_left_successor {p q : ℝ[X]}
    (hpair : PositiveSplitRootCountPair p q) (hno : NoCommonRoots p q)
    {a μ : ℝ} (ha : p.IsRoot a) (hroots_ge : ∀ r ∈ p.roots, a ≤ r)
    (hdeg : p.natDegree = q.natDegree + 1) (hμ : 0 < μ) :
    1 ≤ ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card := by
  let P := X * p - C μ * q
  have htail_card := hpair.card_right_roots_filter_gt_eq_natDegree_of_left_roots_ge
    hno ha hroots_ge hdeg
  have hqa : ¬ q.IsRoot a := hno a ha
  have hP_data := hpair.posLeadingCoeff_and_natDegree_X_mul_sub_C_mul_of_right_natDegree_le
    (by rw [hdeg]; exact Nat.le_succ _) μ
  have hP_pos : HasPosLeadingCoeff P := hP_data.1
  have hP_natDegree_q : P.natDegree = q.natDegree + 2 := by rw [hP_data.2, hdeg]
  have hP_degree_pos : 0 < P.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [hP_natDegree_q]; lia)
  rcases Nat.even_or_odd q.natDegree with hq_even | hq_odd
  · have hq_a_pos : 0 < q.eval a :=
      (hpair.right_splits.eval_pos_iff_even_card_roots_gt
        (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr
          (by simpa [htail_card] using hq_even)
    have hP_even : Even P.natDegree := by
      rw [hP_natDegree_q]
      exact hq_even.add (by norm_num)
    have hbot : Tendsto (fun x => P.eval x) atBot atTop :=
      tendsto_eval_atBot_atTop_of_posLeadingCoeff_even
        hP_pos hP_degree_pos hP_even
    have hP_ne : P ≠ 0 := hP_pos.ne_zero
    simpa [P] using
      one_le_card_xSub_roots_filter_le_of_left_root_right_eval_nonneg
        ha hq_a_pos.le hμ hP_ne hbot
  · have hq_a_neg : q.eval a < 0 :=
      (hpair.right_splits.eval_neg_iff_odd_card_roots_gt
        (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr
          (by simpa [htail_card] using hq_odd)
    have hP_odd : Odd P.natDegree := by
      rw [hP_natDegree_q]
      exact hq_odd.add_even (by norm_num)
    have hbot : Tendsto (fun x => P.eval x) atBot atBot :=
      tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd
        hP_pos hP_degree_pos hP_odd
    have hP_ne : P ≠ 0 := hP_pos.ne_zero
    simpa [P] using
      one_le_card_xSub_roots_filter_le_of_left_root_right_eval_nonpos
        ha (le_of_lt hq_a_neg) hμ hP_ne hbot

/-- In the left-successor degree case, the sorted-root count endpoint proves
splitting whenever the left endpoint has at least two distinct root locations
and both endpoint polynomials have nonnegative coefficients.

The lower tail is obtained from the parity of the strict upper right-root count
above the first left root.  The upper tail uses
`upper_nonpos_tail_add_one_le_card_xSub_ge`, so the endpoint-zero branch is
included. -/
theorem
    PositiveSplitRootCountPair.xSub_splits_of_roots_sort_of_left_successor_nonneg
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hq_nonneg : HasNonnegCoeffs q)
    (hno : NoCommonRoots p q) {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs)
    (hdeg : p.natDegree = q.natDegree + 1) (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  let P := X * p - C μ * q
  have hhead :=
    isRoot_head_and_roots_ge_of_roots_toFinset_sort_eq_cons
      hpair.left_pos.ne_zero hrs
  have ha : p.IsRoot a := hhead.1
  have hroots_ge : ∀ r ∈ p.roots, a ≤ r := hhead.2
  have hP_data :=
    hpair.posLeadingCoeff_and_natDegree_X_mul_sub_C_mul_of_right_natDegree_le
      (by rw [hdeg]; exact Nat.le_succ _) μ
  have hP_pos : HasPosLeadingCoeff P := by simpa [P] using hP_data.1
  have hP_natDegree : P.natDegree = p.natDegree + 1 := by simpa [P] using hP_data.2
  have hP_natDegree_q : P.natDegree = q.natDegree + 2 := by rw [hP_natDegree, hdeg]
  have hP_nat_pos : 0 < P.natDegree := by
    rw [hP_natDegree]
    exact Nat.succ_pos _
  have hP_degree_pos : 0 < P.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hP_nat_pos
  have htop : Tendsto (fun x => P.eval x) atTop atTop :=
    P.tendsto_atTop_of_leadingCoeff_nonneg hP_degree_pos hP_pos.le
  have hupper_nonpos :
      ∀ y ∈ q.roots, (b :: xs).getLast (List.cons_ne_nil b xs) < y → y ≤ 0 :=
    fun y hy _ => roots_nonpos_of_hasNonnegCoeffs hq_nonneg y hy
  have hlower_one :
      1 ≤ (P.roots.filter (fun x => x ≤ a)).card := by
    exact one_le_lower_tail_of_left_successor hpair hno ha hroots_ge hdeg hμ
  exact hpair.xSub_splits_of_roots_sort_of_upper_nonpos_tail_transfer
    hp_nonneg hno hrs hμ hdeg (by simpa [P] using hlower_one)
    hupper_nonpos (by simpa [P] using htop)

/-- The exterior-tail credits close the left-successor endpoint
when the left root list has a single distinct location. -/
private lemma splits_of_extremal_left_root_left_successor {p q : ℝ[X]}
    (hpair : PositiveSplitRootCountPair p q) (hq_nonneg : HasNonnegCoeffs q)
    (hno : NoCommonRoots p q) {a μ : ℝ}
    (hhead : p.IsRoot a ∧ ∀ r ∈ p.roots, a ≤ r)
    (ha_largest : IsLargestRoot p a) (hdeg : p.natDegree = q.natDegree + 1) (hμ : 0 < μ)
    (htail_card : (q.roots.filter (a < ·)).card = q.natDegree) :
    (X * p - C μ * q).Splits := by
  let P := X * p - C μ * q
  let lowerTail := (P.roots.filter (fun x => x ≤ a)).card
  let upperTail := (P.roots.filter (fun x => a ≤ x)).card
  have hPnot : ¬ P.IsRoot a := hno.not_isRoot_xSub_of_left_root hhead.1 hμ.ne'
  have hfilter : P.roots.filter (a ≤ ·) = P.roots.filter (a < ·) := by
    apply Multiset.filter_congr
    intro x hx
    have hxa : x ≠ a := by
      rintro rfl
      exact hPnot (Polynomial.isRoot_of_mem_roots hx)
    exact ⟨fun h => lt_of_le_of_ne h hxa.symm, le_of_lt⟩
  have hpack : lowerTail + upperTail = P.roots.card := by
    dsimp [lowerTail, upperTail]
    rw [hfilter]
    simpa only [Multiset.card_add, not_le] using
      congrArg Multiset.card (Multiset.filter_add_not (fun x => x ≤ a) P.roots)
  have hupper_nonpos : ∀ y ∈ q.roots, a < y → y ≤ 0 :=
    fun y hy _ => roots_nonpos_of_hasNonnegCoeffs hq_nonneg y hy
  have hdata := hpair.posLeadingCoeff_and_natDegree_X_mul_sub_C_mul_of_right_natDegree_le
    (by rw [hdeg]; exact Nat.le_succ _) μ
  have hdegree : P.natDegree = q.natDegree + 2 := by rw [hdata.2, hdeg]
  have htop : Tendsto (fun x => P.eval x) atTop atTop :=
    P.tendsto_atTop_of_leadingCoeff_nonneg
      (natDegree_pos_iff_degree_pos.mp (by rw [hdegree]; lia)) hdata.1.le
  have hlo : 1 ≤ lowerTail :=
    one_le_lower_tail_of_left_successor hpair hno hhead.1 hhead.2 hdeg hμ
  have hup : q.natDegree + 1 ≤ upperTail := by
    rw [← htail_card]
    exact hpair.upper_nonpos_tail_add_one_le_card_xSub_ge
      hno ha_largest hμ (by rw [hdeg]; lia) hupper_nonpos htop
  exact Polynomial.splits_of_le_roots_of_natDegree_le_card (s := P.roots)
    le_rfl (by rw [hdegree]; lia)

/-- No-common-root branch of the left-successor x-subtraction family, in the
unshifted `p, q` form.  If `p` has at least two distinct roots, the sorted-root
count endpoint applies directly.  If it has only one distinct root, the
same exterior-tail credits apply directly, without a low-degree endpoint. -/
theorem PositiveSplitRootCountPair.xSub_splits_of_left_successor_nonneg_of_noCommonRoots
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hq_nonneg : HasNonnegCoeffs q)
    (hno : NoCommonRoots p q)
    (hdeg : p.natDegree = q.natDegree + 1) {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  cases hrs : p.roots.toFinset.sort (· ≤ ·) with
  | nil =>
      have hp_nat_pos : 0 < p.natDegree := by
        rw [hdeg]
        exact Nat.succ_pos _
      have hroots_pos : 0 < p.roots.card := by
        simpa [Polynomial.splits_iff_card_roots.mp hpair.left_splits] using hp_nat_pos
      obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
      have hx_sort : x ∈ p.roots.toFinset.sort (· ≤ ·) := by
        rw [Finset.mem_sort, Multiset.mem_toFinset]
        exact hx
      rw [hrs] at hx_sort
      simp at hx_sort
  | cons a xs =>
      cases hxs : xs with
      | nil =>
          have hrs_single : p.roots.toFinset.sort (· ≤ ·) = [a] := by simpa [hxs] using hrs
          have hhead :=
            isRoot_head_and_roots_ge_of_roots_toFinset_sort_eq_cons
              hpair.left_pos.ne_zero hrs_single
          have ha_largest : IsLargestRoot p a := by
            refine ⟨hhead.1, ?_⟩
            intro s hs
            have hs_sort : s ∈ p.roots.toFinset.sort (· ≤ ·) := by
              rw [Finset.mem_sort, Multiset.mem_toFinset]
              exact hs
            rw [hrs_single] at hs_sort
            have hs_eq : s = a := by simpa using hs_sort
            exact le_of_eq hs_eq
          have htail_card : (q.roots.filter (a < ·)).card = q.natDegree :=
            hpair.card_right_roots_filter_gt_eq_natDegree_of_left_roots_ge
              hno hhead.1 hhead.2 hdeg
          exact splits_of_extremal_left_root_left_successor
            hpair hq_nonneg hno hhead ha_largest hdeg hμ
            htail_card
      | cons b ys =>
          have hrs_two :
              p.roots.toFinset.sort (· ≤ ·) = a :: b :: ys := by
            simpa [hxs] using hrs
          exact hpair.xSub_splits_of_roots_sort_of_left_successor_nonneg
            hp_nonneg hq_nonneg hno hrs_two hdeg hμ

/-- Left-successor x-subtraction family in unshifted positive-split form,
allowing common roots.  The proof peels common roots by strong induction on the
right endpoint degree and dispatches the reduced branch to the no-common-root
theorem. -/
theorem PositiveSplitRootCountPair.xSub_splits_of_left_successor_nonneg
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hq_nonneg : HasNonnegCoeffs q)
    (hdeg : p.natDegree = q.natDegree + 1) {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits :=
  hpair.xSub_splits_of_forall_noCommonRoots (a := 0) (b := 1)
    (fun hpair hp hq hno hdeg _ hμ =>
      hpair.xSub_splits_of_left_successor_nonneg_of_noCommonRoots hp hq hno hdeg hμ)
    hp_nonneg hq_nonneg hdeg hμ

/-- Unrestricted positive-split left-successor translated x-subtraction
family. -/
theorem positiveSplitLeftSuccDegreeTranslatedXSubRightFamily {f g : ℝ[X]} (r : ℝ)
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree + 1) (μ : ℝ) (hμ : 0 < μ) :
    (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  let p := f.comp (X + C r)
  let q := g.comp (X + C r)
  have hpair_shift : PositiveSplitRootCountPair p q := by simpa [p, q] using hpair.comp_X_add_C r
  have hdeg_shift : p.natDegree = q.natDegree + 1 := by
    simpa [p, q, Polynomial.natDegree_comp] using hdeg
  simpa [p, q] using
    hpair_shift.xSub_splits_of_left_successor_nonneg
      hfnn hgnn hdeg_shift hμ

end LiuOppositeSigns
end RealRooted
