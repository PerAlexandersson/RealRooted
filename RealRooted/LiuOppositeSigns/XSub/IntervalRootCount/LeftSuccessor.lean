import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.SplitEndpoints

/-!
# Liu x-subtraction left-successor degree endpoint.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns
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
  have htail_card : (q.roots.filter (a < ·)).card = q.natDegree :=
    hpair.card_right_roots_filter_gt_eq_natDegree_of_left_roots_ge
      hno ha hroots_ge hdeg
  have hqa : ¬ q.IsRoot a := hno a ha
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
  exact hpair.xSub_splits_of_roots_sort_of_upper_nonpos_tail_transfer
    hp_nonneg hno hrs hμ hdeg (by simpa [P] using hlower_one)
    hupper_nonpos (by simpa [P] using htop)

/-- No-common-root branch of the left-successor x-subtraction family, in the
unshifted `p, q` form.  If `p` has at least two distinct roots, the sorted-root
count endpoint applies directly.  If it has only one distinct root, the
upper-tail cap forces `q.natDegree ≤ 1`, so the existing low-degree endpoint
applies. -/
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
        simpa [card_roots_of_splits hpair.left_splits] using hp_nat_pos
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
          have htail_le : (q.roots.filter (a < ·)).card ≤ 1 :=
            hpair.card_right_roots_filter_gt_le_one_of_left_largest_root
              ha_largest
          have hqdeg_le : q.natDegree ≤ 1 := by simpa [htail_card] using htail_le
          have hp_nonneg_zero : HasNonnegCoeffs (p.comp (X + C (0 : ℝ))) := by
            simpa using hp_nonneg
          have hq_nonneg_zero : HasNonnegCoeffs (q.comp (X + C (0 : ℝ))) := by
            simpa using hq_nonneg
          by_cases hqzero : q.natDegree = 0
          · simpa using
              positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
                (f := p) (g := q) (r := 0)
                hpair hdeg hqzero μ hμ
          · have hqone : q.natDegree = 1 := by lia
            simpa using
              positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one
                (f := p) (g := q) (r := 0)
                hpair hp_nonneg_zero hq_nonneg_zero hdeg hqone μ hμ
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
