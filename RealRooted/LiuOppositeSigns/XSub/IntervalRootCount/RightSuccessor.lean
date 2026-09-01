import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.SplitEndpoints

/-!
# Liu x-subtraction right-successor degree endpoint.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns
/-- Positive-top-coefficient branch of the right-successor sorted-root count
endpoint.  The upper exterior tail supplies its strict right-root count plus
one additional root.  If the lower exterior tail has size two, the finite
lower-tail sign-change lemma supplies the one extra lower credit needed in that
case. -/
theorem
    PositiveSplitRootCountPair.xSub_splits_of_roots_sort_of_right_successor_nonneg_of_top_coeff_pos
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hq_nonneg : HasNonnegCoeffs q)
    (hno : NoCommonRoots p q) {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs)
    (hdeg : q.natDegree = p.natDegree + 1)
    (hcoeff : 0 < p.leadingCoeff - μ * q.leadingCoeff) (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  let P := X * p - C μ * q
  let last := (b :: xs).getLast (List.cons_ne_nil b xs)
  let L := (q.roots.filter (fun x => x < a)).card
  let G :=
    (((a :: b :: xs).zip (b :: xs)).map
      (fun ab => min 2
        (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum
  let U := (q.roots.filter (last < ·)).card
  let lowerTail := (P.roots.filter (fun x => x ≤ a)).card
  let upperTail := (P.roots.filter (fun x => last ≤ x)).card
  have hhead :=
    isRoot_head_and_roots_ge_of_roots_toFinset_sort_eq_cons
      hpair.left_pos.ne_zero hrs
  have hlast : IsLargestRoot p last := by
    simpa [last] using isLargestRoot_getLast_of_roots_toFinset_sort_eq_cons_cons
      hpair.left_pos.ne_zero hrs
  have hP_natDegree : P.natDegree = q.natDegree := by
    simpa [P] using
      hpair.natDegree_X_mul_sub_C_mul_eq_right_natDegree_of_right_natDegree_eq_left_add_one
        hdeg (ne_of_gt hcoeff)
  have hL_le : L ≤ 2 := by
    simpa [L] using
      hpair.card_right_roots_filter_lt_le_two_of_roots_ge_of_right_successor
        hhead.2 hdeg
  have hupper_nonpos : ∀ y ∈ q.roots, last < y → y ≤ 0 := by
    intro y hy _hy
    exact roots_nonpos_of_hasNonnegCoeffs hq_nonneg y hy
  have hupper_count : U + 1 ≤ upperTail := by
    simpa [U, upperTail, last, P] using
      hpair.upper_nonpos_tail_add_one_le_card_xSub_ge_of_top_coeff_pos
        hno hlast hμ hdeg hcoeff hupper_nonpos
  have hq_bound : q.natDegree ≤ L + G + U := by
    simpa [L, G, U, last] using
      hpair.right_natDegree_le_lower_sum_min_two_upper_of_roots_sort
        hno (a := a) (xs := b :: xs) (by simpa using hrs)
  have hcases : L = 0 ∨ L = 1 ∨ L = 2 := by lia
  rcases hcases with hL | hL | hL
  · have hlower_credit : 0 ≤ lowerTail := Nat.zero_le _
    exact hpair.xSub_splits_of_roots_sort_of_tail_credits_of_natDegree_le
      hp_nonneg hno hrs hμ
      (lowerCredit := 0) (upperCredit := U + 1)
      (by simp)
      (by simpa [upperTail] using hupper_count)
      (by rw [hP_natDegree]; lia)
  · have hlower_credit : 0 ≤ lowerTail := Nat.zero_le _
    exact hpair.xSub_splits_of_roots_sort_of_tail_credits_of_natDegree_le
      hp_nonneg hno hrs hμ
      (lowerCredit := 0) (upperCredit := U + 1)
      (by simp)
      (by simpa [upperTail] using hupper_count)
      (by rw [hP_natDegree]; lia)
  · have hlower_credit : 1 ≤ lowerTail := by
      simpa [L, lowerTail, P, hL] using
        hpair.one_le_card_xSub_le_of_card_right_roots_lt_head_eq_two
          hq_nonneg hno hhead.1 hhead.2 hdeg (by simpa [L] using hL) hμ
    exact hpair.xSub_splits_of_roots_sort_of_tail_credits_of_natDegree_le
      hp_nonneg hno hrs hμ
      (lowerCredit := 1) (upperCredit := U + 1)
      (by simpa [lowerTail] using hlower_credit)
      (by simpa [upperTail] using hupper_count)
      (by rw [hP_natDegree]; lia)

/-- Negative-top-coefficient branch of the right-successor sorted-root count
endpoint.  The lower exterior tail transfers completely, while the upper
exterior tail contributes its strict right-root count. -/
theorem
    PositiveSplitRootCountPair.xSub_splits_of_roots_sort_of_right_successor_nonneg_of_top_coeff_neg
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hq_nonneg : HasNonnegCoeffs q)
    (hno : NoCommonRoots p q) {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs)
    (hdeg : q.natDegree = p.natDegree + 1)
    (hcoeff : p.leadingCoeff - μ * q.leadingCoeff < 0) (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  let P := X * p - C μ * q
  let last := (b :: xs).getLast (List.cons_ne_nil b xs)
  let L := (q.roots.filter (fun x => x < a)).card
  let G :=
    (((a :: b :: xs).zip (b :: xs)).map
      (fun ab => min 2
        (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum
  let U := (q.roots.filter (last < ·)).card
  let lowerTail := (P.roots.filter (fun x => x ≤ a)).card
  let upperTail := (P.roots.filter (fun x => last ≤ x)).card
  have hhead :=
    isRoot_head_and_roots_ge_of_roots_toFinset_sort_eq_cons
      hpair.left_pos.ne_zero hrs
  have hlast : IsLargestRoot p last := by
    simpa [last] using isLargestRoot_getLast_of_roots_toFinset_sort_eq_cons_cons
      hpair.left_pos.ne_zero hrs
  have hP_natDegree : P.natDegree = q.natDegree := by
    simpa [P] using
      hpair.natDegree_X_mul_sub_C_mul_eq_right_natDegree_of_right_natDegree_eq_left_add_one
        hdeg (ne_of_lt hcoeff)
  have hlower_count : L ≤ lowerTail := by
    simpa [L, lowerTail, P] using
      hpair.card_right_roots_lt_head_le_card_xSub_le_of_top_coeff_neg
        hp_nonneg hno hhead.1 hhead.2 hdeg hcoeff hμ
  have hupper_nonpos : ∀ y ∈ q.roots, last < y → y ≤ 0 := by
    intro y hy _hy
    exact roots_nonpos_of_hasNonnegCoeffs hq_nonneg y hy
  have hupper_count : U ≤ upperTail := by
    simpa [U, upperTail, last, P] using
      hpair.card_right_roots_gt_le_card_xSub_ge_of_left_largest_root_nonpos
        hno hlast hμ hupper_nonpos
  have hq_bound : q.natDegree ≤ L + G + U := by
    simpa [L, G, U, last] using
      hpair.right_natDegree_le_lower_sum_min_two_upper_of_roots_sort
        hno (a := a) (xs := b :: xs) (by simpa using hrs)
  exact hpair.xSub_splits_of_roots_sort_of_tail_credits_of_natDegree_le
    hp_nonneg hno hrs hμ
    (lowerCredit := L) (upperCredit := U)
    (by simpa [lowerTail] using hlower_count)
    (by simpa [upperTail] using hupper_count)
    (by rw [hP_natDegree]; lia)

/-- Cancellation branch of the right-successor sorted-root count endpoint.  The
degree drop lets the count lose one exterior-tail credit; the only lower-tail
credit needed is the finite sign-change witness when the lower exterior tail has
size two. -/
theorem
    PositiveSplitRootCountPair.xSub_splits_of_roots_sort_of_right_successor_nonneg_of_top_coeff_zero
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hq_nonneg : HasNonnegCoeffs q)
    (hno : NoCommonRoots p q) {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs)
    (hdeg : q.natDegree = p.natDegree + 1)
    (hcoeff : p.leadingCoeff - μ * q.leadingCoeff = 0) (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  let P := X * p - C μ * q
  let last := (b :: xs).getLast (List.cons_ne_nil b xs)
  let L := (q.roots.filter (fun x => x < a)).card
  let G :=
    (((a :: b :: xs).zip (b :: xs)).map
      (fun ab => min 2
        (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum
  let U := (q.roots.filter (last < ·)).card
  let lowerTail := (P.roots.filter (fun x => x ≤ a)).card
  let upperTail := (P.roots.filter (fun x => last ≤ x)).card
  have hhead :=
    isRoot_head_and_roots_ge_of_roots_toFinset_sort_eq_cons
      hpair.left_pos.ne_zero hrs
  have hlast : IsLargestRoot p last := by
    simpa [last] using isLargestRoot_getLast_of_roots_toFinset_sort_eq_cons_cons
      hpair.left_pos.ne_zero hrs
  have hP_natDegree_lt : P.natDegree < q.natDegree := by
    simpa [P] using
      hpair.natDegree_X_mul_sub_C_mul_lt_right_natDegree_of_right_natDegree_eq_left_add_one
        hdeg hcoeff
  have hL_le : L ≤ 2 := by
    simpa [L] using
      hpair.card_right_roots_filter_lt_le_two_of_roots_ge_of_right_successor
        hhead.2 hdeg
  have hupper_nonpos : ∀ y ∈ q.roots, last < y → y ≤ 0 := by
    intro y hy _hy
    exact roots_nonpos_of_hasNonnegCoeffs hq_nonneg y hy
  have hupper_count : U ≤ upperTail := by
    simpa [U, upperTail, last, P] using
      hpair.card_right_roots_gt_le_card_xSub_ge_of_left_largest_root_nonpos
        hno hlast hμ hupper_nonpos
  have hq_bound : q.natDegree ≤ L + G + U := by
    simpa [L, G, U, last] using
      hpair.right_natDegree_le_lower_sum_min_two_upper_of_roots_sort
        hno (a := a) (xs := b :: xs) (by simpa using hrs)
  have hcases : L = 0 ∨ L = 1 ∨ L = 2 := by lia
  rcases hcases with hL | hL | hL
  · exact hpair.xSub_splits_of_roots_sort_of_tail_credits_of_natDegree_le
      hp_nonneg hno hrs hμ
      (lowerCredit := 0) (upperCredit := U)
      (by simp)
      (by simpa [upperTail] using hupper_count)
      (by
        have hP_le : P.natDegree < L + G + U := hP_natDegree_lt.trans_le hq_bound
        exact (by simpa [P, G] using (by lia : P.natDegree ≤ 0 + G + U)))
  · exact hpair.xSub_splits_of_roots_sort_of_tail_credits_of_natDegree_le
      hp_nonneg hno hrs hμ
      (lowerCredit := 0) (upperCredit := U)
      (by simp)
      (by simpa [upperTail] using hupper_count)
      (by
        have hP_le : P.natDegree < L + G + U := hP_natDegree_lt.trans_le hq_bound
        exact (by simpa [P, G] using (by lia : P.natDegree ≤ 0 + G + U)))
  · have hlower_credit : 1 ≤ lowerTail := by
      simpa [L, lowerTail, P, hL] using
        hpair.one_le_card_xSub_le_of_card_right_roots_lt_head_eq_two
          hq_nonneg hno hhead.1 hhead.2 hdeg (by simpa [L] using hL) hμ
    exact hpair.xSub_splits_of_roots_sort_of_tail_credits_of_natDegree_le
      hp_nonneg hno hrs hμ
      (lowerCredit := 1) (upperCredit := U)
      (by simpa [lowerTail] using hlower_credit)
      (by simpa [upperTail] using hupper_count)
      (by
        have hP_le : P.natDegree < L + G + U := hP_natDegree_lt.trans_le hq_bound
        exact (by simpa [P, G] using (by lia : P.natDegree ≤ 1 + G + U)))

/-- Right-successor sorted-root count endpoint with nonnegative coefficients.
The sign of the top coefficient decides which exterior-tail transfer supplies
the missing credits. -/
theorem PositiveSplitRootCountPair.xSub_splits_of_roots_sort_of_right_successor_nonneg
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hq_nonneg : HasNonnegCoeffs q)
    (hno : NoCommonRoots p q) {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs)
    (hdeg : q.natDegree = p.natDegree + 1) (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  rcases lt_trichotomy (p.leadingCoeff - μ * q.leadingCoeff) 0 with
    hlt | heq | hgt
  · exact
      hpair.xSub_splits_of_roots_sort_of_right_successor_nonneg_of_top_coeff_neg
        hp_nonneg hq_nonneg hno hrs hdeg hlt hμ
  · exact
      hpair.xSub_splits_of_roots_sort_of_right_successor_nonneg_of_top_coeff_zero
        hp_nonneg hq_nonneg hno hrs hdeg heq hμ
  · exact
      hpair.xSub_splits_of_roots_sort_of_right_successor_nonneg_of_top_coeff_pos
        hp_nonneg hq_nonneg hno hrs hdeg hgt hμ

/-- No-common-root branch of the right-successor x-subtraction family, in the
unshifted `p, q` form.  If `p` has at least two distinct roots, the sorted-root
count endpoint applies directly.  If it has at most one distinct root, the
exterior-tail bounds force `q.natDegree ≤ 3`, so the existing cubic endpoint
applies. -/
theorem PositiveSplitRootCountPair.xSub_splits_of_right_successor_nonneg_of_noCommonRoots
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hq_nonneg : HasNonnegCoeffs q)
    (hno : NoCommonRoots p q)
    (hdeg : q.natDegree = p.natDegree + 1) {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  cases hrs : p.roots.toFinset.sort (· ≤ ·) with
  | nil =>
      have hroots_zero : p.roots = 0 := by
        apply Multiset.eq_zero_of_forall_notMem
        intro x hx
        have hx_sort : x ∈ p.roots.toFinset.sort (· ≤ ·) := by
          rw [Finset.mem_sort, Multiset.mem_toFinset]
          exact hx
        rw [hrs] at hx_sort
        simp at hx_sort
      have hpdeg_zero : p.natDegree = 0 := by
        rw [← card_roots_of_splits hpair.left_splits, hroots_zero]
        simp
      have hqdeg_one : q.natDegree = 1 := by lia
      have hp_nonneg_zero : HasNonnegCoeffs (p.comp (X + C (0 : ℝ))) := by simpa using hp_nonneg
      have hq_nonneg_zero : HasNonnegCoeffs (q.comp (X + C (0 : ℝ))) := by simpa using hq_nonneg
      simpa using
        positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one
          (f := p) (g := q) (r := 0)
          hpair hp_nonneg_zero hq_nonneg_zero hdeg hqdeg_one μ hμ
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
          let L := (q.roots.filter (fun x => x < a)).card
          let U := (q.roots.filter (a < ·)).card
          have hq_bound : q.natDegree ≤ L + U := by
            have hbound :=
              hpair.right_natDegree_le_lower_sum_min_two_upper_of_roots_sort
                hno (a := a) (xs := []) hrs_single
            simpa [L, U] using hbound
          have hL_le : L ≤ 2 := by
            simpa [L] using
              hpair.card_right_roots_filter_lt_le_two_of_roots_ge_of_right_successor
                hhead.2 hdeg
          have hU_le : U ≤ 1 := by
            simpa [U] using
              hpair.card_right_roots_filter_gt_le_one_of_left_largest_root
                ha_largest
          have hqdeg_le : q.natDegree ≤ 3 := by lia
          have hp_nonneg_zero : HasNonnegCoeffs (p.comp (X + C (0 : ℝ))) := by
            simpa using hp_nonneg
          have hq_nonneg_zero : HasNonnegCoeffs (q.comp (X + C (0 : ℝ))) := by
            simpa using hq_nonneg
          simpa using
            positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three
              (f := p) (g := q) (r := 0)
              hpair hp_nonneg_zero hq_nonneg_zero hdeg hqdeg_le μ hμ
      | cons b ys =>
          have hrs_two :
              p.roots.toFinset.sort (· ≤ ·) = a :: b :: ys := by
            simpa [hxs] using hrs
          exact hpair.xSub_splits_of_roots_sort_of_right_successor_nonneg
            hp_nonneg hq_nonneg hno hrs_two hdeg hμ

/-- Right-successor x-subtraction family in unshifted positive-split form,
allowing common roots.  The proof peels common roots by strong induction on the
right endpoint degree and dispatches the reduced branch to the no-common-root
theorem. -/
theorem PositiveSplitRootCountPair.xSub_splits_of_right_successor_nonneg
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hq_nonneg : HasNonnegCoeffs q)
    (hdeg : q.natDegree = p.natDegree + 1) {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  let P : ℕ → Prop := fun n =>
    ∀ {p q : ℝ[X]},
      q.natDegree = n →
      PositiveSplitRootCountPair p q →
      HasNonnegCoeffs p →
      HasNonnegCoeffs q →
      q.natDegree = p.natDegree + 1 →
      ∀ μ : ℝ, 0 < μ → (X * p - C μ * q).Splits
  have hmain : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro p q hqdeg hpair hp_nonneg hq_nonneg hdeg μ hμ
        by_cases hno : NoCommonRoots p q
        · exact hpair.xSub_splits_of_right_successor_nonneg_of_noCommonRoots
            hp_nonneg hq_nonneg hno hdeg hμ
        · rcases exists_common_root_of_not_noCommonRoots hno with
            ⟨r, hp_root, hq_root⟩
          have hpair_delete :
              PositiveSplitRootCountPair (deleteRootFactor p r)
                (deleteRootFactor q r) :=
            hpair.deleteRootFactor_commonRoot hp_root hq_root
          have hp_delete_nonneg :
              HasNonnegCoeffs (deleteRootFactor p r) :=
            hpair.left_deleteRootFactor_nonneg hp_nonneg hp_root
          have hq_delete_nonneg :
              HasNonnegCoeffs (deleteRootFactor q r) :=
            hpair.right_deleteRootFactor_nonneg hq_nonneg hq_root
          have hdeg_delete :
              (deleteRootFactor q r).natDegree =
                (deleteRootFactor p r).natDegree + 1 :=
            hpair.natDegree_deleteRootFactor_right_eq_left_add_one
              hp_root hdeg
          have hq_delete_lt :
              (deleteRootFactor q r).natDegree < n := by
            rw [natDegree_deleteRootFactor, hqdeg]
            have hq_pos : 0 < n := by
              simpa [← hqdeg] using
                natDegree_pos_of_isRoot hpair.right_pos.ne_zero hq_root
            lia
          have hcofactor :
              (X * deleteRootFactor p r -
                C μ * deleteRootFactor q r).Splits :=
            ih (deleteRootFactor q r).natDegree hq_delete_lt
              (rfl : (deleteRootFactor q r).natDegree =
                (deleteRootFactor q r).natDegree)
              hpair_delete hp_delete_nonneg hq_delete_nonneg hdeg_delete μ hμ
          exact
            (X_mul_sub_C_mul_splits_iff_deleteRootFactor_splits_of_commonRoot
              hp_root hq_root).mpr hcofactor
  exact hmain q.natDegree rfl hpair hp_nonneg hq_nonneg hdeg μ hμ

/-- Unrestricted positive-split right-successor translated x-subtraction
family. -/
theorem positiveSplitRightSuccDegreeTranslatedXSubRightFamily :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement := by
  intro f g r hpair hfnn hgnn hdeg μ hμ
  let p := f.comp (X + C r)
  let q := g.comp (X + C r)
  have hpair_shift : PositiveSplitRootCountPair p q := by simpa [p, q] using hpair.comp_X_add_C r
  have hdeg_shift : q.natDegree = p.natDegree + 1 := by
    simpa [p, q, Polynomial.natDegree_comp] using hdeg
  simpa [p, q] using
    hpair_shift.xSub_splits_of_right_successor_nonneg
      hfnn hgnn hdeg_shift hμ

/-- The proved right-successor x-subtraction family gives every predicate
restriction. -/
theorem positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate
    {P : ℕ → Prop} :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement P :=
  positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement_of_imp
    (fun _ _ => trivial)
    (positiveSplitTranslatedXSubRightFamilyPredicateRelation_true_of_relation
      positiveSplitRightSuccDegreeTranslatedXSubRightFamily)

end LiuOppositeSigns
end RealRooted
