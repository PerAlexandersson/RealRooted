import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.SplitEndpoints

/-!
# Liu x-subtraction same-degree endpoint.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns
/-- In the same-degree case, the sorted-root count endpoint proves splitting
whenever the left endpoint has at least two distinct root locations and both
endpoint polynomials have nonnegative coefficients.

The lower tail may contain one strict right-endpoint root below the first left
root.  The same-degree lower-tail transfer accounts for that root, while the
upper nonpositive-tail transfer supplies the strict upper right-root tail plus
one additional x-subtraction root. -/
theorem
    PositiveSplitRootCountPair.xSub_splits_of_roots_sort_of_same_degree_nonneg
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hq_nonneg : HasNonnegCoeffs q)
    (hno : NoCommonRoots p q) {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs)
    (hdeg : p.natDegree = q.natDegree) (hμ : 0 < μ) :
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
  have hP_data :=
    hpair.posLeadingCoeff_and_natDegree_X_mul_sub_C_mul_of_right_natDegree_le
      (by rw [hdeg]) μ
  have hP_pos : HasPosLeadingCoeff P := by simpa [P] using hP_data.1
  have hP_natDegree : P.natDegree = p.natDegree + 1 := by simpa [P] using hP_data.2
  have hP_nat_pos : 0 < P.natDegree := by
    rw [hP_natDegree]
    exact Nat.succ_pos _
  have hP_degree_pos : 0 < P.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hP_nat_pos
  have htop : Tendsto (fun x => P.eval x) atTop atTop :=
    P.tendsto_atTop_of_leadingCoeff_nonneg hP_degree_pos hP_pos.le
  have hlower_count : L ≤ lowerTail := by
    simpa [L, lowerTail, P] using
      hpair.card_right_roots_lt_head_le_card_xSub_le
        hno hhead.1 hhead.2 hdeg hμ
  have hupper_nonpos : ∀ y ∈ q.roots, last < y → y ≤ 0 := by
    intro y hy _hy
    exact roots_nonpos_of_hasNonnegCoeffs hq_nonneg y hy
  have hupper_count : U + 1 ≤ upperTail := by
    simpa [U, upperTail, last, P] using
      hpair.upper_nonpos_tail_add_one_le_card_xSub_ge
        hno hlast hμ (by rw [hdeg]) hupper_nonpos htop
  have hpack :
      lowerTail + G + upperTail ≤ P.roots.card := by
    simpa [lowerTail, upperTail, G, last, P] using
      hpair.lower_sum_upper_le_card_xSub_roots_of_roots_sort
        hp_nonneg hno hrs hμ
  have hq_bound : q.natDegree ≤ L + G + U := by
    simpa [L, G, U, last] using
      hpair.right_natDegree_le_lower_sum_min_two_upper_of_roots_sort
        hno (a := a) (xs := b :: xs) (by simpa using hrs)
  have hcount : L + G + (U + 1) ≤ P.roots.card := by
    have hmono : L + G + (U + 1) ≤ lowerTail + G + upperTail :=
      Nat.add_le_add (Nat.add_le_add hlower_count le_rfl) hupper_count
    exact hmono.trans hpack
  have hdegree : P.natDegree ≤ L + G + (U + 1) := by
    rw [hP_natDegree]
    lia
  exact Polynomial.splits_of_le_roots_of_natDegree_le_card
    (s := P.roots) le_rfl (hdegree.trans hcount)

/-- No-common-root branch of the same-degree x-subtraction family, in the
unshifted `p, q` form.  If `p` has at least two distinct roots, the sorted-root
count endpoint applies directly.  If it has at most one distinct root, the
exterior-tail bounds force `q.natDegree ≤ 2`, so the existing quadratic
endpoint applies. -/
theorem PositiveSplitRootCountPair.xSub_splits_of_same_degree_nonneg_of_noCommonRoots
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hq_nonneg : HasNonnegCoeffs q)
    (hno : NoCommonRoots p q)
    (hdeg : p.natDegree = q.natDegree) {μ : ℝ} (hμ : 0 < μ) :
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
      have hqdeg_zero : q.natDegree = 0 := by lia
      have hp_nonneg_zero : HasNonnegCoeffs (p.comp (X + C (0 : ℝ))) := by simpa using hp_nonneg
      have hq_nonneg_zero : HasNonnegCoeffs (q.comp (X + C (0 : ℝ))) := by simpa using hq_nonneg
      simpa using
        positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
          (f := p) (g := q) (r := 0)
          hpair hp_nonneg_zero hq_nonneg_zero hdeg hqdeg_zero μ hμ
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
          have hL_le : L ≤ 1 := by
            simpa [L] using
              hpair.card_right_roots_filter_lt_le_one_of_left_roots_ge_of_natDegree_eq
                hhead.2 hdeg
          have hU_le : U ≤ 1 := by
            simpa [U] using
              hpair.card_right_roots_filter_gt_le_one_of_left_largest_root
                ha_largest
          have hqdeg_le : q.natDegree ≤ 2 := by lia
          have hp_nonneg_zero : HasNonnegCoeffs (p.comp (X + C (0 : ℝ))) := by
            simpa using hp_nonneg
          have hq_nonneg_zero : HasNonnegCoeffs (q.comp (X + C (0 : ℝ))) := by
            simpa using hq_nonneg
          simpa using
            positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
              (f := p) (g := q) (r := 0)
              hpair hp_nonneg_zero hq_nonneg_zero hdeg hqdeg_le μ hμ
      | cons b ys =>
          have hrs_two :
              p.roots.toFinset.sort (· ≤ ·) = a :: b :: ys := by
            simpa [hxs] using hrs
          exact hpair.xSub_splits_of_roots_sort_of_same_degree_nonneg
            hp_nonneg hq_nonneg hno hrs_two hdeg hμ

/-- Same-degree x-subtraction family in unshifted positive-split form, allowing
common roots.  The proof peels common roots by strong induction on the right
endpoint degree and dispatches the reduced branch to the no-common-root theorem.
-/
theorem PositiveSplitRootCountPair.xSub_splits_of_same_degree_nonneg
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hq_nonneg : HasNonnegCoeffs q)
    (hdeg : p.natDegree = q.natDegree) {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  let P : ℕ → Prop := fun n =>
    ∀ {p q : ℝ[X]},
      q.natDegree = n →
      PositiveSplitRootCountPair p q →
      HasNonnegCoeffs p →
      HasNonnegCoeffs q →
      p.natDegree = q.natDegree →
      ∀ μ : ℝ, 0 < μ → (X * p - C μ * q).Splits
  have hmain : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro p q hqdeg hpair hp_nonneg hq_nonneg hdeg μ hμ
        by_cases hno : NoCommonRoots p q
        · exact hpair.xSub_splits_of_same_degree_nonneg_of_noCommonRoots
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
              (deleteRootFactor p r).natDegree =
                (deleteRootFactor q r).natDegree :=
            hpair.natDegree_deleteRootFactor_eq hdeg
          have hq_delete_lt :
              (deleteRootFactor q r).natDegree < n := by
            rw [natDegree_deleteRootFactor, hqdeg]
            have hq_pos : 0 < n := by
              simpa [← hqdeg] using
                natDegree_pos_of_isRoot hpair.right_pos.ne_zero hq_root
            lia
          have hsplit_delete :
              (X * deleteRootFactor p r -
                C μ * deleteRootFactor q r).Splits :=
            ih (deleteRootFactor q r).natDegree hq_delete_lt
              (rfl : (deleteRootFactor q r).natDegree =
                (deleteRootFactor q r).natDegree)
              hpair_delete hp_delete_nonneg hq_delete_nonneg
              hdeg_delete μ hμ
          exact
            (X_mul_sub_C_mul_splits_iff_deleteRootFactor_splits_of_commonRoot
              hp_root hq_root).mpr hsplit_delete
  exact hmain q.natDegree rfl hpair hp_nonneg hq_nonneg hdeg μ hμ

/-- Same-degree translated x-subtraction family. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily :
    positiveSplitSameDegreeTranslatedXSubRightFamilyStatement := by
  intro f g r hpair hfnn hgnn hdeg μ hμ
  let p := f.comp (X + C r)
  let q := g.comp (X + C r)
  have hpair_shift : PositiveSplitRootCountPair p q := by simpa [p, q] using hpair.comp_X_add_C r
  have hdeg_shift : p.natDegree = q.natDegree := by
    simpa [p, q, Polynomial.natDegree_comp] using hdeg
  simpa [p, q] using
    hpair_shift.xSub_splits_of_same_degree_nonneg hfnn hgnn hdeg_shift hμ

/-- Same-degree translated x-subtraction family packaged with an arbitrary
right-degree predicate. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate
    (P : ℕ → Prop) :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement P :=
    positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement_of_imp
    (fun _ _ => trivial)
    (positiveSplitTranslatedXSubRightFamilyPredicateRelation_true_of_relation
      positiveSplitSameDegreeTranslatedXSubRightFamily)

end LiuOppositeSigns
end RealRooted
