module

import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.SplitEndpoints
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.UpperTail
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.GapCounts
import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.RootFilters
import RealRooted.LiuOppositeSigns.XSub.SameDegree
public import RealRooted.LiuOppositeSigns.NoCommonRoots
public import RealRooted.LiuOppositeSigns.PositiveSplitRootCount
import RealRooted.Mathlib.Algebra.Polynomial.Splits

/-!
# Liu x-subtraction same-degree endpoint.
-/

public section

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
  have hupper_nonpos : ∀ y ∈ q.roots, last < y → y ≤ 0 :=
    fun y hy _ => roots_nonpos_of_hasNonnegCoeffs hq_nonneg y hy
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

/-- The exterior-tail credits close the same-degree endpoint
when the left root list has a single distinct location. -/
private lemma splits_of_extremal_left_root_same_degree {p q : ℝ[X]}
    (hpair : PositiveSplitRootCountPair p q) (hq_nonneg : HasNonnegCoeffs q)
    (hno : NoCommonRoots p q) {a μ : ℝ}
    (hhead : p.IsRoot a ∧ ∀ r ∈ p.roots, a ≤ r)
    (ha_largest : IsLargestRoot p a) (hdeg : p.natDegree = q.natDegree) (hμ : 0 < μ)
    (hq_bound : q.natDegree ≤
      (q.roots.filter (fun x => x < a)).card + (q.roots.filter (a < ·)).card) :
    (X * p - C μ * q).Splits := by
  let L := (q.roots.filter (fun x => x < a)).card
  let U := (q.roots.filter (a < ·)).card
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
    (by rw [hdeg]) μ
  have hdegree : P.natDegree = p.natDegree + 1 := hdata.2
  have htop : Tendsto (fun x => P.eval x) atTop atTop :=
    P.tendsto_atTop_of_leadingCoeff_nonneg
      (natDegree_pos_iff_degree_pos.mp (by rw [hdegree]; exact Nat.succ_pos _))
      hdata.1.le
  have hlo : L ≤ lowerTail := hpair.card_right_roots_lt_head_le_card_xSub_le
    hno hhead.1 hhead.2 hdeg hμ
  have hup : U + 1 ≤ upperTail := hpair.upper_nonpos_tail_add_one_le_card_xSub_ge
    hno ha_largest hμ (by rw [hdeg]) hupper_nonpos htop
  exact Polynomial.splits_of_le_roots_of_natDegree_le_card (s := P.roots)
    le_rfl (by rw [hdegree]; lia)

/-- No-common-root branch of the same-degree x-subtraction family, in the
unshifted `p, q` form.  If `p` has at least two distinct roots, the sorted-root
count endpoint applies directly.  If it has at most one distinct root, the
same lower and upper exterior-tail credits account for every root directly. -/
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
        rw [← Polynomial.splits_iff_card_roots.mp hpair.left_splits, hroots_zero]
        simp
      have hqdeg_zero : q.natDegree = 0 := by lia
      simpa using
        positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
          (f := p) (g := q) (r := 0)
          hdeg hqdeg_zero μ hμ
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
            exact hbound
          exact splits_of_extremal_left_root_same_degree
            hpair hq_nonneg hno hhead ha_largest hdeg hμ
            hq_bound
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
    (X * p - C μ * q).Splits :=
  hpair.xSub_splits_of_forall_noCommonRoots (a := 0) (b := 0)
    (fun hpair hp hq hno hdeg _ hμ =>
      hpair.xSub_splits_of_same_degree_nonneg_of_noCommonRoots hp hq hno hdeg hμ)
    hp_nonneg hq_nonneg hdeg hμ

/-- Same-degree translated x-subtraction family. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily {f g : ℝ[X]} (r : ℝ)
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree) (μ : ℝ) (hμ : 0 < μ) :
    (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  let p := f.comp (X + C r)
  let q := g.comp (X + C r)
  have hpair_shift : PositiveSplitRootCountPair p q := by simpa [p, q] using hpair.comp_X_add_C r
  have hdeg_shift : p.natDegree = q.natDegree := by
    simpa [p, q, Polynomial.natDegree_comp] using hdeg
  simpa [p, q] using
    hpair_shift.xSub_splits_of_same_degree_nonneg hfnn hgnn hdeg_shift hμ

end LiuOppositeSigns
end RealRooted
