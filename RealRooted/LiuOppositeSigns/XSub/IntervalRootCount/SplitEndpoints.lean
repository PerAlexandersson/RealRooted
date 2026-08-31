import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.UpperTail

/-!
# Liu x-subtraction count-to-splitting endpoints.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns
/-- For at least two distinct left-root locations, the closed lower tail at the
first left root, the summed adjacent-gap `min 2` lower bounds, and the closed
upper tail at the last left root fit disjointly inside the full root multiset
of the x-subtraction pencil. -/
theorem
    PositiveSplitRootCountPair.lower_sum_upper_le_card_xSub_roots_of_roots_sort
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) (hμ : 0 < μ) :
    ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card +
        (((a :: b :: xs).zip (b :: xs)).map
          (fun ab => min 2
            (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
      ((X * p - C μ * q).roots.filter
        (fun x => (b :: xs).getLast (List.cons_ne_nil b xs) ≤ x)).card ≤
    (X * p - C μ * q).roots.card := by
  let P := X * p - C μ * q
  let gaps := (a :: b :: xs).zip (b :: xs)
  have hpoint :
      (gaps.map
          (fun ab => min 2
            (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum ≤
        (gaps.map
          (fun ab => (P.roots.filter
            (fun x => ab.1 < x ∧ x < ab.2)).card)).sum := by
    simpa [gaps, P, hrs] using
      hpair.sum_min_two_right_roots_le_sum_xSub_roots_Ioo hp_nonneg hno hμ
  have hchain : (a :: b :: xs).IsChain (· < ·) := by
    have hpair_rs :
        (p.roots.toFinset.sort (· ≤ ·)).Pairwise (· < ·) :=
      (Finset.sortedLT_sort p.roots.toFinset).pairwise
    have hchain_rs : (p.roots.toFinset.sort (· ≤ ·)).IsChain (· < ·) :=
      hpair_rs.isChain
    simpa [hrs] using hchain_rs
  have hpack :=
    card_filter_le_add_sum_card_filter_Ioo_zip_tail_add_card_filter_ge_getLast_le_card
      (s := P.roots) hchain
  have hmono :
      (P.roots.filter (fun x => x ≤ a)).card +
          (gaps.map
            (fun ab => min 2
              (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
        (P.roots.filter
          (fun x => (b :: xs).getLast (List.cons_ne_nil b xs) ≤ x)).card ≤
      (P.roots.filter (fun x => x ≤ a)).card +
          (gaps.map
            (fun ab => (P.roots.filter
              (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
        (P.roots.filter
          (fun x => (b :: xs).getLast (List.cons_ne_nil b xs) ≤ x)).card :=
    Nat.add_le_add (Nat.add_le_add_left hpoint _) le_rfl
  exact le_trans hmono (by simpa [P, gaps] using hpack)

/-- If the lower and upper tails of the x-subtraction pencil each contain a root,
then the full root multiset contains one lower-tail root, the summed adjacent-gap
`min 2` roots, and one upper-tail root. -/
theorem PositiveSplitRootCountPair.one_sum_one_le_card_xSub_roots_of_roots_sort_of_tail_counts
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) (hμ : 0 < μ)
    (hlower_one : 1 ≤ ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card)
    (hupper_one :
      1 ≤ ((X * p - C μ * q).roots.filter
        (fun x => (b :: xs).getLast (List.cons_ne_nil b xs) ≤ x)).card) :
    1 +
        (((a :: b :: xs).zip (b :: xs)).map
          (fun ab => min 2
            (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
      1 ≤
    (X * p - C μ * q).roots.card := by
  let last := (b :: xs).getLast (List.cons_ne_nil b xs)
  let P := X * p - C μ * q
  let gapSum :=
    (((a :: b :: xs).zip (b :: xs)).map
      (fun ab => min 2
        (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum
  let lowerTail := (P.roots.filter (fun x => x ≤ a)).card
  let upperTail := (P.roots.filter (fun x => last ≤ x)).card
  have hpack :=
    hpair.lower_sum_upper_le_card_xSub_roots_of_roots_sort
      hp_nonneg hno hrs hμ
  have hmono : 1 + gapSum + 1 ≤ lowerTail + gapSum + upperTail :=
    Nat.add_le_add (Nat.add_le_add (by simpa [lowerTail, P] using hlower_one) le_rfl)
      (by simpa [upperTail, last, P] using hupper_one)
  exact le_trans hmono (by simpa [lowerTail, upperTail, gapSum, last, P] using hpack)

/-- A flexible count-to-splitting endpoint for the adjacent-gap route.  It is
the same packing argument as
`xSub_splits_of_roots_sort_of_tail_counts_of_natDegree_le`, but the lower and
upper exterior tails can contribute arbitrary certified credits. -/
theorem
    PositiveSplitRootCountPair.xSub_splits_of_roots_sort_of_tail_credits_of_natDegree_le
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) (hμ : 0 < μ)
    {lowerCredit upperCredit : ℕ}
    (hlower_credit :
      lowerCredit ≤
        ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card)
    (hupper_credit :
      upperCredit ≤
        ((X * p - C μ * q).roots.filter
          (fun x => (b :: xs).getLast (List.cons_ne_nil b xs) ≤ x)).card)
    (hdeg :
      (X * p - C μ * q).natDegree ≤
        lowerCredit +
          (((a :: b :: xs).zip (b :: xs)).map
            (fun ab => min 2
              (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
        upperCredit) :
    (X * p - C μ * q).Splits := by
  let P := X * p - C μ * q
  let last := (b :: xs).getLast (List.cons_ne_nil b xs)
  let G :=
    (((a :: b :: xs).zip (b :: xs)).map
      (fun ab => min 2
        (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum
  let lowerTail := (P.roots.filter (fun x => x ≤ a)).card
  let upperTail := (P.roots.filter (fun x => last ≤ x)).card
  have hpack :
      lowerTail + G + upperTail ≤ P.roots.card := by
    simpa [lowerTail, upperTail, G, last, P] using
      hpair.lower_sum_upper_le_card_xSub_roots_of_roots_sort
        hp_nonneg hno hrs hμ
  have hcount : lowerCredit + G + upperCredit ≤ P.roots.card := by
    have hmono : lowerCredit + G + upperCredit ≤ lowerTail + G + upperTail :=
      Nat.add_le_add
        (Nat.add_le_add (by simpa [lowerTail, P] using hlower_credit) le_rfl)
        (by simpa [upperTail, last, P] using hupper_credit)
    exact hmono.trans hpack
  exact Polynomial.splits_of_le_roots_of_natDegree_le_card
    (s := P.roots) le_rfl (by simpa [G, P] using hdeg.trans hcount)

/-- The full tail-gap-tail count gives splitting once it reaches the natural
degree of the x-subtraction pencil.  This is the count-to-splitting endpoint for
the adjacent-gap route; the remaining arithmetic work is to supply `hdeg` from
the appropriate Liu branch hypotheses. -/
theorem
    PositiveSplitRootCountPair.xSub_splits_of_roots_sort_of_tail_counts_of_natDegree_le
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) (hμ : 0 < μ)
    (hlower_one : 1 ≤ ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card)
    (hupper_one :
      1 ≤ ((X * p - C μ * q).roots.filter
        (fun x => (b :: xs).getLast (List.cons_ne_nil b xs) ≤ x)).card)
    (hdeg :
      (X * p - C μ * q).natDegree ≤
        1 +
          (((a :: b :: xs).zip (b :: xs)).map
            (fun ab => min 2
              (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
        1) :
    (X * p - C μ * q).Splits := by
  have hcount :=
    hpair.one_sum_one_le_card_xSub_roots_of_roots_sort_of_tail_counts
      hp_nonneg hno hrs hμ hlower_one hupper_one
  exact Polynomial.splits_of_le_roots_of_natDegree_le_card
    (s := (X * p - C μ * q).roots) le_rfl (hdeg.trans hcount)

/-- Count-to-splitting endpoint with the standard Liu x-subtraction degree bound.
It remains to show that the tail-gap-tail count reaches `p.natDegree + 1`. -/
theorem
    PositiveSplitRootCountPair.xSub_splits_of_roots_sort_of_tail_counts_of_left_natDegree
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) (hμ : 0 < μ)
    (hlower_one : 1 ≤ ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card)
    (hupper_one :
      1 ≤ ((X * p - C μ * q).roots.filter
        (fun x => (b :: xs).getLast (List.cons_ne_nil b xs) ≤ x)).card)
    (hcount_degree :
      p.natDegree + 1 ≤
        1 +
          (((a :: b :: xs).zip (b :: xs)).map
            (fun ab => min 2
              (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
        1) :
    (X * p - C μ * q).Splits :=
  hpair.xSub_splits_of_roots_sort_of_tail_counts_of_natDegree_le
    hp_nonneg hno hrs hμ hlower_one hupper_one
    ((hpair.natDegree_X_mul_sub_C_mul_le_left_natDegree_add_one μ).trans hcount_degree)

/-- Count-to-splitting endpoint from a variable upper exterior-tail count.  The
upper tail is allowed to contribute the strict right-root tail above the largest
left root, plus one additional x-subtraction root. -/
theorem
    PositiveSplitRootCountPair.xSub_splits_of_roots_sort_of_upper_tail_count
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) (hμ : 0 < μ)
    (hdeg : p.natDegree = q.natDegree + 1)
    (hlower_one : 1 ≤ ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card)
    (hupper_count :
      (q.roots.filter ((b :: xs).getLast (List.cons_ne_nil b xs) < ·)).card + 1 ≤
        ((X * p - C μ * q).roots.filter
          (fun x => (b :: xs).getLast (List.cons_ne_nil b xs) ≤ x)).card) :
    (X * p - C μ * q).Splits := by
  let P := X * p - C μ * q
  let last := (b :: xs).getLast (List.cons_ne_nil b xs)
  let G :=
    (((a :: b :: xs).zip (b :: xs)).map
      (fun ab => min 2
        (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum
  let U := (q.roots.filter (last < ·)).card
  let lowerTail := (P.roots.filter (fun x => x ≤ a)).card
  let upperTail := (P.roots.filter (fun x => last ≤ x)).card
  have hupper_count' : U + 1 ≤ upperTail := by simpa [U, upperTail, last, P] using hupper_count
  have hpack :
      lowerTail + G + upperTail ≤ P.roots.card := by
    simpa [lowerTail, upperTail, G, last, P] using
      hpair.lower_sum_upper_le_card_xSub_roots_of_roots_sort
        hp_nonneg hno hrs hμ
  have hcount : 1 + G + (U + 1) ≤ P.roots.card := by
    have hmono : 1 + G + (U + 1) ≤ lowerTail + G + upperTail :=
      Nat.add_le_add (Nat.add_le_add (by simpa [lowerTail, P] using hlower_one) le_rfl)
        hupper_count'
    exact hmono.trans hpack
  have hq_bound : q.natDegree ≤ G + U := by
    simpa [G, U, last] using
      hpair.right_natDegree_le_sum_min_two_add_card_right_roots_gt_getLast
        hno (a := a) (xs := b :: xs) (by simpa using hrs) hdeg
  have hdegree : P.natDegree ≤ 1 + G + (U + 1) := by
    have hP_deg := hpair.natDegree_X_mul_sub_C_mul_le_left_natDegree_add_one μ
    have htarget : p.natDegree + 1 ≤ 1 + G + (U + 1) := by lia
    exact hP_deg.trans htarget
  exact Polynomial.splits_of_le_roots_of_natDegree_le_card
    (s := P.roots) le_rfl (hdegree.trans hcount)

/-- Count-to-splitting endpoint using the nonpositive upper exterior-tail
transfer.  This version includes the endpoint-zero branch. -/
theorem
    PositiveSplitRootCountPair.xSub_splits_of_roots_sort_of_upper_nonpos_tail_transfer
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) (hμ : 0 < μ)
    (hdeg : p.natDegree = q.natDegree + 1)
    (hlower_one : 1 ≤ ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card)
    (hupper_nonpos :
      ∀ y ∈ q.roots,
        (b :: xs).getLast (List.cons_ne_nil b xs) < y → y ≤ 0)
    (htop : Tendsto (fun x => (X * p - C μ * q).eval x) atTop atTop) :
    (X * p - C μ * q).Splits := by
  let P := X * p - C μ * q
  let last := (b :: xs).getLast (List.cons_ne_nil b xs)
  have hlast : IsLargestRoot p last := by
    simpa [last] using isLargestRoot_getLast_of_roots_toFinset_sort_eq_cons_cons
      hpair.left_pos.ne_zero hrs
  have hupper_count :
      (q.roots.filter (last < ·)).card + 1 ≤
        (P.roots.filter (fun x => last ≤ x)).card := by
    simpa [last, P] using
      hpair.upper_nonpos_tail_add_one_le_card_xSub_ge
        hno hlast hμ (by rw [hdeg]; exact Nat.le_succ _)
        hupper_nonpos htop
  exact hpair.xSub_splits_of_roots_sort_of_upper_tail_count
    hp_nonneg hno hrs hμ hdeg hlower_one (by simpa [last, P] using hupper_count)

end LiuOppositeSigns
end RealRooted
