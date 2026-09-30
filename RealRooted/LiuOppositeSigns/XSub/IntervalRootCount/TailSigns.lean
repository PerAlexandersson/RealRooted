import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.SplitEndpoints

/-!
# Liu x-subtraction endpoint-sign tail certificates.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns
/-- If the x-subtraction pencil has the nonnegative-sign lower-tail witness at
the first left root and the nonnegative-sign upper-tail witness at the last
left root, then the full root multiset contains one lower-tail root, the
summed adjacent-gap `min 2` roots, and one upper-tail root. -/
theorem
    PositiveSplitRootCountPair.one_sum_one_le_card_xSub_roots_of_roots_sort_of_q_nonneg_nonneg
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) (hμ : 0 < μ)
    (hq_first : 0 ≤ q.eval a)
    (hbot : Tendsto (fun x => (X * p - C μ * q).eval x) atBot atTop)
    (hq_last : 0 ≤ q.eval ((b :: xs).getLast (List.cons_ne_nil b xs)))
    (htop : Tendsto (fun x => (X * p - C μ * q).eval x) atTop atTop) :
    1 +
        (((a :: b :: xs).zip (b :: xs)).map
          (fun ab => min 2
            (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
      1 ≤
    (X * p - C μ * q).roots.card := by
  let last := (b :: xs).getLast (List.cons_ne_nil b xs)
  let P := X * p - C μ * q
  let lowerTail := (P.roots.filter (fun x => x ≤ a)).card
  let upperTail := (P.roots.filter (fun x => last ≤ x)).card
  have ha_mem : a ∈ p.roots.toFinset.sort (· ≤ ·) := by simp [hrs]
  have ha : p.IsRoot a := by
    rw [Finset.mem_sort, Multiset.mem_toFinset] at ha_mem
    exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp ha_mem
  have hlast_mem_tail : last ∈ b :: xs :=
    List.getLast_mem (List.cons_ne_nil b xs)
  have hlast_mem : last ∈ p.roots.toFinset.sort (· ≤ ·) := by
    rw [hrs]
    exact List.mem_cons.mpr (Or.inr hlast_mem_tail)
  have hlast : p.IsRoot last := by
    rw [Finset.mem_sort, Multiset.mem_toFinset] at hlast_mem
    exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp hlast_mem
  have hP_ne : P ≠ 0 :=
    hno.xSub_ne_zero_of_left_root ha hμ.ne'
  have hlower_one : 1 ≤ lowerTail := by
    simpa [lowerTail, P] using
      one_le_card_xSub_roots_filter_le_of_left_root_right_eval_nonneg
        ha hq_first hμ hP_ne hbot
  have hupper_one : 1 ≤ upperTail := by
    simpa [upperTail, last, P] using
      one_le_card_xSub_roots_filter_ge_of_left_root_right_eval_nonneg
        hlast hq_last hμ hP_ne htop
  exact hpair.one_sum_one_le_card_xSub_roots_of_roots_sort_of_tail_counts
    hp_nonneg hno hrs hμ
    (by simpa [lowerTail, P] using hlower_one)
    (by simpa [upperTail, last, P] using hupper_one)

/-- If the x-subtraction pencil has the nonpositive-sign lower-tail witness at
the first left root and the nonnegative-sign upper-tail witness at the last
left root, then the full root multiset contains one lower-tail root, the
summed adjacent-gap `min 2` roots, and one upper-tail root. -/
theorem
    PositiveSplitRootCountPair.one_sum_one_le_card_xSub_roots_of_roots_sort_of_q_nonpos_nonneg
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) (hμ : 0 < μ)
    (hq_first : q.eval a ≤ 0)
    (hbot : Tendsto (fun x => (X * p - C μ * q).eval x) atBot atBot)
    (hq_last : 0 ≤ q.eval ((b :: xs).getLast (List.cons_ne_nil b xs)))
    (htop : Tendsto (fun x => (X * p - C μ * q).eval x) atTop atTop) :
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
  have ha_mem : a ∈ p.roots.toFinset.sort (· ≤ ·) := by simp [hrs]
  have ha : p.IsRoot a := by
    rw [Finset.mem_sort, Multiset.mem_toFinset] at ha_mem
    exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp ha_mem
  have hlast_mem_tail : last ∈ b :: xs :=
    List.getLast_mem (List.cons_ne_nil b xs)
  have hlast_mem : last ∈ p.roots.toFinset.sort (· ≤ ·) := by
    rw [hrs]
    exact List.mem_cons.mpr (Or.inr hlast_mem_tail)
  have hlast : p.IsRoot last := by
    rw [Finset.mem_sort, Multiset.mem_toFinset] at hlast_mem
    exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp hlast_mem
  have hP_ne : P ≠ 0 :=
    hno.xSub_ne_zero_of_left_root ha hμ.ne'
  have hlower_one : 1 ≤ lowerTail := by
    simpa [lowerTail, P] using
      one_le_card_xSub_roots_filter_le_of_left_root_right_eval_nonpos
        ha hq_first hμ hP_ne hbot
  have hupper_one : 1 ≤ upperTail := by
    simpa [upperTail, last, P] using
      one_le_card_xSub_roots_filter_ge_of_left_root_right_eval_nonneg
        hlast hq_last hμ hP_ne htop
  exact hpair.one_sum_one_le_card_xSub_roots_of_roots_sort_of_tail_counts
    hp_nonneg hno hrs hμ
    (by simpa [lowerTail, P] using hlower_one)
    (by simpa [upperTail, last, P] using hupper_one)

/-- If the x-subtraction pencil has the nonnegative-sign lower-tail witness at
the first left root and the nonpositive-sign upper-tail witness at the last
left root, then the full root multiset contains one lower-tail root, the
summed adjacent-gap `min 2` roots, and one upper-tail root. -/
theorem
    PositiveSplitRootCountPair.one_sum_one_le_card_xSub_roots_of_roots_sort_of_q_nonneg_nonpos
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) (hμ : 0 < μ)
    (hq_first : 0 ≤ q.eval a)
    (hbot : Tendsto (fun x => (X * p - C μ * q).eval x) atBot atTop)
    (hq_last : q.eval ((b :: xs).getLast (List.cons_ne_nil b xs)) ≤ 0)
    (htop : Tendsto (fun x => (X * p - C μ * q).eval x) atTop atBot) :
    1 +
        (((a :: b :: xs).zip (b :: xs)).map
          (fun ab => min 2
            (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
      1 ≤
    (X * p - C μ * q).roots.card := by
  let last := (b :: xs).getLast (List.cons_ne_nil b xs)
  let P := X * p - C μ * q
  let lowerTail := (P.roots.filter (fun x => x ≤ a)).card
  let upperTail := (P.roots.filter (fun x => last ≤ x)).card
  have ha_mem : a ∈ p.roots.toFinset.sort (· ≤ ·) := by simp [hrs]
  have ha : p.IsRoot a := by
    rw [Finset.mem_sort, Multiset.mem_toFinset] at ha_mem
    exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp ha_mem
  have hlast_mem_tail : last ∈ b :: xs :=
    List.getLast_mem (List.cons_ne_nil b xs)
  have hlast_mem : last ∈ p.roots.toFinset.sort (· ≤ ·) := by
    rw [hrs]
    exact List.mem_cons.mpr (Or.inr hlast_mem_tail)
  have hlast : p.IsRoot last := by
    rw [Finset.mem_sort, Multiset.mem_toFinset] at hlast_mem
    exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp hlast_mem
  have hP_ne : P ≠ 0 :=
    hno.xSub_ne_zero_of_left_root ha hμ.ne'
  have hlower_one : 1 ≤ lowerTail := by
    simpa [lowerTail, P] using
      one_le_card_xSub_roots_filter_le_of_left_root_right_eval_nonneg
        ha hq_first hμ hP_ne hbot
  have hupper_one : 1 ≤ upperTail := by
    simpa [upperTail, last, P] using
      one_le_card_xSub_roots_filter_ge_of_left_root_right_eval_nonpos
        hlast hq_last hμ hP_ne htop
  exact hpair.one_sum_one_le_card_xSub_roots_of_roots_sort_of_tail_counts
    hp_nonneg hno hrs hμ
    (by simpa [lowerTail, P] using hlower_one)
    (by simpa [upperTail, last, P] using hupper_one)

/-- If the x-subtraction pencil has the nonpositive-sign lower-tail witness at
the first left root and the nonpositive-sign upper-tail witness at the last
left root, then the full root multiset contains one lower-tail root, the
summed adjacent-gap `min 2` roots, and one upper-tail root. -/
theorem
    PositiveSplitRootCountPair.one_sum_one_le_card_xSub_roots_of_roots_sort_of_q_nonpos_nonpos
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) (hμ : 0 < μ)
    (hq_first : q.eval a ≤ 0)
    (hbot : Tendsto (fun x => (X * p - C μ * q).eval x) atBot atBot)
    (hq_last : q.eval ((b :: xs).getLast (List.cons_ne_nil b xs)) ≤ 0)
    (htop : Tendsto (fun x => (X * p - C μ * q).eval x) atTop atBot) :
    1 +
        (((a :: b :: xs).zip (b :: xs)).map
          (fun ab => min 2
            (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
      1 ≤
    (X * p - C μ * q).roots.card := by
  let last := (b :: xs).getLast (List.cons_ne_nil b xs)
  let P := X * p - C μ * q
  let lowerTail := (P.roots.filter (fun x => x ≤ a)).card
  let upperTail := (P.roots.filter (fun x => last ≤ x)).card
  have ha_mem : a ∈ p.roots.toFinset.sort (· ≤ ·) := by simp [hrs]
  have ha : p.IsRoot a := by
    rw [Finset.mem_sort, Multiset.mem_toFinset] at ha_mem
    exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp ha_mem
  have hlast_mem_tail : last ∈ b :: xs :=
    List.getLast_mem (List.cons_ne_nil b xs)
  have hlast_mem : last ∈ p.roots.toFinset.sort (· ≤ ·) := by
    rw [hrs]
    exact List.mem_cons.mpr (Or.inr hlast_mem_tail)
  have hlast : p.IsRoot last := by
    rw [Finset.mem_sort, Multiset.mem_toFinset] at hlast_mem
    exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp hlast_mem
  have hP_ne : P ≠ 0 :=
    hno.xSub_ne_zero_of_left_root ha hμ.ne'
  have hlower_one : 1 ≤ lowerTail := by
    simpa [lowerTail, P] using
      one_le_card_xSub_roots_filter_le_of_left_root_right_eval_nonpos
        ha hq_first hμ hP_ne hbot
  have hupper_one : 1 ≤ upperTail := by
    simpa [upperTail, last, P] using
      one_le_card_xSub_roots_filter_ge_of_left_root_right_eval_nonpos
        hlast hq_last hμ hP_ne htop
  exact hpair.one_sum_one_le_card_xSub_roots_of_roots_sort_of_tail_counts
    hp_nonneg hno hrs hμ
    (by simpa [lowerTail, P] using hlower_one)
    (by simpa [upperTail, last, P] using hupper_one)

end LiuOppositeSigns
end RealRooted
