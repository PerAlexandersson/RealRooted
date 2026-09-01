import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.GapCounts

/-!
# Liu x-subtraction upper exterior-tail root counts.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns
/-- If the x-subtraction pencil has the right upper-tail sign at the last
left-root location, then the summed adjacent-gap `min 2` lower bounds plus one
additional upper-tail root are bounded by the strict-upper root count above the
first left root. -/
theorem
    PositiveSplitRootCountPair.sum_min_two_add_one_le_card_xSub_gt_of_roots_sort_of_last_q_nonneg
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) (hμ : 0 < μ)
    (hq_last : 0 ≤ q.eval ((b :: xs).getLast (List.cons_ne_nil b xs)))
    (htop : Tendsto (fun x => (X * p - C μ * q).eval x) atTop atTop) :
    (((a :: b :: xs).zip (b :: xs)).map
        (fun ab => min 2
          (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum + 1 ≤
    ((X * p - C μ * q).roots.filter (a < ·)).card := by
  let last := (b :: xs).getLast (List.cons_ne_nil b xs)
  let tailCard := ((X * p - C μ * q).roots.filter (fun x => last ≤ x)).card
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
  have hP_ne : X * p - C μ * q ≠ 0 :=
    hno.xSub_ne_zero_of_left_root ha hμ.ne'
  have htail_one : 1 ≤ tailCard := by
    simpa [tailCard, last] using
      one_le_card_xSub_roots_filter_ge_of_left_root_right_eval_nonneg
        hlast hq_last hμ hP_ne htop
  have hsum_tail :=
    hpair.sum_min_two_add_card_xSub_ge_last_le_card_xSub_gt_of_roots_sort
      hp_nonneg hno hrs hμ
  exact le_trans (Nat.add_le_add_left htail_one _)
    (by simpa [tailCard, last] using hsum_tail)

/-- If a unique right-endpoint root lies strictly above the largest left root
and is negative, then the x-subtraction pencil has at least two roots in the
closed upper tail above that largest left root. -/
theorem
    PositiveSplitRootCountPair.two_le_card_xSub_ge_of_left_largest_right_root_neg
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a y μ : ℝ}
    (ha : IsLargestRoot p a) (hy_mem : y ∈ q.roots)
    (hay : a < y) (hy_neg : y < 0)
    (hμ : 0 < μ)
    (htop : Tendsto (fun x => (X * p - C μ * q).eval x) atTop atTop) :
    2 ≤ ((X * p - C μ * q).roots.filter (fun x => a ≤ x)).card := by
  let P := X * p - C μ * q
  have hy : q.IsRoot y :=
    (Polynomial.mem_roots hpair.right_pos.ne_zero).mp hy_mem
  have hqa : ¬ q.IsRoot a := hno a ha.isRoot
  have hcard : (q.roots.filter (a < ·)).card = 1 := by
    have hU_le : (q.roots.filter (a < ·)).card ≤ 1 :=
      hpair.card_right_roots_filter_gt_le_one_of_left_largest_root ha
    have hy_filter : y ∈ q.roots.filter (a < ·) :=
      Multiset.mem_filter.mpr ⟨hy_mem, hay⟩
    have hU_pos : 0 < (q.roots.filter (a < ·)).card :=
      Multiset.card_pos_iff_exists_mem.mpr ⟨y, hy_filter⟩
    exact le_antisymm hU_le hU_pos
  have hodd : Odd (q.roots.filter (a < ·)).card := by simp [hcard]
  have hq_a_neg : q.eval a < 0 :=
    (hpair.right_splits.eval_neg_iff_odd_card_roots_gt
      (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr hodd
  have hP_ne : P ≠ 0 := by simpa [P] using hno.xSub_ne_zero_of_left_root ha.isRoot hμ.ne'
  have hP_a_pos : 0 < P.eval a := by
    have hmul : μ * q.eval a < 0 := mul_neg_of_pos_of_neg hμ hq_a_neg
    have hneg : 0 < -(μ * q.eval a) := neg_pos.mpr hmul
    simpa [P, eval_X_mul_sub_C_mul_of_left_isRoot ha.isRoot, neg_mul] using hneg
  have hp_y_pos : 0 < p.eval y :=
    eval_pos_of_all_roots_lt hpair.left_pos.ne_zero hpair.left_splits hpair.left_pos
      fun r hr => lt_of_le_of_lt (ha.roots_le r hr) hay
  have hP_y_neg : P.eval y < 0 := by
    have hmul : y * p.eval y < 0 := mul_neg_of_neg_of_pos hy_neg hp_y_pos
    simpa [P, eval_X_mul_sub_C_mul_of_right_isRoot hy] using hmul
  obtain ⟨c₁, hac₁, hc₁y, hc₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg (p := P) hay
      (mul_neg_of_pos_of_neg hP_a_pos hP_y_neg)
  obtain ⟨c₂, hyc₂, hc₂_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
      (p := P) (r := y) (le_of_lt hP_y_neg) (by simpa [P] using htop)
  exact two_le_card_roots_filter_ge_of_two_isRoot_ordered hP_ne
    hac₁ (lt_of_lt_of_le hc₁y hyc₂) hc₁_root hc₂_root

/-- If the unique right-endpoint root strictly above the largest left root is
`0`, and the right natural degree is at most the left natural degree, then the
x-subtraction pencil has at least two roots in the closed upper tail above that
largest left root.

The proof factors `q = X * q.divX`, hence
`X * p - C μ * q = X * (p - C μ * q.divX)`.  The explicit `X` gives one root
at `0`, while the quotient has a root to the right of `a` because it is
negative at `a` and tends to `+∞`. -/
theorem
    PositiveSplitRootCountPair.two_le_card_xSub_ge_of_left_largest_right_root_zero
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a μ : ℝ}
    (ha : IsLargestRoot p a) (ha0 : a < 0)
    (hzero_mem : (0 : ℝ) ∈ q.roots)
    (hqdeg : q.natDegree ≤ p.natDegree) (hμ : 0 < μ) :
    2 ≤ ((X * p - C μ * q).roots.filter (fun x => a ≤ x)).card := by
  let R := p - C μ * q.divX
  have hqa : ¬ q.IsRoot a := hno a ha.isRoot
  have hcard : (q.roots.filter (a < ·)).card = 1 := by
    have hU_le : (q.roots.filter (a < ·)).card ≤ 1 :=
      hpair.card_right_roots_filter_gt_le_one_of_left_largest_root ha
    have hzero_filter : (0 : ℝ) ∈ q.roots.filter (a < ·) :=
      Multiset.mem_filter.mpr ⟨hzero_mem, ha0⟩
    have hU_pos : 0 < (q.roots.filter (a < ·)).card :=
      Multiset.card_pos_iff_exists_mem.mpr ⟨0, hzero_filter⟩
    exact le_antisymm hU_le hU_pos
  have hodd : Odd (q.roots.filter (a < ·)).card := by simp [hcard]
  have hq_a_neg : q.eval a < 0 :=
    (hpair.right_splits.eval_neg_iff_odd_card_roots_gt
      (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr hodd
  have hq_zero : q.IsRoot (0 : ℝ) :=
    (Polynomial.mem_roots hpair.right_pos.ne_zero).mp hzero_mem
  have hq0 : q.coeff 0 = 0 := by
    simpa [Polynomial.IsRoot.def, Polynomial.coeff_zero_eq_eval_zero] using hq_zero
  have hqX : q = X * q.divX := by
    symm
    simpa [hq0] using Polynomial.X_mul_divX_add q
  have hq_eval_a : q.eval a = a * q.divX.eval a := by
    calc
      q.eval a = (X * q.divX).eval a := congrArg (fun P : ℝ[X] => P.eval a) hqX
      _ = a * q.divX.eval a := by simp [Polynomial.eval_mul]
  have hqdiv_a_pos : 0 < q.divX.eval a := by nlinarith
  have hq_nat_pos : 0 < q.natDegree :=
    natDegree_pos_of_isRoot hpair.right_pos.ne_zero hq_zero
  have hqdiv_deg_lt : q.divX.natDegree < q.natDegree := by
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
    exact Nat.sub_lt hq_nat_pos Nat.one_pos
  have hCdiv_deg_lt : (C μ * q.divX).natDegree < p.natDegree :=
    (Polynomial.natDegree_C_mul_le μ q.divX).trans_lt
      (hqdiv_deg_lt.trans_le hqdeg)
  have hnegCdiv_deg_lt : (-(C μ * q.divX)).natDegree < p.natDegree := by simpa using hCdiv_deg_lt
  have hR_pos : HasPosLeadingCoeff R := by
    simpa [R, sub_eq_add_neg] using
      hasPosLeadingCoeff_add_of_natDegree_lt_left
        (p := p) (q := -(C μ * q.divX)) hnegCdiv_deg_lt hpair.left_pos
  have hR_natDegree : R.natDegree = p.natDegree := by
    simpa [R, sub_eq_add_neg] using
      natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff
        (p := p) (q := -(C μ * q.divX)) hnegCdiv_deg_lt hpair.left_pos
  have hp_nat_pos : 0 < p.natDegree := by
    have ha_mem : a ∈ p.roots :=
      (Polynomial.mem_roots hpair.left_pos.ne_zero).mpr ha.isRoot
    have hcard_pos : 0 < p.roots.card :=
      Multiset.card_pos_iff_exists_mem.mpr ⟨a, ha_mem⟩
    simpa [card_roots_of_splits hpair.left_splits] using hcard_pos
  have hR_nat_pos : 0 < R.natDegree := by simpa [hR_natDegree] using hp_nat_pos
  have hR_degree_pos : 0 < R.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hR_nat_pos
  have hR_a_neg : R.eval a < 0 := by
    have hp_a : p.eval a = 0 := by simpa [Polynomial.IsRoot.def] using ha.isRoot
    have hmul_pos : 0 < μ * q.divX.eval a := mul_pos hμ hqdiv_a_pos
    have hneg : -(μ * q.divX.eval a) < 0 := by linarith
    simpa [R, Polynomial.eval_sub, Polynomial.eval_mul, hp_a] using hneg
  have hR_top : Tendsto (fun x => R.eval x) atTop atTop :=
    R.tendsto_atTop_of_leadingCoeff_nonneg hR_degree_pos hR_pos.le
  obtain ⟨c, hac, hc⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
      (p := R) (r := a) (le_of_lt hR_a_neg) hR_top
  have hP_factor : X * p - C μ * q = X * R := by
    rw [hqX]
    simp [R]
    ring
  have htwo :=
    two_le_card_roots_filter_ge_of_X_mul_of_one_root_ge hR_pos.ne_zero
      (le_of_lt ha0) hac hc
  simpa [hP_factor] using htwo

/-- Endpoint-zero upper-tail transfer in the right-successor case when the
top coefficient of the x-subtraction pencil is positive.

Here `q = X * q.divX` and `q.divX` has the same degree as `p`.  The top
coefficient hypothesis makes `p - C μ * q.divX` positive-leading, so the same
factorization argument as
`two_le_card_xSub_ge_of_left_largest_right_root_zero` applies. -/
theorem
    PositiveSplitRootCountPair.two_le_card_xSub_ge_of_left_largest_right_root_zero_of_top_coeff_pos
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a μ : ℝ}
    (ha : IsLargestRoot p a) (ha0 : a < 0)
    (hzero_mem : (0 : ℝ) ∈ q.roots)
    (hdeg : q.natDegree = p.natDegree + 1)
    (hcoeff : 0 < p.leadingCoeff - μ * q.leadingCoeff) (hμ : 0 < μ) :
    2 ≤ ((X * p - C μ * q).roots.filter (fun x => a ≤ x)).card := by
  let R := p - C μ * q.divX
  have hqa : ¬ q.IsRoot a := hno a ha.isRoot
  have hcard : (q.roots.filter (a < ·)).card = 1 := by
    have hU_le : (q.roots.filter (a < ·)).card ≤ 1 :=
      hpair.card_right_roots_filter_gt_le_one_of_left_largest_root ha
    have hzero_filter : (0 : ℝ) ∈ q.roots.filter (a < ·) :=
      Multiset.mem_filter.mpr ⟨hzero_mem, ha0⟩
    have hU_pos : 0 < (q.roots.filter (a < ·)).card :=
      Multiset.card_pos_iff_exists_mem.mpr ⟨0, hzero_filter⟩
    exact le_antisymm hU_le hU_pos
  have hodd : Odd (q.roots.filter (a < ·)).card := by simp [hcard]
  have hq_a_neg : q.eval a < 0 :=
    (hpair.right_splits.eval_neg_iff_odd_card_roots_gt
      (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr hodd
  have hq_zero : q.IsRoot (0 : ℝ) :=
    (Polynomial.mem_roots hpair.right_pos.ne_zero).mp hzero_mem
  have hq0 : q.coeff 0 = 0 := by
    simpa [Polynomial.IsRoot.def, Polynomial.coeff_zero_eq_eval_zero] using hq_zero
  have hqX : q = X * q.divX := by
    symm
    simpa [hq0] using Polynomial.X_mul_divX_add q
  have hq_eval_a : q.eval a = a * q.divX.eval a := by
    calc
      q.eval a = (X * q.divX).eval a := congrArg (fun P : ℝ[X] => P.eval a) hqX
      _ = a * q.divX.eval a := by simp [Polynomial.eval_mul]
  have hqdiv_a_pos : 0 < q.divX.eval a := by nlinarith
  have hqdiv_natDegree : q.divX.natDegree = p.natDegree := by
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hdeg, Nat.add_sub_cancel]
  have hqdiv_lc : q.divX.leadingCoeff = q.leadingCoeff := by
    rw [leadingCoeff, hqdiv_natDegree, leadingCoeff, hdeg, Polynomial.coeff_divX]
  have hqdiv_coeff : q.divX.coeff p.natDegree = q.leadingCoeff := by
    rw [← hqdiv_natDegree, coeff_natDegree, hqdiv_lc]
  have hR_deg_le : R.natDegree ≤ p.natDegree := by
    dsimp [R]
    have hCdiv_deg_le : (C μ * q.divX).natDegree ≤ p.natDegree :=
      (Polynomial.natDegree_C_mul_le μ q.divX).trans_eq hqdiv_natDegree
    simpa using Polynomial.natDegree_sub_le_of_le (p := p) (q := C μ * q.divX)
      le_rfl hCdiv_deg_le
  have hR_coeff : R.coeff p.natDegree = p.leadingCoeff - μ * q.leadingCoeff := by
    dsimp [R]
    rw [coeff_sub, coeff_C_mul, coeff_natDegree, hqdiv_coeff]
  have hR_natDegree : R.natDegree = p.natDegree :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hR_deg_le
      (by simpa [hR_coeff] using ne_of_gt hcoeff)
  have hR_pos : HasPosLeadingCoeff R := by
    unfold HasPosLeadingCoeff
    rw [leadingCoeff, hR_natDegree, hR_coeff]
    exact hcoeff
  have hp_nat_pos : 0 < p.natDegree := by
    have ha_mem : a ∈ p.roots :=
      (Polynomial.mem_roots hpair.left_pos.ne_zero).mpr ha.isRoot
    have hcard_pos : 0 < p.roots.card :=
      Multiset.card_pos_iff_exists_mem.mpr ⟨a, ha_mem⟩
    simpa [card_roots_of_splits hpair.left_splits] using hcard_pos
  have hR_nat_pos : 0 < R.natDegree := by simpa [hR_natDegree] using hp_nat_pos
  have hR_degree_pos : 0 < R.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hR_nat_pos
  have hR_a_neg : R.eval a < 0 := by
    have hp_a : p.eval a = 0 := by simpa [Polynomial.IsRoot.def] using ha.isRoot
    have hmul_pos : 0 < μ * q.divX.eval a := mul_pos hμ hqdiv_a_pos
    have hneg : -(μ * q.divX.eval a) < 0 := by linarith
    simpa [R, Polynomial.eval_sub, Polynomial.eval_mul, hp_a] using hneg
  have hR_top : Tendsto (fun x => R.eval x) atTop atTop :=
    R.tendsto_atTop_of_leadingCoeff_nonneg hR_degree_pos hR_pos.le
  obtain ⟨c, hac, hc⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
      (p := R) (r := a) (le_of_lt hR_a_neg) hR_top
  have hP_factor : X * p - C μ * q = X * R := by
    rw [hqX]
    simp [R]
    ring
  have htwo :=
    two_le_card_roots_filter_ge_of_X_mul_of_one_root_ge hR_pos.ne_zero
      (le_of_lt ha0) hac hc
  simpa [hP_factor] using htwo

/-- If a right-endpoint root lies strictly above the largest left root and is
nonpositive, then the x-subtraction pencil has a root in the closed upper tail
above that largest left root. -/
theorem
    PositiveSplitRootCountPair.one_le_card_xSub_ge_of_left_largest_right_root_nonpos
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a y μ : ℝ}
    (ha : IsLargestRoot p a) (hy_mem : y ∈ q.roots)
    (hay : a < y) (hy_nonpos : y ≤ 0) (hμ : 0 < μ) :
    1 ≤ ((X * p - C μ * q).roots.filter (fun x => a ≤ x)).card := by
  let P := X * p - C μ * q
  have hy : q.IsRoot y :=
    (Polynomial.mem_roots hpair.right_pos.ne_zero).mp hy_mem
  have hP_ne : P ≠ 0 := by simpa [P] using hno.xSub_ne_zero_of_left_root ha.isRoot hμ.ne'
  rcases lt_or_eq_of_le hy_nonpos with hy_neg | hy_zero
  · have hqa : ¬ q.IsRoot a := hno a ha.isRoot
    have hcard : (q.roots.filter (a < ·)).card = 1 := by
      have hU_le : (q.roots.filter (a < ·)).card ≤ 1 :=
        hpair.card_right_roots_filter_gt_le_one_of_left_largest_root ha
      have hy_filter : y ∈ q.roots.filter (a < ·) :=
        Multiset.mem_filter.mpr ⟨hy_mem, hay⟩
      have hU_pos : 0 < (q.roots.filter (a < ·)).card :=
        Multiset.card_pos_iff_exists_mem.mpr ⟨y, hy_filter⟩
      exact le_antisymm hU_le hU_pos
    have hodd : Odd (q.roots.filter (a < ·)).card := by simp [hcard]
    have hq_a_neg : q.eval a < 0 :=
      (hpair.right_splits.eval_neg_iff_odd_card_roots_gt
        (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr hodd
    have hP_a_pos : 0 < P.eval a := by
      have hmul : μ * q.eval a < 0 := mul_neg_of_pos_of_neg hμ hq_a_neg
      have hneg : 0 < -(μ * q.eval a) := neg_pos.mpr hmul
      simpa [P, eval_X_mul_sub_C_mul_of_left_isRoot ha.isRoot, neg_mul] using hneg
    have hp_y_pos : 0 < p.eval y :=
      eval_pos_of_all_roots_lt hpair.left_pos.ne_zero hpair.left_splits hpair.left_pos
        fun r hr => lt_of_le_of_lt (ha.roots_le r hr) hay
    have hP_y_neg : P.eval y < 0 := by
      have hmul : y * p.eval y < 0 := mul_neg_of_neg_of_pos hy_neg hp_y_pos
      simpa [P, eval_X_mul_sub_C_mul_of_right_isRoot hy] using hmul
    obtain ⟨c, hac, _hcy, hc_root⟩ :=
      exists_isRoot_between_of_eval_mul_neg (p := P) hay
        (mul_neg_of_pos_of_neg hP_a_pos hP_y_neg)
    exact one_le_card_roots_filter_ge_of_isRoot hP_ne (le_of_lt hac) hc_root
  · subst y
    have hP_zero : P.IsRoot (0 : ℝ) := by simp [P, eval_X_mul_sub_C_mul_of_right_isRoot hy]
    exact one_le_card_roots_filter_ge_of_isRoot hP_ne (le_of_lt hay) hP_zero

/-- The strict upper right-root tail transfers into the closed upper tail of the
x-subtraction pencil when all strict upper right roots are nonpositive. -/
theorem
    PositiveSplitRootCountPair.card_right_roots_gt_le_card_xSub_ge_of_left_largest_root_nonpos
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a μ : ℝ}
    (ha : IsLargestRoot p a) (hμ : 0 < μ)
    (hupper_nonpos : ∀ y ∈ q.roots, a < y → y ≤ 0) :
    (q.roots.filter (a < ·)).card ≤
      ((X * p - C μ * q).roots.filter (fun x => a ≤ x)).card := by
  let U := (q.roots.filter (a < ·)).card
  have hU_le : U ≤ 1 := by
    simpa [U] using hpair.card_right_roots_filter_gt_le_one_of_left_largest_root ha
  have hcases : U = 0 ∨ U = 1 := by lia
  rcases hcases with hU | hU
  · simp [U, hU]
  · have hU_pos : 0 < (q.roots.filter (a < ·)).card := by simp [U, hU]
    obtain ⟨y, hy_filter⟩ := Multiset.card_pos_iff_exists_mem.mp hU_pos
    rw [Multiset.mem_filter] at hy_filter
    obtain ⟨hy_mem, hay⟩ := hy_filter
    have hone :=
      hpair.one_le_card_xSub_ge_of_left_largest_right_root_nonpos
        hno ha hy_mem hay (hupper_nonpos y hy_mem hay) hμ
    simpa [U, hU] using hone

/-- Upper exterior-tail transfer above the largest left root.  If every
right-endpoint root strictly above the largest left root is negative, then the
closed upper tail of the x-subtraction pencil contains the strict upper
right-root tail, plus one additional root.  The strict-negativity hypothesis
keeps the endpoint-zero case separate. -/
theorem
    PositiveSplitRootCountPair.card_right_roots_gt_add_one_le_card_xSub_ge_of_left_largest_root
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a μ : ℝ}
    (ha : IsLargestRoot p a) (hμ : 0 < μ)
    (hupper_neg : ∀ y ∈ q.roots, a < y → y < 0)
    (htop : Tendsto (fun x => (X * p - C μ * q).eval x) atTop atTop) :
    (q.roots.filter (a < ·)).card + 1 ≤
      ((X * p - C μ * q).roots.filter (fun x => a ≤ x)).card := by
  let U := (q.roots.filter (a < ·)).card
  have hU_le : U ≤ 1 := by
    simpa [U] using hpair.card_right_roots_filter_gt_le_one_of_left_largest_root ha
  have hcases : U = 0 ∨ U = 1 := by lia
  rcases hcases with hU | hU
  · have hqa : ¬ q.IsRoot a := hno a ha.isRoot
    have heven : Even (q.roots.filter (a < ·)).card := by simp [U, hU]
    have hq_a_pos : 0 < q.eval a :=
      (hpair.right_splits.eval_pos_iff_even_card_roots_gt
        (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr heven
    have hP_ne : X * p - C μ * q ≠ 0 :=
      hno.xSub_ne_zero_of_left_root ha.isRoot hμ.ne'
    have hone :=
      one_le_card_xSub_roots_filter_ge_of_left_root_right_eval_nonneg
        ha.isRoot hq_a_pos.le hμ hP_ne htop
    simpa [U, hU] using hone
  · have hU_pos : 0 < (q.roots.filter (a < ·)).card := by simp [U, hU]
    obtain ⟨y, hy_filter⟩ := Multiset.card_pos_iff_exists_mem.mp hU_pos
    rw [Multiset.mem_filter] at hy_filter
    obtain ⟨hy_mem, hay⟩ := hy_filter
    have htwo :=
      hpair.two_le_card_xSub_ge_of_left_largest_right_root_neg
        hno ha hy_mem hay (hupper_neg y hy_mem hay) hμ htop
    simpa [U, hU] using htwo

/-- Upper exterior-tail transfer above the largest left root when the right
natural degree is at most the left natural degree.  If every right-endpoint root
strictly above the largest left root is nonpositive, then the closed upper tail
of the x-subtraction pencil contains the strict upper right-root tail, plus one
additional root.

Compared to
`card_right_roots_gt_add_one_le_card_xSub_ge_of_left_largest_root`, this theorem
also covers the endpoint-zero case, using the degree inequality to factor the
zero root out of `q`. -/
theorem PositiveSplitRootCountPair.upper_nonpos_tail_add_one_le_card_xSub_ge
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a μ : ℝ}
    (ha : IsLargestRoot p a) (hμ : 0 < μ)
    (hqdeg : q.natDegree ≤ p.natDegree)
    (hupper_nonpos : ∀ y ∈ q.roots, a < y → y ≤ 0)
    (htop : Tendsto (fun x => (X * p - C μ * q).eval x) atTop atTop) :
    (q.roots.filter (a < ·)).card + 1 ≤
      ((X * p - C μ * q).roots.filter (fun x => a ≤ x)).card := by
  let U := (q.roots.filter (a < ·)).card
  have hU_le : U ≤ 1 := by
    simpa [U] using hpair.card_right_roots_filter_gt_le_one_of_left_largest_root ha
  have hcases : U = 0 ∨ U = 1 := by lia
  rcases hcases with hU | hU
  · have hqa : ¬ q.IsRoot a := hno a ha.isRoot
    have heven : Even (q.roots.filter (a < ·)).card := by simp [U, hU]
    have hq_a_pos : 0 < q.eval a :=
      (hpair.right_splits.eval_pos_iff_even_card_roots_gt
        (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr heven
    have hP_ne : X * p - C μ * q ≠ 0 :=
      hno.xSub_ne_zero_of_left_root ha.isRoot hμ.ne'
    have hone :=
      one_le_card_xSub_roots_filter_ge_of_left_root_right_eval_nonneg
        ha.isRoot hq_a_pos.le hμ hP_ne htop
    simpa [U, hU] using hone
  · have hU_pos : 0 < (q.roots.filter (a < ·)).card := by simp [U, hU]
    obtain ⟨y, hy_filter⟩ := Multiset.card_pos_iff_exists_mem.mp hU_pos
    rw [Multiset.mem_filter] at hy_filter
    obtain ⟨hy_mem, hay⟩ := hy_filter
    rcases lt_or_eq_of_le (hupper_nonpos y hy_mem hay) with hy_neg | hy_zero
    · have htwo :=
        hpair.two_le_card_xSub_ge_of_left_largest_right_root_neg
          hno ha hy_mem hay hy_neg hμ htop
      simpa [U, hU] using htwo
    · have htwo :=
      hpair.two_le_card_xSub_ge_of_left_largest_right_root_zero
        hno ha (by simpa [hy_zero] using hay)
        (by simpa [hy_zero] using hy_mem) hqdeg hμ
      simpa [U, hU] using htwo

/-- Upper exterior-tail transfer above the largest left root in the
right-successor case, when the top coefficient of the x-subtraction pencil is
positive.  The positive top coefficient supplies the at-top behavior and also
handles the endpoint-zero upper root after factoring `q = X * q.divX`. -/
theorem
    PositiveSplitRootCountPair.upper_nonpos_tail_add_one_le_card_xSub_ge_of_top_coeff_pos
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a μ : ℝ}
    (ha : IsLargestRoot p a) (hμ : 0 < μ)
    (hdeg : q.natDegree = p.natDegree + 1)
    (hcoeff : 0 < p.leadingCoeff - μ * q.leadingCoeff)
    (hupper_nonpos : ∀ y ∈ q.roots, a < y → y ≤ 0) :
    (q.roots.filter (a < ·)).card + 1 ≤
      ((X * p - C μ * q).roots.filter (fun x => a ≤ x)).card := by
  let P := X * p - C μ * q
  have hP_pos : HasPosLeadingCoeff P := by
    simpa [P] using
      hpair.hasPosLeadingCoeff_X_mul_sub_C_mul_of_right_natDegree_eq_left_add_one
        hdeg hcoeff
  have hP_natDegree : P.natDegree = q.natDegree := by
    simpa [P] using
      hpair.natDegree_X_mul_sub_C_mul_eq_right_natDegree_of_right_natDegree_eq_left_add_one
        hdeg (ne_of_gt hcoeff)
  have hP_nat_pos : 0 < P.natDegree := by
    rw [hP_natDegree, hdeg]
    exact Nat.succ_pos _
  have hP_degree_pos : 0 < P.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hP_nat_pos
  have htop : Tendsto (fun x => P.eval x) atTop atTop :=
    P.tendsto_atTop_of_leadingCoeff_nonneg hP_degree_pos hP_pos.le
  let U := (q.roots.filter (a < ·)).card
  have hU_le : U ≤ 1 := by
    simpa [U] using hpair.card_right_roots_filter_gt_le_one_of_left_largest_root ha
  have hcases : U = 0 ∨ U = 1 := by lia
  rcases hcases with hU | hU
  · have hqa : ¬ q.IsRoot a := hno a ha.isRoot
    have heven : Even (q.roots.filter (a < ·)).card := by simp [U, hU]
    have hq_a_pos : 0 < q.eval a :=
      (hpair.right_splits.eval_pos_iff_even_card_roots_gt
        (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr heven
    have hP_ne : X * p - C μ * q ≠ 0 :=
      hno.xSub_ne_zero_of_left_root ha.isRoot hμ.ne'
    have hone :=
      one_le_card_xSub_roots_filter_ge_of_left_root_right_eval_nonneg
        ha.isRoot hq_a_pos.le hμ hP_ne (by simpa [P] using htop)
    simpa [U, hU] using hone
  · have hU_pos : 0 < (q.roots.filter (a < ·)).card := by simp [U, hU]
    obtain ⟨y, hy_filter⟩ := Multiset.card_pos_iff_exists_mem.mp hU_pos
    rw [Multiset.mem_filter] at hy_filter
    obtain ⟨hy_mem, hay⟩ := hy_filter
    rcases lt_or_eq_of_le (hupper_nonpos y hy_mem hay) with hy_neg | hy_zero
    · have htwo :=
        hpair.two_le_card_xSub_ge_of_left_largest_right_root_neg
          hno ha hy_mem hay hy_neg hμ (by simpa [P] using htop)
      simpa [U, hU] using htwo
    · have htwo :=
        hpair.two_le_card_xSub_ge_of_left_largest_right_root_zero_of_top_coeff_pos
          hno ha (by simpa [hy_zero] using hay)
          (by simpa [hy_zero] using hy_mem) hdeg hcoeff hμ
      simpa [U, hU] using htwo

/-- The last entry of the sorted distinct root list is a largest root. -/
lemma isLargestRoot_getLast_of_roots_toFinset_sort_eq_cons_cons
    {p : ℝ[X]} (hp_ne : p ≠ 0) {a b : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) :
    IsLargestRoot p ((b :: xs).getLast (List.cons_ne_nil b xs)) := by
  let last := (b :: xs).getLast (List.cons_ne_nil b xs)
  have hlast_mem_tail : last ∈ b :: xs :=
    List.getLast_mem (List.cons_ne_nil b xs)
  have hlast_mem : last ∈ p.roots.toFinset.sort (· ≤ ·) := by
    rw [hrs]
    exact List.mem_cons.mpr (Or.inr hlast_mem_tail)
  have hlast_root : p.IsRoot last := by
    rw [Finset.mem_sort, Multiset.mem_toFinset] at hlast_mem
    exact (Polynomial.mem_roots hp_ne).mp hlast_mem
  refine ⟨hlast_root, ?_⟩
  intro r hr
  have hr_mem : r ∈ p.roots.toFinset.sort (· ≤ ·) := by
    rw [Finset.mem_sort, Multiset.mem_toFinset]
    exact hr
  have hsorted_le : (p.roots.toFinset.sort (· ≤ ·)).SortedLE :=
    (Finset.sortedLT_sort p.roots.toFinset).sortedLE
  have hle := hsorted_le.pairwise.rel_getLast hr_mem
  simpa [last, hrs] using hle

end LiuOppositeSigns
end RealRooted
