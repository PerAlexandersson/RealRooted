import RealRooted.Mathlib.Data.List.Zip
import RealRooted.LiuOppositeSigns.Theorem21Statements

/-!
# Liu x-subtraction interval root counts

This module converts the odd/even interval witnesses for Liu's x-subtraction
pencil into local lower bounds for the number of roots in a single gap between
consecutive left-endpoint roots.
-/

open Polynomial Filter

namespace Polynomial

/-- Adjacent entries in the sorted distinct root list of a nonzero real
polynomial have no root strictly between them. -/
theorem not_isRoot_Ioo_of_mem_roots_toFinset_sort_zip_tail
    {p : ℝ[X]} (hp_ne : p ≠ 0) {a b z : ℝ}
    (hab : (a, b) ∈ (p.roots.toFinset.sort (· ≤ ·)).zip
      (p.roots.toFinset.sort (· ≤ ·)).tail)
    (haz : a < z) (hzb : z < b) :
    ¬ p.IsRoot z := by
  intro hz
  have hpair :
      (p.roots.toFinset.sort (· ≤ ·)).Pairwise (· < ·) :=
    (Finset.sortedLT_sort p.roots.toFinset).pairwise
  have hz_mem : z ∈ p.roots.toFinset.sort (· ≤ ·) := by
    rw [Finset.mem_sort, Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hp_ne).mpr hz
  exact List.not_mem_of_mem_zip_tail_of_pairwise_lt hpair hab haz hzb hz_mem

end Polynomial

namespace RealRooted
namespace LiuOppositeSigns

/-- If `c` is a root of `P` in `(a, b)`, then the filtered root multiset has
cardinality at least one. -/
private lemma one_le_card_roots_filter_Ioo_of_isRoot
    {P : ℝ[X]} (hP_ne : P ≠ 0) {a b c : ℝ}
    (hac : a < c) (hcb : c < b) (hc : P.IsRoot c) :
    1 ≤ (P.roots.filter (fun r => a < r ∧ r < b)).card := by
  have hmem : c ∈ P.roots.filter (fun r => a < r ∧ r < b) :=
    Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hP_ne).mpr hc, ⟨hac, hcb⟩⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨c, hmem⟩

/-- If `c` is a root of `P` with `a ≤ c`, then the right-half-line root filter
has cardinality at least one. -/
private lemma one_le_card_roots_filter_ge_of_isRoot
    {P : ℝ[X]} (hP_ne : P ≠ 0) {a c : ℝ}
    (hac : a ≤ c) (hc : P.IsRoot c) :
    1 ≤ (P.roots.filter (fun r => a ≤ r)).card := by
  have hmem : c ∈ P.roots.filter (fun r => a ≤ r) :=
    Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hP_ne).mpr hc, hac⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨c, hmem⟩

/-- If `c` is a root of `P` with `c ≤ a`, then the left-half-line root filter
has cardinality at least one. -/
private lemma one_le_card_roots_filter_le_of_isRoot
    {P : ℝ[X]} (hP_ne : P ≠ 0) {a c : ℝ}
    (hca : c ≤ a) (hc : P.IsRoot c) :
    1 ≤ (P.roots.filter (fun r => r ≤ a)).card := by
  have hmem : c ∈ P.roots.filter (fun r => r ≤ a) :=
    Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hP_ne).mpr hc, hca⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨c, hmem⟩

/-- If `c₁ < c₂` are roots of `P` in `(a, b)`, then the filtered root multiset
has cardinality at least two. -/
private lemma two_le_card_roots_filter_Ioo_of_two_isRoot_ordered
    {P : ℝ[X]} (hP_ne : P ≠ 0) {a b c₁ c₂ : ℝ}
    (hac₁ : a < c₁) (hc₁c₂ : c₁ < c₂) (hc₂b : c₂ < b)
    (hc₁ : P.IsRoot c₁) (hc₂ : P.IsRoot c₂) :
    2 ≤ (P.roots.filter (fun r => a < r ∧ r < b)).card := by
  let s := P.roots.filter (fun r => a < r ∧ r < b)
  have hc₁b : c₁ < b := lt_trans hc₁c₂ hc₂b
  have hac₂ : a < c₂ := lt_trans hac₁ hc₁c₂
  have hc₁_mem : c₁ ∈ s :=
    Multiset.mem_filter.mpr
      ⟨(Polynomial.mem_roots hP_ne).mpr hc₁, ⟨hac₁, hc₁b⟩⟩
  have hc₂_mem : c₂ ∈ s :=
    Multiset.mem_filter.mpr
      ⟨(Polynomial.mem_roots hP_ne).mpr hc₂, ⟨hac₂, hc₂b⟩⟩
  have hc₂_erase : c₂ ∈ s.erase c₁ :=
    (Multiset.mem_erase_of_ne (ne_of_lt hc₁c₂).symm).mpr hc₂_mem
  have hpair_le : ({c₁, c₂} : Multiset ℝ) ≤ s := by
    rw [← Multiset.cons_erase hc₁_mem]
    exact Multiset.cons_le_cons c₁ (Multiset.singleton_le.mpr hc₂_erase)
  have hcard := Multiset.card_le_card hpair_le
  simpa [s] using hcard

/-- If `c₁ < c₂` are roots of `P` above `a`, then the closed upper-tail root
filter has cardinality at least two. -/
private lemma two_le_card_roots_filter_ge_of_two_isRoot_ordered
    {P : ℝ[X]} (hP_ne : P ≠ 0) {a c₁ c₂ : ℝ}
    (hac₁ : a < c₁) (hc₁c₂ : c₁ < c₂)
    (hc₁ : P.IsRoot c₁) (hc₂ : P.IsRoot c₂) :
    2 ≤ (P.roots.filter (fun r => a ≤ r)).card := by
  let s := P.roots.filter (fun r => a ≤ r)
  have hac₂ : a < c₂ := lt_trans hac₁ hc₁c₂
  have hc₁_mem : c₁ ∈ s :=
    Multiset.mem_filter.mpr
      ⟨(Polynomial.mem_roots hP_ne).mpr hc₁, le_of_lt hac₁⟩
  have hc₂_mem : c₂ ∈ s :=
    Multiset.mem_filter.mpr
      ⟨(Polynomial.mem_roots hP_ne).mpr hc₂, le_of_lt hac₂⟩
  have hc₂_erase : c₂ ∈ s.erase c₁ :=
    (Multiset.mem_erase_of_ne (ne_of_lt hc₁c₂).symm).mpr hc₂_mem
  have hpair_le : ({c₁, c₂} : Multiset ℝ) ≤ s := by
    rw [← Multiset.cons_erase hc₁_mem]
    exact Multiset.cons_le_cons c₁ (Multiset.singleton_le.mpr hc₂_erase)
  have hcard := Multiset.card_le_card hpair_le
  simpa [s] using hcard

/-- A nonpositive value at `0` and divergence to `+∞` give a root in the
nonnegative upper tail, counted in the root multiset. -/
theorem one_le_card_xSub_roots_filter_nonneg_of_right_nonnegCoeffs
    {p q : ℝ[X]} (hq_nonneg : HasNonnegCoeffs q)
    {μ : ℝ} (hμ : 0 < μ)
    (hP_ne : X * p - C μ * q ≠ 0)
    (htop : Tendsto (fun x => (X * p - C μ * q).eval x) atTop atTop) :
    1 ≤ ((X * p - C μ * q).roots.filter (fun x => 0 ≤ x)).card := by
  have hq0 : 0 ≤ q.eval 0 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hq_nonneg 0
  have hP0 : (X * p - C μ * q).eval 0 ≤ 0 := by
    have hmul : 0 ≤ μ * q.eval 0 := mul_nonneg hμ.le hq0
    have hneg : -(μ * q.eval 0) ≤ 0 := neg_nonpos.mpr hmul
    simpa [eval_sub, eval_mul] using hneg
  obtain ⟨u, hu_nonneg, hu_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop hP0 htop
  exact one_le_card_roots_filter_ge_of_isRoot hP_ne hu_nonneg hu_root

/-- A left-endpoint root with nonnegative right-endpoint value and divergence
to `+∞` gives a root of the x-subtraction pencil in the upper tail. -/
theorem one_le_card_xSub_roots_filter_ge_of_left_root_right_eval_nonneg
    {p q : ℝ[X]} {a μ : ℝ}
    (ha : p.IsRoot a) (hq_a : 0 ≤ q.eval a) (hμ : 0 < μ)
    (hP_ne : X * p - C μ * q ≠ 0)
    (htop : Tendsto (fun x => (X * p - C μ * q).eval x) atTop atTop) :
    1 ≤ ((X * p - C μ * q).roots.filter (fun x => a ≤ x)).card := by
  have hP_a : (X * p - C μ * q).eval a ≤ 0 := by
    have hmul : 0 ≤ μ * q.eval a := mul_nonneg hμ.le hq_a
    have hneg : -(μ * q.eval a) ≤ 0 := neg_nonpos.mpr hmul
    simpa [eval_X_mul_sub_C_mul_of_left_isRoot ha, neg_mul] using hneg
  obtain ⟨u, ha_le, hu_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop hP_a htop
  exact one_le_card_roots_filter_ge_of_isRoot hP_ne ha_le hu_root

/-- A left-endpoint root with nonpositive right-endpoint value and divergence
to `-∞` gives a root of the x-subtraction pencil in the upper tail. -/
theorem one_le_card_xSub_roots_filter_ge_of_left_root_right_eval_nonpos
    {p q : ℝ[X]} {a μ : ℝ}
    (ha : p.IsRoot a) (hq_a : q.eval a ≤ 0) (hμ : 0 < μ)
    (hP_ne : X * p - C μ * q ≠ 0)
    (htop : Tendsto (fun x => (X * p - C μ * q).eval x) atTop atBot) :
    1 ≤ ((X * p - C μ * q).roots.filter (fun x => a ≤ x)).card := by
  let P := X * p - C μ * q
  have hP_a : 0 ≤ P.eval a := by
    have hmul : μ * q.eval a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hμ.le hq_a
    have hneg : 0 ≤ -(μ * q.eval a) := neg_nonneg.mpr hmul
    simpa [P, eval_X_mul_sub_C_mul_of_left_isRoot ha, neg_mul] using hneg
  obtain ⟨u, ha_le, hu_root⟩ :=
    exists_isRoot_ge_of_eval_nonneg_of_tendsto_atTop_atBot hP_a
      (by simpa [P] using htop)
  exact one_le_card_roots_filter_ge_of_isRoot (by simpa [P] using hP_ne) ha_le hu_root

/-- A left-endpoint root with nonnegative right-endpoint value and divergence
to `+∞` at `-∞` gives a root of the x-subtraction pencil in the lower tail. -/
theorem one_le_card_xSub_roots_filter_le_of_left_root_right_eval_nonneg
    {p q : ℝ[X]} {a μ : ℝ}
    (ha : p.IsRoot a) (hq_a : 0 ≤ q.eval a) (hμ : 0 < μ)
    (hP_ne : X * p - C μ * q ≠ 0)
    (hbot : Tendsto (fun x => (X * p - C μ * q).eval x) atBot atTop) :
    1 ≤ ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card := by
  have hP_a : (X * p - C μ * q).eval a ≤ 0 := by
    have hmul : 0 ≤ μ * q.eval a := mul_nonneg hμ.le hq_a
    have hneg : -(μ * q.eval a) ≤ 0 := neg_nonpos.mpr hmul
    simpa [eval_X_mul_sub_C_mul_of_left_isRoot ha, neg_mul] using hneg
  obtain ⟨u, hu_le, hu_root⟩ :=
    exists_isRoot_le_of_eval_nonpos_of_tendsto_atBot_atTop hP_a hbot
  exact one_le_card_roots_filter_le_of_isRoot hP_ne hu_le hu_root

/-- A left-endpoint root with nonpositive right-endpoint value and divergence
to `-∞` at `-∞` gives a root of the x-subtraction pencil in the lower tail. -/
theorem one_le_card_xSub_roots_filter_le_of_left_root_right_eval_nonpos
    {p q : ℝ[X]} {a μ : ℝ}
    (ha : p.IsRoot a) (hq_a : q.eval a ≤ 0) (hμ : 0 < μ)
    (hP_ne : X * p - C μ * q ≠ 0)
    (hbot : Tendsto (fun x => (X * p - C μ * q).eval x) atBot atBot) :
    1 ≤ ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card := by
  have hP_a : 0 ≤ (X * p - C μ * q).eval a := by
    have hmul : μ * q.eval a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hμ.le hq_a
    have hneg : 0 ≤ -(μ * q.eval a) := neg_nonneg.mpr hmul
    simpa [eval_X_mul_sub_C_mul_of_left_isRoot ha, neg_mul] using hneg
  obtain ⟨u, hu_le, hu_root⟩ :=
    exists_isRoot_le_of_eval_nonneg_of_tendsto_atBot_atBot hP_a hbot
  exact one_le_card_roots_filter_le_of_isRoot hP_ne hu_le hu_root

/-- The x-subtraction pencil does not vanish at a left root when the two
endpoint polynomials have no common roots. -/
theorem NoCommonRoots.not_isRoot_xSub_of_left_root
    {p q : ℝ[X]} (hno : NoCommonRoots p q) {a μ : ℝ}
    (ha : p.IsRoot a) (hμ : μ ≠ 0) :
    ¬ (X * p - C μ * q).IsRoot a := by
  exact not_isRoot_X_mul_sub_C_mul_of_left_isRoot ha hμ (hno a ha)

/-- The x-subtraction pencil is nonzero when the left endpoint has a root and
the two endpoint polynomials have no common roots. -/
theorem NoCommonRoots.xSub_ne_zero_of_left_root
    {p q : ℝ[X]} (hno : NoCommonRoots p q) {a μ : ℝ}
    (ha : p.IsRoot a) (hμ : μ ≠ 0) :
    X * p - C μ * q ≠ 0 := by
  intro hzero
  exact hno.not_isRoot_xSub_of_left_root ha hμ (by rw [hzero]; simp)

/-- At a left root, the closed upper tail of the x-subtraction root multiset
equals the strict upper tail. -/
theorem NoCommonRoots.card_xSub_roots_filter_ge_eq_filter_gt_of_left_root
    {p q : ℝ[X]} (hno : NoCommonRoots p q) {a μ : ℝ}
    (ha : p.IsRoot a) (hμ : μ ≠ 0) :
    ((X * p - C μ * q).roots.filter (fun x => a ≤ x)).card =
      ((X * p - C μ * q).roots.filter (a < ·)).card := by
  let P := X * p - C μ * q
  have hP_ne : P ≠ 0 := by
    simpa [P] using hno.xSub_ne_zero_of_left_root ha hμ
  have hnot : ¬ P.IsRoot a := by
    simpa [P] using hno.not_isRoot_xSub_of_left_root ha hμ
  have ha_not_mem : a ∉ P.roots := by
    intro ha_mem
    exact hnot ((Polynomial.mem_roots hP_ne).mp ha_mem)
  simpa [P] using congrArg Multiset.card
    (Multiset.filter_ge_eq_filter_gt_of_not_mem P.roots ha_not_mem)

/-- At a left root, the closed lower tail of the x-subtraction root multiset
equals the strict lower tail. -/
theorem NoCommonRoots.card_xSub_roots_filter_le_eq_filter_lt_of_left_root
    {p q : ℝ[X]} (hno : NoCommonRoots p q) {a μ : ℝ}
    (ha : p.IsRoot a) (hμ : μ ≠ 0) :
    ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card =
      ((X * p - C μ * q).roots.filter (· < a)).card := by
  let P := X * p - C μ * q
  have hP_ne : P ≠ 0 := by
    simpa [P] using hno.xSub_ne_zero_of_left_root ha hμ
  have hnot : ¬ P.IsRoot a := by
    simpa [P] using hno.not_isRoot_xSub_of_left_root ha hμ
  have ha_not_mem : a ∉ P.roots := by
    intro ha_mem
    exact hnot ((Polynomial.mem_roots hP_ne).mp ha_mem)
  simpa [P] using congrArg Multiset.card
    (Multiset.filter_le_eq_filter_lt_of_not_mem P.roots ha_not_mem)

/-- In a left-root gap with no interior left roots, Liu-compatible root counts
allow at most two right roots, counted with multiplicity. -/
theorem RootCountCompatible.card_right_roots_filter_Ioo_le_two_of_left_no_isRoot_Ioo
    {p q : ℝ[X]} (hcount : RootCountCompatible p q)
    (hp_ne : p ≠ 0) (hq_ne : q ≠ 0) {a b : ℝ}
    (hab : a < b)
    (hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z)
    (hqb : ¬ q.IsRoot b) :
    (q.roots.filter (fun r => a < r ∧ r < b)).card ≤ 2 := by
  let P := (p.roots.filter (a < ·)).card
  let Qa := (q.roots.filter (a < ·)).card
  let Qb := (q.roots.filter (b < ·)).card
  let I := (q.roots.filter (fun r => a < r ∧ r < b)).card
  by_cases htwo : 2 ≤ I
  · have hQa_eq : Qa = P + 1 := by
      simpa [P, Qa, I] using
        hcount.card_right_roots_gt_eq_left_roots_gt_add_one_of_left_no_isRoot_Ioo
          hp_ne hq_ne hab hp_no hqb htwo
    have hP_at_b : rootCountAtOrAbove p b = P := by
      have hfilter :
          p.roots.filter (fun r => b ≤ r) = p.roots.filter (a < ·) := by
        apply Multiset.filter_congr
        intro r hr
        constructor
        · intro hbr
          exact lt_of_lt_of_le hab hbr
        · intro har
          by_contra hbr
          exact hp_no r har (lt_of_not_ge hbr)
            ((Polynomial.mem_roots hp_ne).mp hr)
      simp [rootCountAtOrAbove, P, hfilter]
    have hQ_at_b : rootCountAtOrAbove q b = Qb := by
      simpa [Qb] using rootCountAtOrAbove_eq_rootCountAbove_of_not_isRoot
        hq_ne hqb
    have hP_Qb_le : ((P : ℤ) - Qb) ≤ 1 := by
      simpa [hP_at_b, hQ_at_b] using (hcount.bounds b).1
    have hq_not_mem_b : b ∉ q.roots := by
      intro hb_mem
      exact hqb ((Polynomial.mem_roots hq_ne).mp hb_mem)
    have hpart : I + Qb = Qa := by
      simpa [I, Qb, Qa] using
        card_filter_Ioo_add_card_filter_gt_eq_card_filter_gt_of_not_mem
          q.roots (le_of_lt hab) hq_not_mem_b
    have hI_le_int : (I : ℤ) ≤ 2 := by
      have hpart_int : (I : ℤ) + Qb = Qa := by
        exact_mod_cast hpart
      have hQa_eq_int : (Qa : ℤ) = P + 1 := by
        exact_mod_cast hQa_eq
      linarith
    exact_mod_cast hI_le_int
  · exact Nat.le_of_not_ge htwo

/-- Odd right-root count in a left-root gap gives at least one root of the
x-subtraction pencil in that gap. -/
theorem NoCommonRoots.one_le_card_xSub_roots_Ioo_of_odd_right_roots
    {p q : ℝ[X]} (hno : NoCommonRoots p q)
    (hq_ne : q ≠ 0) (hq : q.Splits) {a b μ : ℝ}
    (hab : a < b) (ha : p.IsRoot a) (hb : p.IsRoot b)
    (hμ : 0 < μ)
    (hodd : Odd (q.roots.filter (fun x => a < x ∧ x < b)).card) :
    1 ≤ ((X * p - C μ * q).roots.filter
      (fun x => a < x ∧ x < b)).card := by
  have hP_ne : X * p - C μ * q ≠ 0 :=
    hno.xSub_ne_zero_of_left_root ha hμ.ne'
  obtain ⟨c, hac, hcb, hc⟩ :=
    hno.exists_isRoot_between_X_mul_sub_C_mul_of_odd_right_roots
      hq_ne hq hab ha hb hμ.ne' hodd
  exact one_le_card_roots_filter_Ioo_of_isRoot hP_ne hac hcb hc

/-- Positive even right-root count in a left-root gap gives at least two roots
of the x-subtraction pencil in that gap. -/
theorem
    PositiveSplitRootCountPair.two_le_card_xSub_roots_Ioo_of_even_right_roots
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} (_hab : a < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) (hμ : 0 < μ)
    (hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z)
    (hpos : 0 < (q.roots.filter (fun x => a < x ∧ x < b)).card)
    (heven : Even (q.roots.filter (fun x => a < x ∧ x < b)).card) :
    2 ≤ ((X * p - C μ * q).roots.filter
      (fun x => a < x ∧ x < b)).card := by
  let s := q.roots.filter (fun x => a < x ∧ x < b)
  have hs_pos : 0 < s.card := by
    simpa [s] using hpos
  obtain ⟨y, hy_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hs_pos
  have hy_mem' : y ∈ q.roots.filter (fun x => a < x ∧ x < b) := by
    simpa [s] using hy_mem
  rw [Multiset.mem_filter] at hy_mem'
  obtain ⟨hy_root_mem, ⟨hay, hyb⟩⟩ := hy_mem'
  have hy : q.IsRoot y :=
    (Polynomial.mem_roots hpair.right_pos.ne_zero).mp hy_root_mem
  have hP_ne : X * p - C μ * q ≠ 0 :=
    hno.xSub_ne_zero_of_left_root ha hμ.ne'
  obtain ⟨c₁, c₂, hac₁, hc₁y, hyc₂, hc₂b, hc₁, hc₂⟩ :=
    hpair.exists_two_isRoot_between_X_mul_sub_C_mul_of_even_right_roots
      hp_nonneg hno hay hyb ha hb hy hμ hp_no heven
  exact two_le_card_roots_filter_Ioo_of_two_isRoot_ordered
    hP_ne hac₁ (lt_trans hc₁y hyc₂) hc₂b hc₁ hc₂

/-- Local root-count transfer for a left-root gap: Liu-compatible root counts
and the odd/even x-subtraction witnesses give at least
`min 2` as many x-subtraction roots as right roots in the gap. -/
theorem PositiveSplitRootCountPair.min_two_card_right_roots_le_card_xSub_roots_Ioo
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} (hab : a < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) (hμ : 0 < μ)
    (hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z) :
    min 2 (q.roots.filter (fun x => a < x ∧ x < b)).card ≤
      ((X * p - C μ * q).roots.filter
        (fun x => a < x ∧ x < b)).card := by
  let I := (q.roots.filter (fun x => a < x ∧ x < b)).card
  have hI_le_two : I ≤ 2 := by
    simpa [I] using
      hpair.count.card_right_roots_filter_Ioo_le_two_of_left_no_isRoot_Ioo
        hpair.left_pos.ne_zero hpair.right_pos.ne_zero hab hp_no (hno b hb)
  have hcases : I = 0 ∨ I = 1 ∨ I = 2 := by
    lia
  rcases hcases with hI | hI | hI
  · simp [I, hI]
  · have hodd : Odd (q.roots.filter (fun x => a < x ∧ x < b)).card := by
      simp [I, hI]
    have hone :=
      hno.one_le_card_xSub_roots_Ioo_of_odd_right_roots
        hpair.right_pos.ne_zero hpair.right_splits hab ha hb hμ hodd
    simpa [I, hI] using hone
  · have hpos : 0 < (q.roots.filter (fun x => a < x ∧ x < b)).card := by
      simp [I, hI]
    have heven : Even (q.roots.filter (fun x => a < x ∧ x < b)).card := by
      simp [I, hI]
    have htwo :=
      hpair.two_le_card_xSub_roots_Ioo_of_even_right_roots
        hp_nonneg hno hab ha hb hμ hp_no hpos heven
    simpa [I, hI] using htwo

/-- Adjacent distinct left roots in the sorted root set give the local
`min 2` lower bound for the x-subtraction pencil. -/
theorem PositiveSplitRootCountPair.min_two_card_xSub_Ioo_of_adjacent_left_roots
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ}
    (hab_mem : (a, b) ∈ (p.roots.toFinset.sort (· ≤ ·)).zip
      (p.roots.toFinset.sort (· ≤ ·)).tail)
    (hμ : 0 < μ) :
    min 2 (q.roots.filter (fun x => a < x ∧ x < b)).card ≤
      ((X * p - C μ * q).roots.filter
        (fun x => a < x ∧ x < b)).card := by
  let rs := p.roots.toFinset.sort (· ≤ ·)
  have hpair_rs : rs.Pairwise (· < ·) :=
    (Finset.sortedLT_sort p.roots.toFinset).pairwise
  have hchain : rs.IsChain (· < ·) := hpair_rs.isChain
  have hab : a < b := by
    simpa [rs] using List.rel_of_mem_zip_tail_of_isChain hchain hab_mem
  have ha_mem : a ∈ p.roots.toFinset.sort (· ≤ ·) :=
    List.fst_mem_of_mem_zip hab_mem
  have hb_mem : b ∈ p.roots.toFinset.sort (· ≤ ·) :=
    List.mem_of_mem_tail (List.snd_mem_of_mem_zip hab_mem)
  have ha : p.IsRoot a := by
    rw [Finset.mem_sort, Multiset.mem_toFinset] at ha_mem
    exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp ha_mem
  have hb : p.IsRoot b := by
    rw [Finset.mem_sort, Multiset.mem_toFinset] at hb_mem
    exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp hb_mem
  have hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z := by
    intro z haz hzb
    exact Polynomial.not_isRoot_Ioo_of_mem_roots_toFinset_sort_zip_tail
      hpair.left_pos.ne_zero hab_mem haz hzb
  exact hpair.min_two_card_right_roots_le_card_xSub_roots_Ioo
    hp_nonneg hno hab ha hb hμ hp_no

/-- Summing over adjacent entries of the sorted distinct left-root list, the
local `min 2` lower bounds for right-root counts transfer to the corresponding
open-interval root counts of the x-subtraction pencil. -/
theorem PositiveSplitRootCountPair.sum_min_two_right_roots_le_sum_xSub_roots_Ioo
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {μ : ℝ} (hμ : 0 < μ) :
    (((p.roots.toFinset.sort (· ≤ ·)).zip
        (p.roots.toFinset.sort (· ≤ ·)).tail).map
        (fun ab => min 2
          (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum ≤
      (((p.roots.toFinset.sort (· ≤ ·)).zip
        (p.roots.toFinset.sort (· ≤ ·)).tail).map
        (fun ab => ((X * p - C μ * q).roots.filter
          (fun x => ab.1 < x ∧ x < ab.2)).card)).sum := by
  apply List.sum_le_sum
  intro ab hab
  exact hpair.min_two_card_xSub_Ioo_of_adjacent_left_roots
    hp_nonneg hno hab hμ

/-- In the left-successor degree case, the right endpoint roots are accounted
for by the adjacent open gaps and the strict upper exterior tail.  The lower
exterior tail is empty, and each adjacent gap has at most two right roots. -/
theorem
    PositiveSplitRootCountPair.right_natDegree_le_sum_min_two_add_card_right_roots_gt_getLast
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: xs)
    (hdeg : p.natDegree = q.natDegree + 1) :
    q.natDegree ≤
      (((a :: xs).zip xs).map
        (fun ab => min 2
          (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
        (q.roots.filter
          (fun x => (a :: xs).getLast (List.cons_ne_nil a xs) < x)).card := by
  let gaps := (a :: xs).zip xs
  let plainGapSum :=
    (gaps.map
      (fun ab => (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum
  let minGapSum :=
    (gaps.map
      (fun ab => min 2
        (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum
  let upperTail :=
    (q.roots.filter
      (fun x => (a :: xs).getLast (List.cons_ne_nil a xs) < x)).card
  have hchain : (a :: xs).IsChain (· < ·) := by
    have hpair_rs :
        (p.roots.toFinset.sort (· ≤ ·)).Pairwise (· < ·) :=
      (Finset.sortedLT_sort p.roots.toFinset).pairwise
    have hchain_rs : (p.roots.toFinset.sort (· ≤ ·)).IsChain (· < ·) :=
      hpair_rs.isChain
    simpa [hrs] using hchain_rs
  have hroots_ge : ∀ r ∈ p.roots, a ≤ r := by
    intro r hr
    have hr_mem : r ∈ p.roots.toFinset.sort (· ≤ ·) := by
      rw [Finset.mem_sort, Multiset.mem_toFinset]
      exact hr
    have hsorted_le : (p.roots.toFinset.sort (· ≤ ·)).SortedLE :=
      (Finset.sortedLT_sort p.roots.toFinset).sortedLE
    simpa [hrs] using hsorted_le.pairwise.head!_le hr_mem
  have hlower_zero :
      (q.roots.filter (fun r => r < a)).card = 0 :=
    hpair.card_right_roots_filter_lt_eq_zero_of_left_roots_ge_of_left_natDegree_eq_right_add_one
      hroots_ge hdeg
  have hnode : ∀ x ∈ a :: xs, x ∉ q.roots := by
    intro x hx hxq
    have hx_mem : x ∈ p.roots.toFinset.sort (· ≤ ·) := by
      rw [hrs]
      exact hx
    have hpx : p.IsRoot x := by
      rw [Finset.mem_sort, Multiset.mem_toFinset] at hx_mem
      exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp hx_mem
    have hqx : q.IsRoot x :=
      (Polynomial.mem_roots hpair.right_pos.ne_zero).mp hxq
    exact (hno x hpx) hqx
  have hpartition :=
    card_filter_lt_add_sum_card_filter_Ioo_zip_tail_add_card_filter_gt_getLast_eq_card
      (s := q.roots) hchain hnode
  have hplain_le_min : plainGapSum ≤ minGapSum := by
    apply List.sum_le_sum
    intro ab hab
    rcases ab with ⟨u, v⟩
    have hab_sort : (u, v) ∈ (p.roots.toFinset.sort (· ≤ ·)).zip
        (p.roots.toFinset.sort (· ≤ ·)).tail := by
      simpa [gaps, hrs] using hab
    have huv_lt : u < v :=
      List.rel_of_mem_zip_tail_of_isChain hchain (by simpa [gaps] using hab)
    have hv_mem : v ∈ p.roots.toFinset.sort (· ≤ ·) :=
      List.mem_of_mem_tail (List.snd_mem_of_mem_zip hab_sort)
    have hv : p.IsRoot v := by
      rw [Finset.mem_sort, Multiset.mem_toFinset] at hv_mem
      exact (Polynomial.mem_roots hpair.left_pos.ne_zero).mp hv_mem
    have hp_no : ∀ z : ℝ, u < z → z < v → ¬ p.IsRoot z := by
      intro z huz hzv
      exact Polynomial.not_isRoot_Ioo_of_mem_roots_toFinset_sort_zip_tail
        hpair.left_pos.ne_zero hab_sort huz hzv
    have hgap_le_two :
        (q.roots.filter (fun x => u < x ∧ x < v)).card ≤ 2 :=
      hpair.count.card_right_roots_filter_Ioo_le_two_of_left_no_isRoot_Ioo
        hpair.left_pos.ne_zero hpair.right_pos.ne_zero huv_lt hp_no (hno v hv)
    rw [Nat.min_eq_right hgap_le_two]
  have hq_part : plainGapSum + upperTail = q.natDegree := by
    rw [← card_roots_of_splits hpair.right_splits]
    simpa [plainGapSum, upperTail, gaps, hlower_zero] using hpartition
  rw [← hq_part]
  exact Nat.add_le_add hplain_le_min le_rfl

/-- Summing over adjacent entries of the sorted distinct left-root list, the
local `min 2` lower bounds for the right-root counts are bounded by the
strict-upper root count of the x-subtraction pencil above the first left root.

This is only the interior-gap count; exterior tail intervals are separate
obligations for the final splitting count. -/
theorem PositiveSplitRootCountPair.sum_min_two_le_card_xSub_gt_of_roots_sort_cons
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: xs) (hμ : 0 < μ) :
    (((a :: xs).zip xs).map
        (fun ab => min 2
          (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum ≤
      ((X * p - C μ * q).roots.filter (a < ·)).card := by
  let P := X * p - C μ * q
  let gaps := (a :: xs).zip xs
  have hpoint :
      (gaps.map
          (fun ab => min 2
            (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum ≤
        (gaps.map
          (fun ab => (P.roots.filter
            (fun x => ab.1 < x ∧ x < ab.2)).card)).sum := by
    simpa [gaps, P, hrs] using
      hpair.sum_min_two_right_roots_le_sum_xSub_roots_Ioo hp_nonneg hno hμ
  have hchain : (a :: xs).IsChain (· < ·) := by
    have hpair_rs :
        (p.roots.toFinset.sort (· ≤ ·)).Pairwise (· < ·) :=
      (Finset.sortedLT_sort p.roots.toFinset).pairwise
    have hchain_rs : (p.roots.toFinset.sort (· ≤ ·)).IsChain (· < ·) :=
      hpair_rs.isChain
    simpa [hrs] using hchain_rs
  have htel :
      (gaps.map
          (fun ab => (P.roots.filter
            (fun x => ab.1 < x ∧ x < ab.2)).card)).sum ≤
        (P.roots.filter (a < ·)).card := by
    simpa [gaps, P] using
      sum_card_filter_Ioo_zip_tail_le_card_filter_gt (s := P.roots) hchain
  exact le_trans hpoint htel

/-- For at least two distinct left-root locations, the summed adjacent-gap
`min 2` lower bounds and the closed upper tail at the last left root fit
disjointly inside the strict-upper root count of the x-subtraction pencil above
the first left root. -/
theorem
    PositiveSplitRootCountPair.sum_min_two_add_card_xSub_ge_last_le_card_xSub_gt_of_roots_sort
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) (hμ : 0 < μ) :
    (((a :: b :: xs).zip (b :: xs)).map
        (fun ab => min 2
          (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
      ((X * p - C μ * q).roots.filter
        (fun x => (b :: xs).getLast (List.cons_ne_nil b xs) ≤ x)).card ≤
    ((X * p - C μ * q).roots.filter (a < ·)).card := by
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
  have htail :
      (gaps.map
          (fun ab => (P.roots.filter
            (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
        (P.roots.filter
          (fun x => (b :: xs).getLast (List.cons_ne_nil b xs) ≤ x)).card ≤
      (P.roots.filter (a < ·)).card := by
    simpa [gaps, P] using
      sum_card_filter_Ioo_zip_tail_add_card_filter_ge_getLast_le_card_filter_gt
        (s := P.roots) hchain
  exact le_trans (Nat.add_le_add hpoint le_rfl) htail

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
  have ha_mem : a ∈ p.roots.toFinset.sort (· ≤ ·) := by
    simp [hrs]
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
    (hcard : (q.roots.filter (a < ·)).card = 1) (hμ : 0 < μ)
    (htop : Tendsto (fun x => (X * p - C μ * q).eval x) atTop atTop) :
    2 ≤ ((X * p - C μ * q).roots.filter (fun x => a ≤ x)).card := by
  let P := X * p - C μ * q
  have hy : q.IsRoot y :=
    (Polynomial.mem_roots hpair.right_pos.ne_zero).mp hy_mem
  have hqa : ¬ q.IsRoot a := hno a ha.isRoot
  have hodd : Odd (q.roots.filter (a < ·)).card := by
    simp [hcard]
  have hq_a_neg : q.eval a < 0 :=
    (hpair.right_splits.eval_neg_iff_odd_card_roots_gt
      (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr hodd
  have hP_ne : P ≠ 0 := by
    simpa [P] using hno.xSub_ne_zero_of_left_root ha.isRoot hμ.ne'
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
  have hcases : U = 0 ∨ U = 1 := by
    lia
  rcases hcases with hU | hU
  · have hqa : ¬ q.IsRoot a := hno a ha.isRoot
    have heven : Even (q.roots.filter (a < ·)).card := by
      simp [U, hU]
    have hq_a_pos : 0 < q.eval a :=
      (hpair.right_splits.eval_pos_iff_even_card_roots_gt
        (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr heven
    have hP_ne : X * p - C μ * q ≠ 0 :=
      hno.xSub_ne_zero_of_left_root ha.isRoot hμ.ne'
    have hone :=
      one_le_card_xSub_roots_filter_ge_of_left_root_right_eval_nonneg
        ha.isRoot hq_a_pos.le hμ hP_ne htop
    simpa [U, hU] using hone
  · have hU_pos : 0 < (q.roots.filter (a < ·)).card := by
      simp [U, hU]
    obtain ⟨y, hy_filter⟩ := Multiset.card_pos_iff_exists_mem.mp hU_pos
    rw [Multiset.mem_filter] at hy_filter
    obtain ⟨hy_mem, hay⟩ := hy_filter
    have htwo :=
      hpair.two_le_card_xSub_ge_of_left_largest_right_root_neg
        hno ha hy_mem hay (hupper_neg y hy_mem hay) (by simpa [U] using hU)
        hμ htop
    simpa [U, hU] using htwo

/-- The last entry of the sorted distinct root list is a largest root. -/
private lemma isLargestRoot_getLast_of_roots_toFinset_sort_eq_cons_cons
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

/-- Count-to-splitting endpoint using the variable upper exterior-tail transfer.
The upper tail contributes the strict right-root tail above the largest left
root, plus one additional x-subtraction root.  The endpoint-zero case is kept
outside this theorem by the strict-negativity hypothesis on those right roots. -/
theorem
    PositiveSplitRootCountPair.xSub_splits_of_roots_sort_of_upper_tail_transfer
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b μ : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: b :: xs) (hμ : 0 < μ)
    (hdeg : p.natDegree = q.natDegree + 1)
    (hlower_one : 1 ≤ ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card)
    (hupper_neg :
      ∀ y ∈ q.roots, (b :: xs).getLast (List.cons_ne_nil b xs) < y → y < 0)
    (htop : Tendsto (fun x => (X * p - C μ * q).eval x) atTop atTop) :
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
  have hlast : IsLargestRoot p last := by
    simpa [last] using isLargestRoot_getLast_of_roots_toFinset_sort_eq_cons_cons
      hpair.left_pos.ne_zero hrs
  have hupper_count : U + 1 ≤ upperTail := by
    simpa [U, upperTail, last, P] using
      hpair.card_right_roots_gt_add_one_le_card_xSub_ge_of_left_largest_root
        hno hlast hμ hupper_neg htop
  have hpack :
      lowerTail + G + upperTail ≤ P.roots.card := by
    simpa [lowerTail, upperTail, G, last, P] using
      hpair.lower_sum_upper_le_card_xSub_roots_of_roots_sort
        hp_nonneg hno hrs hμ
  have hcount : 1 + G + (U + 1) ≤ P.roots.card := by
    have hmono : 1 + G + (U + 1) ≤ lowerTail + G + upperTail :=
      Nat.add_le_add (Nat.add_le_add (by simpa [lowerTail, P] using hlower_one) le_rfl)
        hupper_count
    exact hmono.trans hpack
  have hq_bound : q.natDegree ≤ G + U := by
    simpa [G, U, last] using
      hpair.right_natDegree_le_sum_min_two_add_card_right_roots_gt_getLast
        hno (a := a) (xs := b :: xs) (by simpa using hrs) hdeg
  have hdegree : P.natDegree ≤ 1 + G + (U + 1) := by
    have hP_deg := hpair.natDegree_X_mul_sub_C_mul_le_left_natDegree_add_one μ
    have htarget : p.natDegree + 1 ≤ 1 + G + (U + 1) := by
      lia
    exact hP_deg.trans htarget
  exact Polynomial.splits_of_le_roots_of_natDegree_le_card
    (s := P.roots) le_rfl (hdegree.trans hcount)

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
  have ha_mem : a ∈ p.roots.toFinset.sort (· ≤ ·) := by
    simp [hrs]
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
  have ha_mem : a ∈ p.roots.toFinset.sort (· ≤ ·) := by
    simp [hrs]
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
  have ha_mem : a ∈ p.roots.toFinset.sort (· ≤ ·) := by
    simp [hrs]
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
  have ha_mem : a ∈ p.roots.toFinset.sort (· ≤ ·) := by
    simp [hrs]
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
