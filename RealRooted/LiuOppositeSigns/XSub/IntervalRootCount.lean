import RealRooted.Mathlib.Data.List.Zip
import RealRooted.LiuOppositeSigns.NonnegCoeffs
import RealRooted.LiuOppositeSigns.Theorem21Statements
import RealRooted.LiuOppositeSigns.XSub.LeftSucc
import RealRooted.LiuOppositeSigns.XSub.QuadraticQuadratic

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
  exact Multiset.two_le_card_of_mem_of_ne hc₁_mem hc₂_mem (ne_of_lt hc₁c₂)

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
  exact Multiset.two_le_card_of_mem_of_ne hc₁_mem hc₂_mem (ne_of_lt hc₁c₂)

/-- If `R` has a root in the closed upper tail above `a` and `a ≤ 0`, then
`X * R` has at least two roots in that upper tail, counted with multiplicity:
one from the explicit `X` factor and one from `R`. -/
private lemma two_le_card_roots_filter_ge_of_X_mul_of_one_root_ge
    {R : ℝ[X]} (hR_ne : R ≠ 0) {a c : ℝ}
    (ha0 : a ≤ 0) (hac : a ≤ c) (hc : R.IsRoot c) :
    2 ≤ ((X * R).roots.filter (fun x => a ≤ x)).card := by
  have hXR_ne : X * R ≠ 0 := mul_ne_zero X_ne_zero hR_ne
  have hone : 1 ≤ (R.roots.filter (fun x => a ≤ x)).card :=
    one_le_card_roots_filter_ge_of_isRoot hR_ne hac hc
  have hcard :
      ((X * R).roots.filter (fun x => a ≤ x)).card =
        1 + (R.roots.filter (fun x => a ≤ x)).card := by
    rw [Polynomial.roots_mul hXR_ne, Polynomial.roots_X, Multiset.filter_add,
      Multiset.card_add]
    rw [Multiset.filter_singleton]
    simp [ha0]
  rw [hcard]
  lia

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

/-- A simultaneous translation preserves the no-common-root condition. -/
theorem NoCommonRoots.comp_X_add_C
    {p q : ℝ[X]} (hno : NoCommonRoots p q) (r : ℝ) :
    NoCommonRoots (p.comp (X + C r)) (q.comp (X + C r)) := by
  intro x hpx hqx
  have hp : p.IsRoot (x + r) := by
    simpa [Polynomial.IsRoot.def, Polynomial.eval_comp] using hpx
  have hq : q.IsRoot (x + r) := by
    simpa [Polynomial.IsRoot.def, Polynomial.eval_comp] using hqx
  exact (hno (x + r) hp) hq

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

/-- The first entry of the sorted distinct root list is a root, and every root
of the polynomial lies weakly above it. -/
private lemma isRoot_head_and_roots_ge_of_roots_toFinset_sort_eq_cons
    {p : ℝ[X]} (hp_ne : p ≠ 0) {a : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: xs) :
    p.IsRoot a ∧ ∀ r ∈ p.roots, a ≤ r := by
  have ha_mem : a ∈ p.roots.toFinset.sort (· ≤ ·) := by
    simp [hrs]
  have ha : p.IsRoot a := by
    rw [Finset.mem_sort, Multiset.mem_toFinset] at ha_mem
    exact (Polynomial.mem_roots hp_ne).mp ha_mem
  refine ⟨ha, ?_⟩
  intro r hr
  have hr_mem : r ∈ p.roots.toFinset.sort (· ≤ ·) := by
    rw [Finset.mem_sort, Multiset.mem_toFinset]
    exact hr
  have hsorted_le : (p.roots.toFinset.sort (· ≤ ·)).SortedLE :=
    (Finset.sortedLT_sort p.roots.toFinset).sortedLE
  simpa [hrs] using hsorted_le.pairwise.head!_le hr_mem

/-- The right endpoint roots are accounted for by the lower exterior tail,
adjacent open gaps, and the strict upper exterior tail.  Each adjacent gap has
at most two right roots, so replacing each gap count by `min 2` still bounds the
right natural degree from above. -/
theorem
    PositiveSplitRootCountPair.right_natDegree_le_lower_sum_min_two_upper_of_roots_sort
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a : ℝ} {xs : List ℝ}
    (hrs : p.roots.toFinset.sort (· ≤ ·) = a :: xs) :
    q.natDegree ≤
      (q.roots.filter (fun r => r < a)).card +
        (((a :: xs).zip xs).map
          (fun ab => min 2
            (q.roots.filter (fun x => ab.1 < x ∧ x < ab.2)).card)).sum +
        (q.roots.filter
          (fun x => (a :: xs).getLast (List.cons_ne_nil a xs) < x)).card := by
  let gaps := (a :: xs).zip xs
  let lowerTail := (q.roots.filter (fun r => r < a)).card
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
  have hq_part : lowerTail + plainGapSum + upperTail = q.natDegree := by
    rw [← card_roots_of_splits hpair.right_splits]
    simpa [lowerTail, plainGapSum, upperTail, gaps] using hpartition
  rw [← hq_part]
  exact Nat.add_le_add (Nat.add_le_add le_rfl hplain_le_min) le_rfl

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
  have hroots_ge : ∀ r ∈ p.roots, a ≤ r :=
    (isRoot_head_and_roots_ge_of_roots_toFinset_sort_eq_cons
      hpair.left_pos.ne_zero hrs).2
  have hlower_zero :
      (q.roots.filter (fun r => r < a)).card = 0 :=
    hpair.card_right_roots_filter_lt_eq_zero_of_left_roots_ge_of_left_natDegree_eq_right_add_one
      hroots_ge hdeg
  have hbound :=
    hpair.right_natDegree_le_lower_sum_min_two_upper_of_roots_sort
      hno hrs
  simpa [hlower_zero] using hbound

/-- In the same-degree case, the lower exterior right-root tail below the first
left-root threshold transfers into the closed lower tail of the x-subtraction
pencil. -/
theorem PositiveSplitRootCountPair.card_right_roots_lt_head_le_card_xSub_le
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a μ : ℝ}
    (ha : p.IsRoot a) (hroots_ge : ∀ r ∈ p.roots, a ≤ r)
    (hdeg : p.natDegree = q.natDegree) (hμ : 0 < μ) :
    (q.roots.filter (fun r => r < a)).card ≤
      ((X * p - C μ * q).roots.filter (fun x => x ≤ a)).card := by
  let P := X * p - C μ * q
  let lower := (q.roots.filter (fun r => r < a)).card
  let upper := rootCountAtOrAbove q a
  have hqa : ¬ q.IsRoot a := hno a ha
  have hlower_le_one : lower ≤ 1 := by
    simpa [lower] using
      hpair.card_right_roots_filter_lt_le_one_of_left_roots_ge_of_natDegree_eq
        hroots_ge hdeg
  have hcases : lower = 0 ∨ lower = 1 := by
    lia
  rcases hcases with hlower | hlower
  · simp [lower, hlower]
  · have hpart : lower + upper = q.natDegree := by
      have hcard := congrArg Multiset.card
        (Multiset.filter_add_not (p := fun r : ℝ => r < a) q.roots)
      have hnot : q.roots.filter (fun r : ℝ => ¬ r < a) =
          q.roots.filter (fun r : ℝ => a ≤ r) := by
        apply Multiset.filter_congr
        intro r _hr
        simp [not_lt]
      rw [Multiset.card_add] at hcard
      simpa [lower, upper, rootCountAtOrAbove, hnot,
        card_roots_of_splits hpair.right_splits] using hcard
    have hP_data :=
      hpair.posLeadingCoeff_and_natDegree_X_mul_sub_C_mul_of_right_natDegree_le
        (by rw [hdeg]) μ
    have hP_pos : HasPosLeadingCoeff P := by
      simpa [P] using hP_data.1
    have hP_natDegree : P.natDegree = p.natDegree + 1 := by
      simpa [P] using hP_data.2
    have hP_natDegree_upper : P.natDegree = upper + 2 := by
      rw [hP_natDegree, hdeg]
      lia
    have hP_nat_pos : 0 < P.natDegree := by
      rw [hP_natDegree]
      exact Nat.succ_pos _
    have hP_degree_pos : 0 < P.degree :=
      Polynomial.natDegree_pos_iff_degree_pos.mp hP_nat_pos
    have hupper_eq :
        upper = (q.roots.filter (a < ·)).card := by
      simpa [upper] using
        rootCountAtOrAbove_eq_rootCountAbove_of_not_isRoot
          hpair.right_pos.ne_zero hqa
    have hP_ne : P ≠ 0 := hP_pos.ne_zero
    rcases Nat.even_or_odd upper with hupper_even | hupper_odd
    · have hq_a_pos : 0 < q.eval a :=
        (hpair.right_splits.eval_pos_iff_even_card_roots_gt
          (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr
            (by simpa [hupper_eq] using hupper_even)
      have hP_even : Even P.natDegree := by
        rw [hP_natDegree_upper]
        exact hupper_even.add (by norm_num)
      have hbot : Tendsto (fun x => P.eval x) atBot atTop :=
        tendsto_eval_atBot_atTop_of_posLeadingCoeff_even
          hP_pos hP_degree_pos hP_even
      have htail :=
        one_le_card_xSub_roots_filter_le_of_left_root_right_eval_nonneg
          ha hq_a_pos.le hμ hP_ne (by simpa [P] using hbot)
      simpa [lower, P, hlower] using htail
    · have hq_a_neg : q.eval a < 0 :=
        (hpair.right_splits.eval_neg_iff_odd_card_roots_gt
          (by simpa [HasPosLeadingCoeff] using hpair.right_pos) hqa).mpr
            (by simpa [hupper_eq] using hupper_odd)
      have hP_odd : Odd P.natDegree := by
        rw [hP_natDegree_upper]
        exact hupper_odd.add_even (by norm_num)
      have hbot : Tendsto (fun x => P.eval x) atBot atBot :=
        tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd
          hP_pos hP_degree_pos hP_odd
      have htail :=
        one_le_card_xSub_roots_filter_le_of_left_root_right_eval_nonpos
          ha (le_of_lt hq_a_neg) hμ hP_ne (by simpa [P] using hbot)
      simpa [lower, P, hlower] using htail

/-- In the left-successor degree case, if `a` is a lowest left-root threshold
and `p` and `q` have no common root at `a`, then every right root lies strictly
above `a`, counted with multiplicity. -/
theorem
    PositiveSplitRootCountPair.card_right_roots_filter_gt_eq_natDegree_of_left_roots_ge
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hno : NoCommonRoots p q) {a : ℝ}
    (ha : p.IsRoot a) (hroots_ge : ∀ r ∈ p.roots, a ≤ r)
    (hdeg : p.natDegree = q.natDegree + 1) :
    (q.roots.filter (a < ·)).card = q.natDegree := by
  have hlower_zero :
      (q.roots.filter (fun r => r < a)).card = 0 :=
    hpair.card_right_roots_filter_lt_eq_zero_of_left_roots_ge_of_left_natDegree_eq_right_add_one
      hroots_ge hdeg
  have hqa : ¬ q.IsRoot a := hno a ha
  have hq_all_gt : ∀ r ∈ q.roots, a < r := by
    intro r hr
    have hnot_lt : ¬ r < a := by
      intro hra
      have hr_filter : r ∈ q.roots.filter (fun x => x < a) :=
        Multiset.mem_filter.mpr ⟨hr, hra⟩
      have hpos : 0 < (q.roots.filter (fun x => x < a)).card :=
        Multiset.card_pos_iff_exists_mem.mpr ⟨r, hr_filter⟩
      rw [hlower_zero] at hpos
      exact Nat.lt_irrefl 0 hpos
    have har : a ≤ r := le_of_not_gt hnot_lt
    have hne : r ≠ a := by
      intro hra
      have hqr : q.IsRoot a := by
        simpa [hra] using (Polynomial.mem_roots hpair.right_pos.ne_zero).mp hr
      exact hqa hqr
    exact lt_of_le_of_ne har (Ne.symm hne)
  have hfilter : q.roots.filter (a < ·) = q.roots :=
    Multiset.filter_eq_self.mpr hq_all_gt
  simp [hfilter, card_roots_of_splits hpair.right_splits]

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
  have hodd : Odd (q.roots.filter (a < ·)).card := by
    simp [hcard]
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
  have hqdiv_a_pos : 0 < q.divX.eval a := by
    nlinarith
  have hq_nat_pos : 0 < q.natDegree :=
    natDegree_pos_of_isRoot hpair.right_pos.ne_zero hq_zero
  have hqdiv_deg_lt : q.divX.natDegree < q.natDegree := by
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
    exact Nat.sub_lt hq_nat_pos Nat.one_pos
  have hCdiv_deg_lt : (C μ * q.divX).natDegree < p.natDegree :=
    (Polynomial.natDegree_C_mul_le μ q.divX).trans_lt
      (hqdiv_deg_lt.trans_le hqdeg)
  have hnegCdiv_deg_lt : (-(C μ * q.divX)).natDegree < p.natDegree := by
    simpa using hCdiv_deg_lt
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
  have hR_nat_pos : 0 < R.natDegree := by
    simpa [hR_natDegree] using hp_nat_pos
  have hR_degree_pos : 0 < R.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hR_nat_pos
  have hR_a_neg : R.eval a < 0 := by
    have hp_a : p.eval a = 0 := by
      simpa [Polynomial.IsRoot.def] using ha.isRoot
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
  have hupper_count' : U + 1 ≤ upperTail := by
    simpa [U, upperTail, last, P] using hupper_count
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
    have htarget : p.natDegree + 1 ≤ 1 + G + (U + 1) := by
      lia
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
  have hP_pos : HasPosLeadingCoeff P := by
    simpa [P] using hP_data.1
  have hP_natDegree : P.natDegree = p.natDegree + 1 := by
    simpa [P] using hP_data.2
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
      have hqdeg_zero : q.natDegree = 0 := by
        lia
      have hp_nonneg_zero : HasNonnegCoeffs (p.comp (X + C (0 : ℝ))) := by
        simpa using hp_nonneg
      have hq_nonneg_zero : HasNonnegCoeffs (q.comp (X + C (0 : ℝ))) := by
        simpa using hq_nonneg
      simpa using
        positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
          (f := p) (g := q) (r := 0)
          hpair hp_nonneg_zero hq_nonneg_zero hdeg hqdeg_zero μ hμ
  | cons a xs =>
      cases hxs : xs with
      | nil =>
          have hrs_single : p.roots.toFinset.sort (· ≤ ·) = [a] := by
            simpa [hxs] using hrs
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
            have hs_eq : s = a := by
              simpa using hs_sort
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
          have hqdeg_le : q.natDegree ≤ 2 := by
            lia
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
  have hpair_shift : PositiveSplitRootCountPair p q := by
    simpa [p, q] using hpair.comp_X_add_C r
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
  have hP_pos : HasPosLeadingCoeff P := by
    simpa [P] using hP_data.1
  have hP_natDegree : P.natDegree = p.natDegree + 1 := by
    simpa [P] using hP_data.2
  have hP_natDegree_q : P.natDegree = q.natDegree + 2 := by
    rw [hP_natDegree, hdeg]
  have hP_nat_pos : 0 < P.natDegree := by
    rw [hP_natDegree]
    exact Nat.succ_pos _
  have hP_degree_pos : 0 < P.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hP_nat_pos
  have htop : Tendsto (fun x => P.eval x) atTop atTop :=
    P.tendsto_atTop_of_leadingCoeff_nonneg hP_degree_pos hP_pos.le
  have hupper_nonpos :
      ∀ y ∈ q.roots, (b :: xs).getLast (List.cons_ne_nil b xs) < y → y ≤ 0 := by
    intro y hy _hy
    exact roots_nonpos_of_hasNonnegCoeffs hq_nonneg y hy
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
          have hrs_single : p.roots.toFinset.sort (· ≤ ·) = [a] := by
            simpa [hxs] using hrs
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
            have hs_eq : s = a := by
              simpa using hs_sort
            exact le_of_eq hs_eq
          have htail_card : (q.roots.filter (a < ·)).card = q.natDegree :=
            hpair.card_right_roots_filter_gt_eq_natDegree_of_left_roots_ge
              hno hhead.1 hhead.2 hdeg
          have htail_le : (q.roots.filter (a < ·)).card ≤ 1 :=
            hpair.card_right_roots_filter_gt_le_one_of_left_largest_root
              ha_largest
          have hqdeg_le : q.natDegree ≤ 1 := by
            simpa [htail_card] using htail_le
          have hp_nonneg_zero : HasNonnegCoeffs (p.comp (X + C (0 : ℝ))) := by
            simpa using hp_nonneg
          have hq_nonneg_zero : HasNonnegCoeffs (q.comp (X + C (0 : ℝ))) := by
            simpa using hq_nonneg
          by_cases hqzero : q.natDegree = 0
          · simpa using
              positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
                (f := p) (g := q) (r := 0)
                hpair hp_nonneg_zero hq_nonneg_zero hdeg hqzero μ hμ
          · have hqone : q.natDegree = 1 := by
              lia
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

/-- No-common-root branch of the translated left-successor x-subtraction
family.  This is the shifted endpoint interface used by the factor-return
assembly; the proof delegates to the core `p, q` form. -/
theorem positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_noCommonRoots
    {f g : ℝ[X]} {r : ℝ}
    (hno : NoCommonRoots f g)
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree + 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  let p := f.comp (X + C r)
  let q := g.comp (X + C r)
  have hpair_shift : PositiveSplitRootCountPair p q := by
    simpa [p, q] using hpair.comp_X_add_C r
  have hno_shift : NoCommonRoots p q := by
    simpa [p, q] using hno.comp_X_add_C r
  have hdeg_shift : p.natDegree = q.natDegree + 1 := by
    simpa [p, q, Polynomial.natDegree_comp] using hdeg
  simpa [p, q] using
    hpair_shift.xSub_splits_of_left_successor_nonneg_of_noCommonRoots
      hfnn hgnn hno_shift hdeg_shift hμ

/-- Left-successor x-subtraction family in unshifted positive-split form,
allowing common roots.  The proof peels common roots by strong induction on the
right endpoint degree and dispatches the reduced branch to the no-common-root
theorem. -/
theorem PositiveSplitRootCountPair.xSub_splits_of_left_successor_nonneg
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hq_nonneg : HasNonnegCoeffs q)
    (hdeg : p.natDegree = q.natDegree + 1) {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  let P : ℕ → Prop := fun n =>
    ∀ {p q : ℝ[X]},
      q.natDegree = n →
      PositiveSplitRootCountPair p q →
      HasNonnegCoeffs p →
      HasNonnegCoeffs q →
      p.natDegree = q.natDegree + 1 →
      ∀ μ : ℝ, 0 < μ → (X * p - C μ * q).Splits
  have hmain : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro p q hqdeg hpair hp_nonneg hq_nonneg hdeg μ hμ
        by_cases hno : NoCommonRoots p q
        · exact hpair.xSub_splits_of_left_successor_nonneg_of_noCommonRoots
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
                (deleteRootFactor q r).natDegree + 1 :=
            hpair.natDegree_deleteRootFactor_left_eq_right_add_one
              hq_root hdeg
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

/-- Unrestricted positive-split left-successor translated x-subtraction
family. -/
theorem positiveSplitLeftSuccDegreeTranslatedXSubRightFamily :
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement := by
  intro f g r hpair hfnn hgnn hdeg μ hμ
  let p := f.comp (X + C r)
  let q := g.comp (X + C r)
  have hpair_shift : PositiveSplitRootCountPair p q := by
    simpa [p, q] using hpair.comp_X_add_C r
  have hdeg_shift : p.natDegree = q.natDegree + 1 := by
    simpa [p, q, Polynomial.natDegree_comp] using hdeg
  simpa [p, q] using
    hpair_shift.xSub_splits_of_left_successor_nonneg
      hfnn hgnn hdeg_shift hμ

/-- The proved left-successor x-subtraction family gives every predicate
restriction. -/
theorem positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate
    {P : ℕ → Prop} :
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement P :=
  positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement_of_imp
    (fun _ _ => trivial)
    (positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_true_of_xSub
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamily)

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
