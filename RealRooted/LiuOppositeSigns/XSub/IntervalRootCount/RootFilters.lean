import RealRooted.Mathlib.Data.List.Zip
import RealRooted.LiuOppositeSigns.NonnegCoeffs
import RealRooted.LiuOppositeSigns.NoCommonRoots
import RealRooted.LiuOppositeSigns.XSub.LeftSucc
import RealRooted.LiuOppositeSigns.XSub.QuadraticQuadratic
import RealRooted.LiuOppositeSigns.XSub.QuadraticCubic

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
lemma one_le_card_roots_filter_Ioo_of_isRoot
    {P : ℝ[X]} (hP_ne : P ≠ 0) {a b c : ℝ}
    (hac : a < c) (hcb : c < b) (hc : P.IsRoot c) :
    1 ≤ (P.roots.filter (fun r => a < r ∧ r < b)).card := by
  have hmem : c ∈ P.roots.filter (fun r => a < r ∧ r < b) :=
    Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hP_ne).mpr hc, ⟨hac, hcb⟩⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨c, hmem⟩

/-- If `c` is a root of `P` with `a ≤ c`, then the right-half-line root filter
has cardinality at least one. -/
lemma one_le_card_roots_filter_ge_of_isRoot
    {P : ℝ[X]} (hP_ne : P ≠ 0) {a c : ℝ}
    (hac : a ≤ c) (hc : P.IsRoot c) :
    1 ≤ (P.roots.filter (fun r => a ≤ r)).card := by
  have hmem : c ∈ P.roots.filter (fun r => a ≤ r) :=
    Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hP_ne).mpr hc, hac⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨c, hmem⟩

/-- If `c` is a root of `P` with `c ≤ a`, then the left-half-line root filter
has cardinality at least one. -/
lemma one_le_card_roots_filter_le_of_isRoot
    {P : ℝ[X]} (hP_ne : P ≠ 0) {a c : ℝ}
    (hca : c ≤ a) (hc : P.IsRoot c) :
    1 ≤ (P.roots.filter (fun r => r ≤ a)).card := by
  have hmem : c ∈ P.roots.filter (fun r => r ≤ a) :=
    Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hP_ne).mpr hc, hca⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨c, hmem⟩

/-- If `c₁ < c₂` are roots of `P` in `(a, b)`, then the filtered root multiset
has cardinality at least two. -/
lemma two_le_card_roots_filter_Ioo_of_two_isRoot_ordered
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
lemma two_le_card_roots_filter_ge_of_two_isRoot_ordered
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

/-- If `c₁ < c₂` are roots of `P` below `a`, then the closed lower-tail root
filter has cardinality at least two. -/
lemma two_le_card_roots_filter_le_of_two_isRoot_ordered
    {P : ℝ[X]} (hP_ne : P ≠ 0) {a c₁ c₂ : ℝ}
    (hc₁c₂ : c₁ < c₂) (hc₂a : c₂ < a)
    (hc₁ : P.IsRoot c₁) (hc₂ : P.IsRoot c₂) :
    2 ≤ (P.roots.filter (fun r => r ≤ a)).card := by
  let s := P.roots.filter (fun r => r ≤ a)
  have hc₁a : c₁ < a := lt_trans hc₁c₂ hc₂a
  have hc₁_mem : c₁ ∈ s :=
    Multiset.mem_filter.mpr
      ⟨(Polynomial.mem_roots hP_ne).mpr hc₁, le_of_lt hc₁a⟩
  have hc₂_mem : c₂ ∈ s :=
    Multiset.mem_filter.mpr
      ⟨(Polynomial.mem_roots hP_ne).mpr hc₂, le_of_lt hc₂a⟩
  exact Multiset.two_le_card_of_mem_of_ne hc₁_mem hc₂_mem (ne_of_lt hc₁c₂)

/-- If `R` has a root in the closed upper tail above `a` and `a ≤ 0`, then
`X * R` has at least two roots in that upper tail, counted with multiplicity:
one from the explicit `X` factor and one from `R`. -/
lemma two_le_card_roots_filter_ge_of_X_mul_of_one_root_ge
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
  have hq0 : 0 ≤ q.eval 0 := by simpa [Polynomial.coeff_zero_eq_eval_zero] using hq_nonneg 0
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

/-- If `-P` has positive leading coefficient and `P` has even degree, then
`P(x)` tends to `-∞` as `x → -∞`. -/
lemma tendsto_eval_atBot_atBot_of_neg_posLeadingCoeff_even
    {P : ℝ[X]} (hneg_pos : HasPosLeadingCoeff (-P))
    (hdeg : 0 < P.degree) (hpar : Even P.natDegree) :
    Tendsto (fun x => P.eval x) atBot atBot := by
  have hneg_deg : 0 < (-P).degree := by simpa [Polynomial.degree_neg] using hdeg
  have hneg_par : Even (-P).natDegree := by simpa [Polynomial.natDegree_neg] using hpar
  have htnegP : Tendsto (fun x => (-P).eval x) atBot atTop :=
    tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hneg_pos hneg_deg hneg_par
  have ht := tendsto_neg_atTop_atBot.comp htnegP
  convert ht using 1
  ext x
  simp

/-- If `-P` has positive leading coefficient and `P` has odd degree, then
`P(x)` tends to `+∞` as `x → -∞`. -/
lemma tendsto_eval_atBot_atTop_of_neg_posLeadingCoeff_odd
    {P : ℝ[X]} (hneg_pos : HasPosLeadingCoeff (-P))
    (hdeg : 0 < P.degree) (hpar : Odd P.natDegree) :
    Tendsto (fun x => P.eval x) atBot atTop := by
  have hneg_deg : 0 < (-P).degree := by simpa [Polynomial.degree_neg] using hdeg
  have hneg_par : Odd (-P).natDegree := by simpa [Polynomial.natDegree_neg] using hpar
  have htnegP : Tendsto (fun x => (-P).eval x) atBot atBot :=
    tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hneg_pos hneg_deg hneg_par
  have ht := tendsto_neg_atBot_atTop.comp htnegP
  convert ht using 1
  ext x
  simp

/-- A simultaneous translation preserves the no-common-root condition. -/
theorem NoCommonRoots.comp_X_add_C
    {p q : ℝ[X]} (hno : NoCommonRoots p q) (r : ℝ) :
    NoCommonRoots (p.comp (X + C r)) (q.comp (X + C r)) := by
  intro x hpx hqx
  have hp : p.IsRoot (x + r) := by simpa [Polynomial.IsRoot.def, Polynomial.eval_comp] using hpx
  have hq : q.IsRoot (x + r) := by simpa [Polynomial.IsRoot.def, Polynomial.eval_comp] using hqx
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
  have hP_ne : P ≠ 0 := by simpa [P] using hno.xSub_ne_zero_of_left_root ha hμ
  have hnot : ¬ P.IsRoot a := by simpa [P] using hno.not_isRoot_xSub_of_left_root ha hμ
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
  have hP_ne : P ≠ 0 := by simpa [P] using hno.xSub_ne_zero_of_left_root ha hμ
  have hnot : ¬ P.IsRoot a := by simpa [P] using hno.not_isRoot_xSub_of_left_root ha hμ
  have ha_not_mem : a ∉ P.roots := by
    intro ha_mem
    exact hnot ((Polynomial.mem_roots hP_ne).mp ha_mem)
  simpa [P] using congrArg Multiset.card
    (Multiset.filter_le_eq_filter_lt_of_not_mem P.roots ha_not_mem)
end LiuOppositeSigns
end RealRooted
