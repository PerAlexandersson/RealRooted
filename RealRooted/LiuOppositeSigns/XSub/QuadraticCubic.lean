module

import RealRooted.LiuOppositeSigns.XSub.IntervalRootCount.RightSuccessor
import RealRooted.CommonInterleaver.RootCountCombinatorics
import RealRooted.LiuOppositeSigns.XSub.LinearQuadratic
import RealRooted.LiuOppositeSigns.XSub.SplittingTools
import RealRooted.LiuOppositeSigns.PositiveSplitPair
public import RealRooted.LiuOppositeSigns.PositiveSplitRootCount
import RealRooted.SameDegreeCubicRootCount
import RealRooted.SameDegreeQuadraticRootCount
import RealRooted.QuadraticRoot
import RealRooted.MaWang.StrictSigns.Assembly
import RealRooted.MaWang.StrictSigns.RootSigns
import RealRooted.WagnerRightSum.Sign

/-!
# Liu quadratic/cubic x-subtraction leaf

This module contains the normalized quadratic/cubic positive-split
x-subtraction cases, derived from the general right-successor endpoint.
-/

@[expose] public section

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- In the `(2, 3)` positive split root-count case, the roots obey the
finite interleaving inequalities obtained by symmetry from the `(3, 2)` case.
-/
lemma roots_order_of_positiveSplitRootCountPair_two_three
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    {a b c d e : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hde : d ≤ e)
    (hfroots : f.roots = {a, b}) (hgroots : g.roots = {c, d, e}) :
    c ≤ a ∧ d ≤ b ∧ a ≤ e :=
  roots_order_of_positiveSplitRootCountPair_three_two
    h.symm hcd hde hab hgroots hfroots

/-- A `(2, 3)` positive split root-count pair admits ordered root data with
the interleaving inequalities needed by the degree-three right-successor
x-subtraction terminal. -/
lemma exists_roots_order_of_positiveSplitRootCountPair_two_three
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    (hfdeg : f.natDegree = 2) (hgdeg : g.natDegree = 3) :
    ∃ a b c d e : ℝ,
      a ≤ b ∧ c ≤ d ∧ d ≤ e ∧
        f.roots = {a, b} ∧ g.roots = {c, d, e} ∧
          f = C f.leadingCoeff * ((X - C a) * (X - C b)) ∧
            g = C g.leadingCoeff * ((X - C c) * (X - C d) * (X - C e)) ∧
              c ≤ a ∧ d ≤ b ∧ a ≤ e := by
  obtain ⟨a, b, hab, hfroots, hffac⟩ :=
    exists_roots_pair_of_splits_natDegree_two h.left_splits hfdeg
  obtain ⟨c, d, e, hcd, hde, hgroots, hgfac⟩ :=
    exists_roots_triple_of_splits_natDegree_three h.right_splits hgdeg
  obtain ⟨hca, hdb, hae⟩ :=
    roots_order_of_positiveSplitRootCountPair_two_three
      h hab hcd hde hfroots hgroots
  exact
    ⟨a, b, c, d, e, hab, hcd, hde, hfroots, hgroots, hffac, hgfac,
      hca, hdb, hae⟩

/-- The normalized quadratic/cubic x-subtraction polynomial. -/
noncomputable def xSubQuadraticCubic (a b c d e μ : ℝ) : ℝ[X] :=
  X * ((X - C a) * (X - C b)) -
    C μ * ((X - C c) * (X - C d) * (X - C e))

/-- The normalized degree-three pencil is a specialization of the general tail theorem. -/
private lemma normalized_cubic {a b c d e μ : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hde : d ≤ e) (hca : c ≤ a)
    (hdb : d ≤ b) (hae : a ≤ e) (hb0 : b ≤ 0) (he0 : e ≤ 0)
    (hμ : 0 < μ) : (xSubQuadraticCubic a b c d e μ).Splits := by
  let p : ℝ[X] := (X - C a) * (X - C b)
  let q : ℝ[X] := (X - C c) * (X - C d) * (X - C e)
  let k : ℝ[X] := (X - C c) * (X - C (max a d)) * (X - C (max b e))
  have hp : p.Monic := (monic_X_sub_C a).mul (monic_X_sub_C b)
  have hq : q.Monic := ((monic_X_sub_C c).mul (monic_X_sub_C d)).mul (monic_X_sub_C e)
  have hk : k.Monic :=
    ((monic_X_sub_C c).mul (monic_X_sub_C (max a d))).mul (monic_X_sub_C (max b e))
  have hp_split : p.Splits := (Splits.X_sub_C a).mul (Splits.X_sub_C b)
  have hq_split : q.Splits := ((Splits.X_sub_C c).mul (Splits.X_sub_C d)).mul (Splits.X_sub_C e)
  have hk_split : k.Splits :=
    ((Splits.X_sub_C c).mul (Splits.X_sub_C (max a d))).mul (Splits.X_sub_C (max b e))
  have hp_roots : p.roots = (↑[a, b] : Multiset ℝ) := by
    change p.roots = {a, b}
    simp [p, roots_mul, X_sub_C_ne_zero]
  have hq_roots : q.roots = (↑[c, d, e] : Multiset ℝ) := by
    change q.roots = {c, d, e}
    simp [q, roots_mul, X_sub_C_ne_zero]
  have hk_roots : k.roots = (↑[c, max a d, max b e] : Multiset ℝ) := by
    change k.roots = {c, max a d, max b e}
    simp [k, roots_mul, X_sub_C_ne_zero]
  have hpk : StrictInterl p k := by
    refine ⟨⟨hp.ne_zero, hp_split⟩, ⟨hk.ne_zero, hk_split⟩,
      [a, b], [c, max a d, max b e], ?_, ?_, hp_roots.symm, hk_roots.symm, Or.inl ?_⟩
    · simp [hab]
    · grind [List.pairwise_cons, max_le_iff, le_max_iff]
    · exact ⟨rfl, by simp [ListInterlaces, hca, hab, hdb, max_le_iff]⟩
  have hqk : StrictInterl q k := by
    refine ⟨⟨hq.ne_zero, hq_split⟩, ⟨hk.ne_zero, hk_split⟩,
      [c, d, e], [c, max a d, max b e], ?_, ?_, hq_roots.symm, hk_roots.symm, Or.inr ?_⟩
    · simp [hcd, hde, hcd.trans hde]
    · grind [List.pairwise_cons, max_le_iff, le_max_iff]
    · exact ⟨rfl, by simp [ListAlternates, ListInterlaces, hae, hde, hcd, max_le_iff]⟩
  have hpair : PositiveSplitRootCountPair p q := by
    refine ⟨hasPosLeadingCoeff_of_monic hp, hasPosLeadingCoeff_of_monic hq,
      hp_split, hq_split, ?_⟩
    apply RootCountCompatible.of_rootCountAbove_bounds_of_nonRoot hp.ne_zero hq.ne_zero
    intro x _ _
    have hpbound := succDegreeRootCountAboveOriented_of_strictInterl hpk
      (by simp [p, k, natDegree_mul, X_sub_C_ne_zero]) x
    have hqdeg : k.natDegree = q.natDegree := by
      simp [q, k, natDegree_mul, X_sub_C_ne_zero]
    have hqbound :=
      (sameDegreeRootCountAbove_oriented_iff_rootCount_oriented_pointwise
        hk_split hq_split hqdeg.symm x).mpr
          (sameDegreeRootCountOriented_of_strictInterl hqk hqdeg x)
    constructor <;> lia
  have hpnn : HasNonnegCoeffs p :=
    (hasNonnegCoeffs_X_sub_C (hab.trans hb0)).mul (hasNonnegCoeffs_X_sub_C hb0)
  have hqnn : HasNonnegCoeffs q :=
    ((hasNonnegCoeffs_X_sub_C (hcd.trans (hde.trans he0))).mul
      (hasNonnegCoeffs_X_sub_C (hde.trans he0))).mul (hasNonnegCoeffs_X_sub_C he0)
  have hdeg : q.natDegree = p.natDegree + 1 := by
    simp [p, q, natDegree_mul, X_sub_C_ne_zero]
  exact hpair.xSub_splits_of_right_successor_nonneg hpnn hqnn hdeg hμ

/-- Expanded form of the normalized quadratic/cubic endpoint polynomial. -/
lemma xSubQuadraticCubic_eq_cubic_expansion (a b c d e μ : ℝ) :
    xSubQuadraticCubic a b c d e μ =
        C (1 - μ) * X ^ 3 + C (μ * (c + d + e) - (a + b)) * X ^ 2 +
          C (a * b - μ * (c * d + c * e + d * e)) * X +
            C (μ * c * d * e) := by
  unfold xSubQuadraticCubic
  simp only [C_add, C_sub, C_mul, C_1]
  ring_nf

/-- The normalized quadratic/cubic x-subtraction polynomial has degree at most
three. -/
lemma natDegree_xSubQuadraticCubic_le (a b c d e μ : ℝ) :
    (xSubQuadraticCubic a b c d e μ).natDegree ≤ 3 := by
  unfold xSubQuadraticCubic
  compute_degree

/-- When the top cubic terms cancel, the normalized quadratic/cubic
x-subtraction polynomial has degree at most two. -/
lemma natDegree_xSubQuadraticCubic_of_mu_one_le_two (a b c d e : ℝ) :
    (xSubQuadraticCubic a b c d e 1).natDegree ≤ 2 := by
  rw [xSubQuadraticCubic_eq_cubic_expansion]
  simp only [sub_self, map_zero, zero_mul, one_mul, map_sub, map_add, zero_add,
    map_mul]
  compute_degree

/-- Cubic coefficient of the normalized quadratic/cubic endpoint polynomial. -/
lemma coeff_three_xSubQuadraticCubic (a b c d e μ : ℝ) :
    (xSubQuadraticCubic a b c d e μ).coeff 3 = 1 - μ := by
  rw [xSubQuadraticCubic_eq_cubic_expansion]
  simp [Polynomial.coeff_mul_X_pow']

/-- Away from the cancellation value `μ = 1`, the normalized quadratic/cubic
x-subtraction polynomial is a genuine cubic. -/
lemma natDegree_xSubQuadraticCubic_of_mu_ne_one
    (a b c d e μ : ℝ) (hμ : μ ≠ 1) :
    (xSubQuadraticCubic a b c d e μ).natDegree = 3 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_xSubQuadraticCubic_le a b c d e μ
  · rw [coeff_three_xSubQuadraticCubic]
    intro h
    exact hμ (by linarith)

/-- Away from the cancellation value `μ = 1`, the normalized quadratic/cubic
x-subtraction polynomial is nonzero. -/
lemma xSubQuadraticCubic_ne_zero_of_mu_ne_one
    (a b c d e μ : ℝ) (hμ : μ ≠ 1) :
    xSubQuadraticCubic a b c d e μ ≠ 0 := by
  intro hzero
  have hdeg := natDegree_xSubQuadraticCubic_of_mu_ne_one a b c d e μ hμ
  rw [hzero] at hdeg
  norm_num at hdeg

/-- Leading coefficient of the normalized quadratic/cubic endpoint polynomial
away from the cancellation value `μ = 1`. -/
lemma leadingCoeff_xSubQuadraticCubic_of_mu_ne_one
    (a b c d e μ : ℝ) (hμ : μ ≠ 1) :
    (xSubQuadraticCubic a b c d e μ).leadingCoeff = 1 - μ := by
  rw [Polynomial.leadingCoeff,
    natDegree_xSubQuadraticCubic_of_mu_ne_one a b c d e μ hμ,
    coeff_three_xSubQuadraticCubic]

/-- Positive-leading case for the normalized quadratic/cubic endpoint
polynomial. -/
lemma hasPosLeadingCoeff_xSubQuadraticCubic_of_mu_lt_one
    (a b c d e μ : ℝ) (hμ : μ < 1) :
    HasPosLeadingCoeff
      (xSubQuadraticCubic a b c d e μ) := by
  unfold HasPosLeadingCoeff
  rw [leadingCoeff_xSubQuadraticCubic_of_mu_ne_one]
  · linarith
  · exact ne_of_lt hμ

/-- Negative-leading case, expressed as positivity of the negated normalized
quadratic/cubic endpoint polynomial. -/
lemma hasPosLeadingCoeff_neg_xSubQuadraticCubic_of_one_lt_mu
    (a b c d e μ : ℝ) (hμ : 1 < μ) :
    HasPosLeadingCoeff
      (-(xSubQuadraticCubic a b c d e μ)) := by
  unfold HasPosLeadingCoeff
  rw [Polynomial.leadingCoeff_neg, leadingCoeff_xSubQuadraticCubic_of_mu_ne_one]
  · linarith
  · exact ne_of_gt hμ

/-- Evaluation form of the normalized quadratic/cubic x-subtraction leaf. -/
lemma eval_xSubQuadraticCubic (a b c d e μ x : ℝ) :
    (xSubQuadraticCubic a b c d e μ).eval x =
      x * ((x - a) * (x - b)) - μ * ((x - c) * (x - d) * (x - e)) := by
  simp only [xSubQuadraticCubic, eval_sub, eval_mul, eval_X, eval_C]

/-- The value at zero of the normalized quadratic/cubic x-subtraction polynomial. -/
lemma eval_zero_xSubQuadraticCubic (a b c d e μ : ℝ) :
    (xSubQuadraticCubic a b c d e μ).eval 0 = μ * c * d * e := by
  rw [eval_xSubQuadraticCubic]
  ring

/-- Negative zero value under negative cubic roots and a positive parameter. -/
lemma xSubQuadraticCubic_eval_zero_neg (a b c d e μ : ℝ)
    (hc : c < 0) (hd : d < 0) (he : e < 0) (hμ : 0 < μ) :
    (xSubQuadraticCubic a b c d e μ).eval 0 < 0 := by
  rw [eval_zero_xSubQuadraticCubic]
  have hcd_pos : 0 < c * d := mul_pos_of_neg_of_neg hc hd
  have hcde_neg : c * d * e < 0 := mul_neg_of_pos_of_neg hcd_pos he
  calc
    μ * c * d * e = μ * (c * d * e) := by ring
    _ < 0 := mul_neg_of_pos_of_neg hμ hcde_neg

/-- If `μ < 1`, the normalized quadratic/cubic endpoint polynomial tends to
`+∞` at `+∞`. -/
lemma tendsto_eval_xSubQuadraticCubic_atTop_atTop_of_mu_lt_one
    (a b c d e μ : ℝ) (hμ : μ < 1) :
    Tendsto
      (fun x =>
        (xSubQuadraticCubic a b c d e μ).eval x)
      atTop atTop := by
  let P : ℝ[X] := xSubQuadraticCubic a b c d e μ
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubQuadraticCubic_of_mu_lt_one a b c d e μ hμ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      dsimp [P]
      rw [natDegree_xSubQuadraticCubic_of_mu_ne_one]
      · norm_num
      · exact ne_of_lt hμ
    exact natDegree_pos_iff_degree_pos.mp hnat
  exact P.tendsto_atTop_of_leadingCoeff_nonneg hP_deg_pos hP_pos.le

/-- If `1 < μ`, the normalized quadratic/cubic endpoint polynomial tends to
`+∞` at `-∞`. -/
lemma tendsto_eval_xSubQuadraticCubic_atBot_atTop_of_one_lt_mu
    (a b c d e μ : ℝ) (hμ : 1 < μ) :
    Tendsto
      (fun x =>
        (xSubQuadraticCubic a b c d e μ).eval x)
      atBot atTop := by
  let P : ℝ[X] := xSubQuadraticCubic a b c d e μ
  let Q : ℝ[X] := -P
  have hQ_pos : HasPosLeadingCoeff Q := by
    dsimp [Q, P]
    exact hasPosLeadingCoeff_neg_xSubQuadraticCubic_of_one_lt_mu a b c d e μ hμ
  have hQ_deg_pos : 0 < Q.degree := by
    have hnat : 0 < Q.natDegree := by
      dsimp [Q, P]
      rw [Polynomial.natDegree_neg]
      rw [natDegree_xSubQuadraticCubic_of_mu_ne_one]
      · norm_num
      · exact ne_of_gt hμ
    exact natDegree_pos_iff_degree_pos.mp hnat
  have hQ_odd : Odd Q.natDegree := by
    dsimp [Q, P]
    rw [Polynomial.natDegree_neg]
    rw [natDegree_xSubQuadraticCubic_of_mu_ne_one]
    · norm_num
    · exact ne_of_gt hμ
  have htQ : Tendsto (fun x => Q.eval x) atBot atBot :=
    tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hQ_pos hQ_deg_pos hQ_odd
  have htneg := tendsto_neg_atBot_atTop.comp htQ
  convert htneg using 1
  ext x
  dsimp [Q]
  rw [eval_neg]
  rw [eval_xSubQuadraticCubic]
  ring

/-- The common splitting tail for the normalized quadratic/cubic endpoint:
two ordered finite roots, a negative value to their left, and a negative value
at zero imply splitting.  The proof splits on the leading coefficient:
`μ < 1` gives a right outer root, `1 < μ` gives a left outer root, and
`μ = 1` drops the degree to at most two. -/
lemma xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    {a b c d e μ l r₁ r₂ : ℝ}
    (hleft_neg :
      (xSubQuadraticCubic a b c d e μ).eval l < 0)
    (hzero_neg :
      (xSubQuadraticCubic a b c d e μ).eval 0 < 0)
    (hl1 : l < r₁) (h12 : r₁ < r₂) (hr2_0 : r₂ < 0)
    (hr₁ :
      (xSubQuadraticCubic a b c d e μ).IsRoot r₁)
    (hr₂ :
      (xSubQuadraticCubic a b c d e μ).IsRoot r₂) :
    (xSubQuadraticCubic a b c d e μ).Splits := by
  let P : ℝ[X] := xSubQuadraticCubic a b c d e μ
  have hP_left_neg : P.eval l < 0 := by simpa [P] using hleft_neg
  have hP_zero_neg : P.eval 0 < 0 := by simpa [P] using hzero_neg
  have hP_r₁ : P.IsRoot r₁ := by simpa [P] using hr₁
  have hP_r₂ : P.IsRoot r₂ := by simpa [P] using hr₂
  rcases lt_trichotomy μ 1 with hμ_lt | hμ_eq | hμ_gt
  · have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
      dsimp [P]
      exact
        tendsto_eval_xSubQuadraticCubic_atTop_atTop_of_mu_lt_one
          a b c d e μ hμ_lt
    obtain ⟨rR, hrR_ge, hrR_root⟩ :=
      exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
        (le_of_lt hP_zero_neg) ht_top
    have h2R : r₂ < rR := lt_of_lt_of_le hr2_0 hrR_ge
    have hP_ne : P ≠ 0 := by
      dsimp [P]
      exact xSubQuadraticCubic_ne_zero_of_mu_ne_one
        a b c d e μ (ne_of_lt hμ_lt)
    have hdeg_le : P.natDegree ≤ 3 := by
      dsimp [P]
      exact natDegree_xSubQuadraticCubic_le a b c d e μ
    have hsplits := splits_of_three_ordered_roots_of_natDegree_le
      hP_ne hdeg_le h12 h2R hP_r₁ hP_r₂ hrR_root
    simpa [P] using hsplits
  · have hP_ne : P ≠ 0 := by
      intro hzero
      have hroot : P.eval l = 0 := by simp [hzero]
      linarith
    have hdeg_le : P.natDegree ≤ 2 := by
      dsimp [P]
      rw [hμ_eq]
      exact natDegree_xSubQuadraticCubic_of_mu_one_le_two a b c d e
    have hsplits := splits_of_roots_list_of_natDegree_le (rs := [r₁, r₂])
      hP_ne (by simpa using hdeg_le)
      (by simp [ne_of_lt h12])
      (by
        intro r hr
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl
        · exact hP_r₁
        · exact hP_r₂)
    simpa [P] using hsplits
  · have ht_bot : Tendsto (fun x => P.eval x) atBot atTop := by
      dsimp [P]
      exact
        tendsto_eval_xSubQuadraticCubic_atBot_atTop_of_one_lt_mu
          a b c d e μ hμ_gt
    obtain ⟨rL, hrL_le, hrL_root⟩ :=
      exists_isRoot_le_of_eval_nonpos_of_tendsto_atBot_atTop
        (le_of_lt hP_left_neg) ht_bot
    have hL1 : rL < r₁ := lt_of_le_of_lt hrL_le hl1
    have hP_ne : P ≠ 0 := by
      dsimp [P]
      exact xSubQuadraticCubic_ne_zero_of_mu_ne_one
        a b c d e μ (ne_of_gt hμ_gt)
    have hdeg_le : P.natDegree ≤ 3 := by
      dsimp [P]
      exact natDegree_xSubQuadraticCubic_le a b c d e μ
    have hsplits := splits_of_three_ordered_roots_of_natDegree_le
      hP_ne hdeg_le hL1 h12 hrL_root hP_r₁ hP_r₂
    simpa [P] using hsplits

/-- Strict ordinary interleaving case `c < a < d < b < e < 0` for the
normalized quadratic/cubic pencil, as a specialization of the general endpoint. -/
lemma xSubQuadraticCubicSplits_of_order_c_a_d_b_e
    {a b c d e μ : ℝ} (hca : c < a) (had : a < d) (hdb : d < b)
    (hbe : b < e) (he0 : e < 0) (hμ : 0 < μ) :
    (xSubQuadraticCubic a b c d e μ).Splits := by
  apply normalized_cubic <;> linarith

/-- Strict nonordinary case `c < d < a < b < e < 0` for the normalized
quadratic/cubic leaf.  This is parallel to
`xSubQuadraticCubicSplits_of_order_c_a_d_b_e`, with the first finite sign
change on `(d, a)`. -/
lemma xSubQuadraticCubicSplits_of_order_c_d_a_b_e
    {a b c d e μ : ℝ} (hcd : c < d) (hda : d < a) (hab : a < b)
    (hbe : b < e) (he0 : e < 0) (hμ : 0 < μ) :
    (xSubQuadraticCubic a b c d e μ).Splits := by
  apply normalized_cubic <;> linarith

/-- Strict endpoint order `c < a < d < e < b < 0` for the normalized
quadratic/cubic leaf.  The first finite sign change is on `(a, d)`, while the
second is on `(e, b)`. -/
lemma xSubQuadraticCubicSplits_of_order_c_a_d_e_b
    {a b c d e μ : ℝ} (hca : c < a) (had : a < d) (hde : d < e)
    (heb : e < b) (hb0 : b < 0) (hμ : 0 < μ) :
    (xSubQuadraticCubic a b c d e μ).Splits := by
  apply normalized_cubic <;> linarith

/-- Strict endpoint order `c < d < a < e < b < 0` for the normalized
quadratic/cubic leaf.  This is the remaining strict total order compatible with
the endpoint inequalities. -/
lemma xSubQuadraticCubicSplits_of_order_c_d_a_e_b
    {a b c d e μ : ℝ} (hcd : c < d) (hda : d < a) (hae : a < e)
    (heb : e < b) (hb0 : b < 0) (hμ : 0 < μ) :
    (xSubQuadraticCubic a b c d e μ).Splits := by
  apply normalized_cubic <;> linarith

/-- Strict shared-root-free quadratic/cubic endpoint data reduces to one of
the four strict total orders. -/
lemma xSubQuadraticCubicSplits_of_strict_no_common_middle_roots
    {a b c d e μ : ℝ} (hab : a < b) (hcd : c < d) (hde : d < e)
    (hca : c < a) (hdb : d < b) (hae : a < e)
    (had_ne : a ≠ d) (hbe_ne : b ≠ e) (hb0 : b < 0) (he0 : e < 0)
    (hμ : 0 < μ) :
    (xSubQuadraticCubic a b c d e μ).Splits := by
  rcases lt_or_gt_of_ne had_ne with had | hda <;>
    rcases lt_or_gt_of_ne hbe_ne with hbe | heb
  · exact xSubQuadraticCubicSplits_of_order_c_a_d_b_e hca had hdb hbe he0 hμ
  · exact xSubQuadraticCubicSplits_of_order_c_a_d_e_b hca had hde heb hb0 hμ
  · exact xSubQuadraticCubicSplits_of_order_c_d_a_b_e hcd hda hab hbe he0 hμ
  · exact xSubQuadraticCubicSplits_of_order_c_d_a_e_b hcd hda hae heb hb0 hμ

/-- A difference of two monic quadratics splits when their roots satisfy the
weak endpoint inequalities appearing in the quadratic/cubic boundary case. -/
lemma quadraticSubQuadratic_splits_of_roots_le
    {a b c d μ : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hca : c ≤ a) (hdb : d ≤ b) (hμ : 0 < μ) :
    (((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).Splits := by
  have hpoly :
      ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C d)) =
        C (1 - μ) * X ^ 2 + C (-(a + b) + μ * (c + d)) * X +
          C (a * b - μ * (c * d)) := by
    simp only [C_add, C_mul, C_neg, C_sub, C_1]
    ring_nf
  have hdisc :
      0 ≤ discrim (1 - μ) (-(a + b) + μ * (c + d))
        (a * b - μ * (c * d)) := by
    by_cases hda : d ≤ a
    · let u : ℝ := d - c
      let v : ℝ := a - d
      let w : ℝ := b - a
      have hu : 0 ≤ u := by
        dsimp [u]
        linarith
      have hv : 0 ≤ v := by
        dsimp [v]
        linarith
      have hw : 0 ≤ w := by
        dsimp [w]
        linarith
      have hdisc_eq :
          discrim (1 - μ) (-(a + b) + μ * (c + d))
              (a * b - μ * (c * d)) =
            (μ * u + w) ^ 2 + 4 * μ * v * (u + v + w) := by
        dsimp [u, v, w]
        unfold discrim
        ring_nf
      rw [hdisc_eq]
      positivity
    · have had : a ≤ d := le_of_not_ge hda
      let u : ℝ := a - c
      let v : ℝ := d - a
      let w : ℝ := b - d
      have hu : 0 ≤ u := by
        dsimp [u]
        linarith
      have hv : 0 ≤ v := by
        dsimp [v]
        linarith
      have hw : 0 ≤ w := by
        dsimp [w]
        linarith
      have hdisc_eq :
          discrim (1 - μ) (-(a + b) + μ * (c + d))
              (a * b - μ * (c * d)) =
            (μ * (u + v) - (v + w)) ^ 2 + 4 * μ * u * w := by
        dsimp [u, v, w]
        unfold discrim
        ring_nf
      rw [hdisc_eq]
      positivity
  simpa [hpoly] using quadraticPoly_splits_of_discrim_nonneg_or_linear hdisc

/-- Boundary case where the upper cubic root is zero.  Factoring out `X`
leaves a difference of two monic quadratics. -/
lemma xSubQuadraticCubicSplits_of_right_root_zero
    {a b c d μ : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hca : c ≤ a) (hdb : d ≤ b) (hμ : 0 < μ) :
    (xSubQuadraticCubic a b c d 0 μ).Splits := by
  have hquad :
      (((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d))).Splits :=
    quadraticSubQuadratic_splits_of_roots_le hab hcd hca hdb hμ
  have hfactor :
      xSubQuadraticCubic a b c d 0 μ =
          X * (((X - C a) * (X - C b)) -
            C μ * ((X - C c) * (X - C d))) := by
    unfold xSubQuadraticCubic
    simp only [map_zero, sub_zero]
    ring
  rw [hfactor]
  exact Polynomial.Splits.X.mul hquad

/-- Common-root boundary for the normalized quadratic/cubic leaf.  Factoring
out the shared linear factor leaves the already proved linear/quadratic
x-subtraction endpoint. -/
lemma xSubQuadraticCubicSplits_of_common_root
    {r s u v μ : ℝ} (huv : u ≤ v) (hus : u ≤ s)
    (hv0 : v ≤ 0) (hs0 : s ≤ 0) (hμ : 0 < μ) :
    (xSubQuadraticCubic r s r u v μ).Splits := by
  have hquad :
      (X * (X - C s) - C μ * ((X - C u) * (X - C v))).Splits :=
    xSubLinearQuadraticSplits huv hus hv0 hs0 hμ
  have hfactor :
      xSubQuadraticCubic r s r u v μ =
          (X - C r) *
            (X * (X - C s) - C μ * ((X - C u) * (X - C v))) := by
    unfold xSubQuadraticCubic
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C r).mul hquad

/-- Boundary case where the middle cubic root is the lower quadratic root. -/
lemma xSubQuadraticCubicSplits_of_middle_common_root
    {a b c e μ : ℝ} (hca : c ≤ a) (hab : a ≤ b) (hae : a ≤ e)
    (hb0 : b ≤ 0) (he0 : e ≤ 0) (hμ : 0 < μ) :
    (xSubQuadraticCubic a b c a e μ).Splits := by
  apply normalized_cubic <;> linarith

/-- Boundary case where the upper cubic root is the lower quadratic root. -/
lemma xSubQuadraticCubicSplits_of_left_upper_common_root
    {a b c d μ : ℝ} (hcd : c ≤ d) (hca : c ≤ a) (hda : d ≤ a)
    (hab : a ≤ b) (hb0 : b ≤ 0) (hμ : 0 < μ) :
    (xSubQuadraticCubic a b c d a μ).Splits := by
  apply normalized_cubic <;> linarith

/-- Boundary case where the middle cubic root is the upper quadratic root. -/
lemma xSubQuadraticCubicSplits_of_right_middle_common_root
    {a b c e μ : ℝ} (hab : a ≤ b) (hce : c ≤ e) (hca : c ≤ a)
    (hb0 : b ≤ 0) (he0 : e ≤ 0) (hμ : 0 < μ) :
    (xSubQuadraticCubic a b c b e μ).Splits := by
  have ha0 : a ≤ 0 := hab.trans hb0
  have hsplits := xSubQuadraticCubicSplits_of_common_root
    (r := b) (s := a) (u := c) (v := e) hce hca he0 ha0 hμ
  simpa [xSubQuadraticCubic, mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Boundary case where the upper cubic root is the upper quadratic root. -/
lemma xSubQuadraticCubicSplits_of_upper_common_root
    {a b c d μ : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hca : c ≤ a)
    (hdb : d ≤ b) (hb0 : b ≤ 0) (hμ : 0 < μ) :
    (xSubQuadraticCubic a b c d b μ).Splits := by
  apply normalized_cubic <;> linarith

/-- Boundary case where the quadratic endpoint has a double root. -/
lemma xSubQuadraticCubicSplits_of_left_double_root
    {a c d e μ : ℝ} (hcd : c < d) (hda : d < a) (hae : a < e)
    (he0 : e < 0) (hμ : 0 < μ) :
    (xSubQuadraticCubic a a c d e μ).Splits := by
  apply normalized_cubic <;> linarith

/-- Boundary case where the two lower cubic roots coincide. -/
lemma xSubQuadraticCubicSplits_of_lower_cubic_double_root
    {a b c e μ : ℝ} (hca : c < a) (hab : a ≤ b) (hbe : b < e)
    (he0 : e < 0) (hμ : 0 < μ) :
    (xSubQuadraticCubic a b c c e μ).Splits := by
  apply normalized_cubic <;> linarith

/-- Boundary case where the two lower cubic roots coincide and the remaining
cubic root lies below the upper quadratic root. -/
lemma xSubQuadraticCubicSplits_of_lower_cubic_double_root_right
    {a b c e μ : ℝ} (hca : c < a) (hae : a < e) (heb : e < b)
    (hb0 : b < 0) (hμ : 0 < μ) :
    (xSubQuadraticCubic a b c c e μ).Splits := by
  apply normalized_cubic <;> linarith

/-- Boundary case where the two upper cubic roots coincide. -/
lemma xSubQuadraticCubicSplits_of_upper_cubic_double_root
    {a b c d μ : ℝ} (hca : c < a) (had : a < d) (hdb : d < b)
    (hb0 : b < 0) (hμ : 0 < μ) :
    (xSubQuadraticCubic a b c d d μ).Splits := by
  apply normalized_cubic <;> linarith

/-- Boundary case where the upper quadratic root is zero and no middle root is
shared. -/
lemma xSubQuadraticCubicSplits_of_left_root_zero
    {a c d e μ : ℝ} (hcd : c ≤ d) (hca : c < a) (hde : d ≤ e)
    (hae : a < e) (he0 : e < 0) (had_ne : a ≠ d) (hμ : 0 < μ) :
    (xSubQuadraticCubic a 0 c d e μ).Splits := by
  let P : ℝ[X] := xSubQuadraticCubic a 0 c d e μ
  have hd0 : d < 0 := lt_of_le_of_lt hde he0
  have ha0 : a < 0 := lt_trans hae he0
  have hc0 : c < 0 := lt_trans hca ha0
  have hP_c_neg : P.eval c < 0 := by
    simpa [P, eval_xSubQuadraticCubic] using
      mul_neg_of_neg_of_pos hc0
        (mul_pos_of_neg_of_neg (sub_neg.mpr hca) hc0)
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    exact xSubQuadraticCubic_eval_zero_neg a 0 c d e μ hc0 hd0 he0 hμ
  have hP_e_pos : 0 < P.eval e := by
    simpa [P, eval_xSubQuadraticCubic] using
      mul_pos_of_neg_of_neg he0
        (mul_neg_of_pos_of_neg (sub_pos.mpr hae) he0)
  rcases lt_or_gt_of_ne had_ne with had | hda
  · have hP_a_neg : P.eval a < 0 := by
      simpa [P, eval_xSubQuadraticCubic, mul_assoc] using
        neg_lt_zero.mpr
          (mul_pos hμ (mul_pos (sub_pos.mpr hca)
            (mul_pos_of_neg_of_neg (sub_neg.mpr had) (sub_neg.mpr hae))))
    have hP_d_pos : 0 < P.eval d := by
      simpa [P, eval_xSubQuadraticCubic] using
        mul_pos_of_neg_of_neg hd0
          (mul_neg_of_pos_of_neg (sub_pos.mpr had) hd0)
    obtain ⟨r₁, ha_r₁, hr₁_d, hr₁_root⟩ :=
      exists_isRoot_between_of_eval_mul_neg had
        (mul_neg_of_neg_of_pos hP_a_neg hP_d_pos)
    obtain ⟨r₂, he_r₂, hr₂_zero, hr₂_root⟩ :=
      exists_isRoot_between_of_eval_mul_neg he0
        (mul_neg_of_pos_of_neg hP_e_pos hP_zero_neg)
    have hleft_r₁ : c < r₁ := lt_trans hca ha_r₁
    have h12 : r₁ < r₂ := lt_trans hr₁_d (lt_of_le_of_lt hde he_r₂)
    exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
      hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root
  · have hP_d_neg : P.eval d < 0 := by
      simpa [P, eval_xSubQuadraticCubic] using
        mul_neg_of_neg_of_pos hd0
          (mul_pos_of_neg_of_neg (sub_neg.mpr hda) hd0)
    have hP_a_pos : 0 < P.eval a := by
      simpa [P, eval_xSubQuadraticCubic, mul_assoc] using
        neg_pos.mpr
          (mul_neg_of_pos_of_neg hμ (mul_neg_of_pos_of_neg
            (mul_pos (sub_pos.mpr hca) (sub_pos.mpr hda)) (sub_neg.mpr hae)))
    obtain ⟨r₁, hd_r₁, hr₁_a, hr₁_root⟩ :=
      exists_isRoot_between_of_eval_mul_neg hda
        (mul_neg_of_neg_of_pos hP_d_neg hP_a_pos)
    obtain ⟨r₂, he_r₂, hr₂_zero, hr₂_root⟩ :=
      exists_isRoot_between_of_eval_mul_neg he0
        (mul_neg_of_pos_of_neg hP_e_pos hP_zero_neg)
    have hleft_r₁ : c < r₁ := lt_of_le_of_lt hcd hd_r₁
    have h12 : r₁ < r₂ := lt_trans hr₁_a (lt_trans hae he_r₂)
    exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
      hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- The normalized monic quadratic/cubic x-subtraction pencil splits. -/
theorem xSubQuadraticCubicSplits {a b c d e μ : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hde : d ≤ e) (hca : c ≤ a)
    (hdb : d ≤ b) (hae : a ≤ e) (hb0 : b ≤ 0) (he0 : e ≤ 0)
    (hμ : 0 < μ) :
    (xSubQuadraticCubic a b c d e μ).Splits := by
  exact normalized_cubic hab hcd hde hca hdb hae hb0 he0 hμ

/-- Degree-two/degree-three positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_three
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 2) (hqdeg : q.natDegree = 3)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  exact hpair.xSub_splits_of_right_successor_nonneg hpnn hqnn (by lia) hμ

/-- Degree-three right endpoint case for the right-successor sign-normalized
x-subtraction leaf. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg : f.natDegree = 2 := by lia
  have hFdeg : (f.comp (X + C r)).natDegree = 2 := by simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 3 := by simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_three
    (hpair.comp_X_add_C r) hfnn hgnn hFdeg hGdeg hμ

/-- Endpoint cases through right degree three for the right-successor
sign-normalized x-subtraction leaf. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hle_two : g.natDegree ≤ 2
  · exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
      hpair hfnn hgnn hdeg hle_two
  · have hthree : g.natDegree = 3 := by lia
    exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three
      hpair hfnn hgnn hdeg hthree

end LiuOppositeSigns
end RealRooted
