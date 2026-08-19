import RealRooted.LiuOppositeSigns.XSub.LinearQuadratic
import RealRooted.LiuOppositeSigns.XSub.SplittingTools

/-!
# Liu quadratic/cubic x-subtraction leaf

This module contains the normalized quadratic/cubic positive-split
x-subtraction leaf used by the right-successor right-degree-three endpoint.
-/

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
    c ≤ a ∧ d ≤ b ∧ a ≤ e := by
  exact roots_order_of_positiveSplitRootCountPair_three_two
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

/-- Normalized monic arithmetic leaf for the degree-two/degree-three
right-successor positive-split x-subtraction endpoint. -/
def xSubQuadraticCubicSplitsStatement : Prop :=
  ∀ {a b c d e μ : ℝ},
    a ≤ b → c ≤ d → d ≤ e → c ≤ a → d ≤ b → a ≤ e →
      b ≤ 0 → e ≤ 0 → 0 < μ →
        (X * ((X - C a) * (X - C b)) -
            C μ * ((X - C c) * (X - C d) * (X - C e))).Splits

/-- Expanded form of the normalized quadratic/cubic endpoint polynomial. -/
lemma xSubQuadraticCubic_eq_cubic_expansion (a b c d e μ : ℝ) :
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e)) =
        C (1 - μ) * X ^ 3 + C (μ * (c + d + e) - (a + b)) * X ^ 2 +
          C (a * b - μ * (c * d + c * e + d * e)) * X +
            C (μ * c * d * e) := by
  simp only [C_add, C_sub, C_mul, C_1]
  ring_nf

/-- The normalized quadratic/cubic x-subtraction polynomial has degree at most
three. -/
lemma natDegree_xSubQuadraticCubic_le (a b c d e μ : ℝ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).natDegree ≤ 3 := by
  compute_degree

/-- When the top cubic terms cancel, the normalized quadratic/cubic
x-subtraction polynomial has degree at most two. -/
lemma natDegree_xSubQuadraticCubic_of_mu_one_le_two (a b c d e : ℝ) :
    (X * ((X - C a) * (X - C b)) -
      C (1 : ℝ) * ((X - C c) * (X - C d) * (X - C e))).natDegree ≤ 2 := by
  rw [xSubQuadraticCubic_eq_cubic_expansion]
  simp only [sub_self, map_zero, zero_mul, one_mul, map_sub, map_add, zero_add,
    map_mul]
  compute_degree

/-- Cubic coefficient of the normalized quadratic/cubic endpoint polynomial. -/
lemma coeff_three_xSubQuadraticCubic (a b c d e μ : ℝ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).coeff 3 = 1 - μ := by
  rw [xSubQuadraticCubic_eq_cubic_expansion]
  simp [Polynomial.coeff_mul_X_pow']

/-- Away from the cancellation value `μ = 1`, the normalized quadratic/cubic
x-subtraction polynomial is a genuine cubic. -/
lemma natDegree_xSubQuadraticCubic_of_mu_ne_one
    (a b c d e μ : ℝ) (hμ : μ ≠ 1) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).natDegree = 3 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_xSubQuadraticCubic_le a b c d e μ
  · rw [coeff_three_xSubQuadraticCubic]
    intro h
    exact hμ (by linarith)

/-- Away from the cancellation value `μ = 1`, the normalized quadratic/cubic
x-subtraction polynomial is nonzero. -/
lemma xSubQuadraticCubic_ne_zero_of_mu_ne_one
    (a b c d e μ : ℝ) (hμ : μ ≠ 1) :
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e)) ≠ 0 := by
  intro hzero
  have hdeg := natDegree_xSubQuadraticCubic_of_mu_ne_one a b c d e μ hμ
  rw [hzero] at hdeg
  norm_num at hdeg

/-- Leading coefficient of the normalized quadratic/cubic endpoint polynomial
away from the cancellation value `μ = 1`. -/
lemma leadingCoeff_xSubQuadraticCubic_of_mu_ne_one
    (a b c d e μ : ℝ) (hμ : μ ≠ 1) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).leadingCoeff = 1 - μ := by
  rw [Polynomial.leadingCoeff,
    natDegree_xSubQuadraticCubic_of_mu_ne_one a b c d e μ hμ,
    coeff_three_xSubQuadraticCubic]

/-- Positive-leading case for the normalized quadratic/cubic endpoint
polynomial. -/
lemma hasPosLeadingCoeff_xSubQuadraticCubic_of_mu_lt_one
    (a b c d e μ : ℝ) (hμ : μ < 1) :
    HasPosLeadingCoeff
      (X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d) * (X - C e))) := by
  unfold HasPosLeadingCoeff
  rw [leadingCoeff_xSubQuadraticCubic_of_mu_ne_one]
  · linarith
  · exact ne_of_lt hμ

/-- Negative-leading case, expressed as positivity of the negated normalized
quadratic/cubic endpoint polynomial. -/
lemma hasPosLeadingCoeff_neg_xSubQuadraticCubic_of_one_lt_mu
    (a b c d e μ : ℝ) (hμ : 1 < μ) :
    HasPosLeadingCoeff
      (-(X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d) * (X - C e)))) := by
  unfold HasPosLeadingCoeff
  rw [Polynomial.leadingCoeff_neg, leadingCoeff_xSubQuadraticCubic_of_mu_ne_one]
  · linarith
  · exact ne_of_gt hμ

/-- Evaluation form of the normalized quadratic/cubic x-subtraction leaf. -/
lemma eval_xSubQuadraticCubic (a b c d e μ x : ℝ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).eval x =
      x * ((x - a) * (x - b)) - μ * ((x - c) * (x - d) * (x - e)) := by
  simp only [eval_sub, eval_mul, eval_X, eval_C]

/-- If `μ < 1`, the normalized quadratic/cubic endpoint polynomial tends to
`+∞` at `+∞`. -/
lemma tendsto_eval_xSubQuadraticCubic_atTop_atTop_of_mu_lt_one
    (a b c d e μ : ℝ) (hμ : μ < 1) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C d) * (X - C e))).eval x)
      atTop atTop := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
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

/-- If `μ < 1`, the normalized quadratic/cubic endpoint polynomial tends to
`-∞` at `-∞`. -/
lemma tendsto_eval_xSubQuadraticCubic_atBot_atBot_of_mu_lt_one
    (a b c d e μ : ℝ) (hμ : μ < 1) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C d) * (X - C e))).eval x)
      atBot atBot := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
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
  have hP_odd : Odd P.natDegree := by
    dsimp [P]
    rw [natDegree_xSubQuadraticCubic_of_mu_ne_one]
    · norm_num
    · exact ne_of_lt hμ
  exact tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hP_pos hP_deg_pos hP_odd

/-- If `1 < μ`, the normalized quadratic/cubic endpoint polynomial tends to
`+∞` at `-∞`. -/
lemma tendsto_eval_xSubQuadraticCubic_atBot_atTop_of_one_lt_mu
    (a b c d e μ : ℝ) (hμ : 1 < μ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C d) * (X - C e))).eval x)
      atBot atTop := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
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
  simp only [eval_sub, eval_mul, eval_X, eval_C, neg_neg]
  rw [eval_xSubQuadraticCubic]

/-- If `1 < μ`, the normalized quadratic/cubic endpoint polynomial tends to
`-∞` at `+∞`. -/
lemma tendsto_eval_xSubQuadraticCubic_atTop_atBot_of_one_lt_mu
    (a b c d e μ : ℝ) (hμ : 1 < μ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C d) * (X - C e))).eval x)
      atTop atBot := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
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
  have htQ : Tendsto (fun x => Q.eval x) atTop atTop :=
    Q.tendsto_atTop_of_leadingCoeff_nonneg hQ_deg_pos hQ_pos.le
  have htneg := tendsto_neg_atTop_atBot.comp htQ
  convert htneg using 1
  ext x
  dsimp [Q]
  rw [eval_neg]
  simp only [eval_sub, eval_mul, eval_X, eval_C, neg_neg]
  rw [eval_xSubQuadraticCubic]

/-- The common splitting tail for the normalized quadratic/cubic endpoint:
two ordered finite roots, a negative value to their left, and a negative value
at zero imply splitting.  The proof splits on the leading coefficient:
`μ < 1` gives a right outer root, `1 < μ` gives a left outer root, and
`μ = 1` drops the degree to at most two. -/
lemma xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    {a b c d e μ l r₁ r₂ : ℝ}
    (hleft_neg :
      (X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d) * (X - C e))).eval l < 0)
    (hzero_neg :
      (X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d) * (X - C e))).eval 0 < 0)
    (hl1 : l < r₁) (h12 : r₁ < r₂) (hr2_0 : r₂ < 0)
    (hr₁ :
      (X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d) * (X - C e))).IsRoot r₁)
    (hr₂ :
      (X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d) * (X - C e))).IsRoot r₂) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
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
normalized quadratic/cubic leaf.  The proof uses the two finite sign changes
between `(a, d)` and `(b, e)`.  The third root is on the right when `μ < 1`,
on the left when `1 < μ`, and unnecessary when the cubic term cancels at
`μ = 1`. -/
lemma xSubQuadraticCubicSplits_of_order_c_a_d_b_e
    {a b c d e μ : ℝ} (hca : c < a) (had : a < d) (hdb : d < b)
    (hbe : b < e) (he0 : e < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  have hcd : c < d := lt_trans hca had
  have hde : d < e := lt_trans hdb hbe
  have hcb : c < b := lt_trans hcd hdb
  have hae : a < e := lt_trans had hde
  have hb0 : b < 0 := lt_trans hbe he0
  have hd0 : d < 0 := lt_trans hdb hb0
  have ha0 : a < 0 := lt_trans had hd0
  have hc0 : c < 0 := lt_trans hca ha0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_neg : a - d < 0 := sub_neg.mpr had
    have hae_neg : a - e < 0 := sub_neg.mpr hae
    have htail_pos : 0 < (a - d) * (a - e) :=
      mul_pos_of_neg_of_neg had_neg hae_neg
    have hG_pos : 0 < (a - c) * (a - d) * (a - e) := by nlinarith [mul_pos hac_pos htail_pos]
    nlinarith [mul_pos hμ hG_pos]
  have hP_d_pos : 0 < P.eval d := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hda_pos : 0 < d - a := sub_pos.mpr had
    have hdb_neg : d - b < 0 := sub_neg.mpr hdb
    have hprod_neg : (d - a) * (d - b) < 0 :=
      mul_neg_of_pos_of_neg hda_pos hdb_neg
    have hleft_pos : 0 < d * ((d - a) * (d - b)) :=
      mul_pos_of_neg_of_neg hd0 hprod_neg
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbd_pos : 0 < b - d := sub_pos.mpr hdb
    have hbe_neg : b - e < 0 := sub_neg.mpr hbe
    have hhead_pos : 0 < (b - c) * (b - d) := mul_pos hbc_pos hbd_pos
    have hG_neg : (b - c) * (b - d) * (b - e) < 0 := by
      nlinarith [mul_neg_of_pos_of_neg hhead_pos hbe_neg]
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_e_neg : P.eval e < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have heb_pos : 0 < e - b := sub_pos.mpr hbe
    have hprod_pos : 0 < (e - a) * (e - b) := mul_pos hea_pos heb_pos
    have hleft_neg : e * ((e - a) * (e - b)) < 0 :=
      mul_neg_of_neg_of_pos he0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hzd_pos : 0 < 0 - d := sub_pos.mpr hd0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - d) := mul_pos hzc_pos hzd_pos
    have hG_pos : 0 < (0 - c) * (0 - d) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, ha_r₁, hr₁_d, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg had
      (mul_neg_of_neg_of_pos hP_a_neg hP_d_pos)
  obtain ⟨r₂, hb_r₂, hr₂_e, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hbe
      (mul_neg_of_pos_of_neg hP_b_pos hP_e_neg)
  have hleft_r₁ : c < r₁ := lt_trans hca ha_r₁
  have h12 : r₁ < r₂ := lt_trans hr₁_d (lt_trans hdb hb_r₂)
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_e he0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Strict nonordinary case `c < d < a < b < e < 0` for the normalized
quadratic/cubic leaf.  This is parallel to
`xSubQuadraticCubicSplits_of_order_c_a_d_b_e`, with the first finite sign
change on `(d, a)`. -/
lemma xSubQuadraticCubicSplits_of_order_c_d_a_b_e
    {a b c d e μ : ℝ} (hcd : c < d) (hda : d < a) (hab : a < b)
    (hbe : b < e) (he0 : e < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  have hca : c < a := lt_trans hcd hda
  have hdb : d < b := lt_trans hda hab
  have hde : d < e := lt_trans hdb hbe
  have hcb : c < b := lt_trans hca hab
  have hae : a < e := lt_trans hab hbe
  have hb0 : b < 0 := lt_trans hbe he0
  have ha0 : a < 0 := lt_trans hab hb0
  have hd0 : d < 0 := lt_trans hda ha0
  have hc0 : c < 0 := lt_trans hcd hd0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hda_neg : d - a < 0 := sub_neg.mpr hda
    have hdb_neg : d - b < 0 := sub_neg.mpr hdb
    have hprod_pos : 0 < (d - a) * (d - b) :=
      mul_pos_of_neg_of_neg hda_neg hdb_neg
    have hleft_neg : d * ((d - a) * (d - b)) < 0 :=
      mul_neg_of_neg_of_pos hd0 hprod_pos
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_pos : 0 < a - d := sub_pos.mpr hda
    have hae_neg : a - e < 0 := sub_neg.mpr hae
    have hhead_pos : 0 < (a - c) * (a - d) := mul_pos hac_pos had_pos
    have hG_neg : (a - c) * (a - d) * (a - e) < 0 := by
      nlinarith [mul_neg_of_pos_of_neg hhead_pos hae_neg]
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbd_pos : 0 < b - d := sub_pos.mpr hdb
    have hbe_neg : b - e < 0 := sub_neg.mpr hbe
    have hhead_pos : 0 < (b - c) * (b - d) := mul_pos hbc_pos hbd_pos
    have hG_neg : (b - c) * (b - d) * (b - e) < 0 := by
      nlinarith [mul_neg_of_pos_of_neg hhead_pos hbe_neg]
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_e_neg : P.eval e < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have heb_pos : 0 < e - b := sub_pos.mpr hbe
    have hprod_pos : 0 < (e - a) * (e - b) := mul_pos hea_pos heb_pos
    have hleft_neg : e * ((e - a) * (e - b)) < 0 :=
      mul_neg_of_neg_of_pos he0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hzd_pos : 0 < 0 - d := sub_pos.mpr hd0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - d) := mul_pos hzc_pos hzd_pos
    have hG_pos : 0 < (0 - c) * (0 - d) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, hd_r₁, hr₁_a, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hda
      (mul_neg_of_neg_of_pos hP_d_neg hP_a_pos)
  obtain ⟨r₂, hb_r₂, hr₂_e, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hbe
      (mul_neg_of_pos_of_neg hP_b_pos hP_e_neg)
  have hleft_r₁ : c < r₁ := lt_trans hcd hd_r₁
  have h12 : r₁ < r₂ := lt_trans hr₁_a (lt_trans hab hb_r₂)
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_e he0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Strict endpoint order `c < a < d < e < b < 0` for the normalized
quadratic/cubic leaf.  The first finite sign change is on `(a, d)`, while the
second is on `(e, b)`. -/
lemma xSubQuadraticCubicSplits_of_order_c_a_d_e_b
    {a b c d e μ : ℝ} (hca : c < a) (had : a < d) (hde : d < e)
    (heb : e < b) (hb0 : b < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  have hcd : c < d := lt_trans hca had
  have hdb : d < b := lt_trans hde heb
  have hcb : c < b := lt_trans hcd hdb
  have hae : a < e := lt_trans had hde
  have he0 : e < 0 := lt_trans heb hb0
  have hd0 : d < 0 := lt_trans hde he0
  have ha0 : a < 0 := lt_trans had hd0
  have hc0 : c < 0 := lt_trans hca ha0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_neg : a - d < 0 := sub_neg.mpr had
    have hae_neg : a - e < 0 := sub_neg.mpr hae
    have htail_pos : 0 < (a - d) * (a - e) :=
      mul_pos_of_neg_of_neg had_neg hae_neg
    have hG_pos : 0 < (a - c) * (a - d) * (a - e) := by nlinarith [mul_pos hac_pos htail_pos]
    nlinarith [mul_pos hμ hG_pos]
  have hP_d_pos : 0 < P.eval d := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hda_pos : 0 < d - a := sub_pos.mpr had
    have hdb_neg : d - b < 0 := sub_neg.mpr hdb
    have hprod_neg : (d - a) * (d - b) < 0 :=
      mul_neg_of_pos_of_neg hda_pos hdb_neg
    have hleft_pos : 0 < d * ((d - a) * (d - b)) :=
      mul_pos_of_neg_of_neg hd0 hprod_neg
    nlinarith
  have hP_e_pos : 0 < P.eval e := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have heb_neg : e - b < 0 := sub_neg.mpr heb
    have hprod_neg : (e - a) * (e - b) < 0 :=
      mul_neg_of_pos_of_neg hea_pos heb_neg
    have hleft_pos : 0 < e * ((e - a) * (e - b)) :=
      mul_pos_of_neg_of_neg he0 hprod_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbd_pos : 0 < b - d := sub_pos.mpr hdb
    have hbe_pos : 0 < b - e := sub_pos.mpr heb
    have hhead_pos : 0 < (b - c) * (b - d) := mul_pos hbc_pos hbd_pos
    have hG_pos : 0 < (b - c) * (b - d) * (b - e) :=
      mul_pos hhead_pos hbe_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hzd_pos : 0 < 0 - d := sub_pos.mpr hd0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - d) := mul_pos hzc_pos hzd_pos
    have hG_pos : 0 < (0 - c) * (0 - d) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, ha_r₁, hr₁_d, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg had
      (mul_neg_of_neg_of_pos hP_a_neg hP_d_pos)
  obtain ⟨r₂, he_r₂, hr₂_b, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg heb
      (mul_neg_of_pos_of_neg hP_e_pos hP_b_neg)
  have hleft_r₁ : c < r₁ := lt_trans hca ha_r₁
  have h12 : r₁ < r₂ := lt_trans hr₁_d (lt_trans hde he_r₂)
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_b hb0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Strict endpoint order `c < d < a < e < b < 0` for the normalized
quadratic/cubic leaf.  This is the remaining strict total order compatible with
the endpoint inequalities. -/
lemma xSubQuadraticCubicSplits_of_order_c_d_a_e_b
    {a b c d e μ : ℝ} (hcd : c < d) (hda : d < a) (hae : a < e)
    (heb : e < b) (hb0 : b < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  have hca : c < a := lt_trans hcd hda
  have hdb : d < b := lt_trans (lt_trans hda hae) heb
  have hcb : c < b := lt_trans hcd hdb
  have hde : d < e := lt_trans hda hae
  have he0 : e < 0 := lt_trans heb hb0
  have hd0 : d < 0 := lt_trans hde he0
  have hc0 : c < 0 := lt_trans hcd hd0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hda_neg : d - a < 0 := sub_neg.mpr hda
    have hdb_neg : d - b < 0 := sub_neg.mpr hdb
    have hprod_pos : 0 < (d - a) * (d - b) :=
      mul_pos_of_neg_of_neg hda_neg hdb_neg
    have hleft_neg : d * ((d - a) * (d - b)) < 0 :=
      mul_neg_of_neg_of_pos hd0 hprod_pos
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_pos : 0 < a - d := sub_pos.mpr hda
    have hae_neg : a - e < 0 := sub_neg.mpr hae
    have hhead_pos : 0 < (a - c) * (a - d) := mul_pos hac_pos had_pos
    have hG_neg : (a - c) * (a - d) * (a - e) < 0 := by
      nlinarith [mul_neg_of_pos_of_neg hhead_pos hae_neg]
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_e_pos : 0 < P.eval e := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have heb_neg : e - b < 0 := sub_neg.mpr heb
    have hprod_neg : (e - a) * (e - b) < 0 :=
      mul_neg_of_pos_of_neg hea_pos heb_neg
    have hleft_pos : 0 < e * ((e - a) * (e - b)) :=
      mul_pos_of_neg_of_neg he0 hprod_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbd_pos : 0 < b - d := sub_pos.mpr hdb
    have hbe_pos : 0 < b - e := sub_pos.mpr heb
    have hhead_pos : 0 < (b - c) * (b - d) := mul_pos hbc_pos hbd_pos
    have hG_pos : 0 < (b - c) * (b - d) * (b - e) :=
      mul_pos hhead_pos hbe_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hzd_pos : 0 < 0 - d := sub_pos.mpr hd0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - d) := mul_pos hzc_pos hzd_pos
    have hG_pos : 0 < (0 - c) * (0 - d) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, hd_r₁, hr₁_a, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hda
      (mul_neg_of_neg_of_pos hP_d_neg hP_a_pos)
  obtain ⟨r₂, he_r₂, hr₂_b, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg heb
      (mul_neg_of_pos_of_neg hP_e_pos hP_b_neg)
  have hleft_r₁ : c < r₁ := lt_trans hcd hd_r₁
  have h12 : r₁ < r₂ := lt_trans hr₁_a (lt_trans hae he_r₂)
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_b hb0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Strict shared-root-free quadratic/cubic endpoint data reduces to one of
the four strict total orders. -/
lemma xSubQuadraticCubicSplits_of_strict_no_common_middle_roots
    {a b c d e μ : ℝ} (hab : a < b) (hcd : c < d) (hde : d < e)
    (hca : c < a) (hdb : d < b) (hae : a < e)
    (had_ne : a ≠ d) (hbe_ne : b ≠ e) (hb0 : b < 0) (he0 : e < 0)
    (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  rcases lt_or_gt_of_ne had_ne with had | hda
  · rcases lt_or_gt_of_ne hbe_ne with hbe | heb
    · exact xSubQuadraticCubicSplits_of_order_c_a_d_b_e
        hca had hdb hbe he0 hμ
    · exact xSubQuadraticCubicSplits_of_order_c_a_d_e_b
        hca had hde heb hb0 hμ
  · rcases lt_or_gt_of_ne hbe_ne with hbe | heb
    · exact xSubQuadraticCubicSplits_of_order_c_d_a_b_e
        hcd hda hab hbe he0 hμ
    · exact xSubQuadraticCubicSplits_of_order_c_d_a_e_b
        hcd hda hae heb hb0 hμ

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
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * X)).Splits := by
  have hquad :
      (((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d))).Splits :=
    quadraticSubQuadratic_splits_of_roots_le hab hcd hca hdb hμ
  have hfactor :
      X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d) * X) =
          X * (((X - C a) * (X - C b)) -
            C μ * ((X - C c) * (X - C d))) := by
    ring
  rw [hfactor]
  exact Polynomial.Splits.X.mul hquad

/-- Common-root boundary for the normalized quadratic/cubic leaf.  Factoring
out the shared linear factor leaves the already proved linear/quadratic
x-subtraction endpoint. -/
lemma xSubQuadraticCubicSplits_of_common_root
    {r s u v μ : ℝ} (huv : u ≤ v) (hus : u ≤ s)
    (hv0 : v ≤ 0) (hs0 : s ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C r) * (X - C s)) -
      C μ * ((X - C r) * (X - C u) * (X - C v))).Splits := by
  have hquad :
      (X * (X - C s) - C μ * ((X - C u) * (X - C v))).Splits :=
    xSubLinearQuadraticSplits huv hus hv0 hs0 hμ
  have hfactor :
      X * ((X - C r) * (X - C s)) -
        C μ * ((X - C r) * (X - C u) * (X - C v)) =
          (X - C r) *
            (X * (X - C s) - C μ * ((X - C u) * (X - C v))) := by
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C r).mul hquad

/-- Boundary case where the lower cubic root is the lower quadratic root. -/
lemma xSubQuadraticCubicSplits_of_lower_common_root
    {a b d e μ : ℝ} (hde : d ≤ e) (hdb : d ≤ b)
    (hb0 : b ≤ 0) (he0 : e ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C a) * (X - C d) * (X - C e))).Splits :=
  xSubQuadraticCubicSplits_of_common_root
    (r := a) (s := b) (u := d) (v := e) hde hdb he0 hb0 hμ

/-- Boundary case where the middle cubic root is the lower quadratic root. -/
lemma xSubQuadraticCubicSplits_of_middle_common_root
    {a b c e μ : ℝ} (hca : c ≤ a) (hab : a ≤ b) (hae : a ≤ e)
    (hb0 : b ≤ 0) (he0 : e ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C a) * (X - C e))).Splits := by
  have hce : c ≤ e := hca.trans hae
  have hcb : c ≤ b := hca.trans hab
  have hsplits := xSubQuadraticCubicSplits_of_common_root
    (r := a) (s := b) (u := c) (v := e) hce hcb he0 hb0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Boundary case where the upper cubic root is the lower quadratic root. -/
lemma xSubQuadraticCubicSplits_of_left_upper_common_root
    {a b c d μ : ℝ} (hcd : c ≤ d) (hca : c ≤ a) (hda : d ≤ a)
    (hab : a ≤ b) (hb0 : b ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C a))).Splits := by
  have hd0 : d ≤ 0 := hda.trans (hab.trans hb0)
  have hsplits := xSubQuadraticCubicSplits_of_common_root
    (r := a) (s := b) (u := c) (v := d) hcd (hca.trans hab)
    hd0 hb0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Boundary case where the middle cubic root is the upper quadratic root. -/
lemma xSubQuadraticCubicSplits_of_right_middle_common_root
    {a b c e μ : ℝ} (hab : a ≤ b) (hce : c ≤ e) (hca : c ≤ a)
    (hb0 : b ≤ 0) (he0 : e ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C b) * (X - C e))).Splits := by
  have ha0 : a ≤ 0 := hab.trans hb0
  have hsplits := xSubQuadraticCubicSplits_of_common_root
    (r := b) (s := a) (u := c) (v := e) hce hca he0 ha0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Boundary case where the upper cubic root is the upper quadratic root. -/
lemma xSubQuadraticCubicSplits_of_upper_common_root
    {a b c d μ : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hca : c ≤ a)
    (hdb : d ≤ b) (hb0 : b ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C b))).Splits := by
  have hd0 : d ≤ 0 := hdb.trans hb0
  have ha0 : a ≤ 0 := hab.trans hb0
  have hsplits := xSubQuadraticCubicSplits_of_common_root
    (r := b) (s := a) (u := c) (v := d) hcd hca hd0 ha0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits

/-- Boundary case where the quadratic endpoint has a double root. -/
lemma xSubQuadraticCubicSplits_of_left_double_root
    {a c d e μ : ℝ} (hcd : c < d) (hda : d < a) (hae : a < e)
    (he0 : e < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C a)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C a)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  have hca : c < a := lt_trans hcd hda
  have hd0 : d < 0 := lt_trans hda (lt_trans hae he0)
  have ha0 : a < 0 := lt_trans hae he0
  have hc0 : c < 0 := lt_trans hcd hd0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hprod_pos : 0 < (c - a) * (c - a) :=
      mul_pos_of_neg_of_neg hca_neg hca_neg
    have hleft_neg : c * ((c - a) * (c - a)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hda_neg : d - a < 0 := sub_neg.mpr hda
    have hprod_pos : 0 < (d - a) * (d - a) :=
      mul_pos_of_neg_of_neg hda_neg hda_neg
    have hleft_neg : d * ((d - a) * (d - a)) < 0 :=
      mul_neg_of_neg_of_pos hd0 hprod_pos
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_pos : 0 < a - d := sub_pos.mpr hda
    have hae_neg : a - e < 0 := sub_neg.mpr hae
    have hhead_pos : 0 < (a - c) * (a - d) := mul_pos hac_pos had_pos
    have hG_neg : (a - c) * (a - d) * (a - e) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos hae_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_e_neg : P.eval e < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have hprod_pos : 0 < (e - a) * (e - a) := mul_pos hea_pos hea_pos
    have hleft_neg : e * ((e - a) * (e - a)) < 0 :=
      mul_neg_of_neg_of_pos he0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hzd_pos : 0 < 0 - d := sub_pos.mpr hd0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - d) := mul_pos hzc_pos hzd_pos
    have hG_pos : 0 < (0 - c) * (0 - d) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, hd_r₁, hr₁_a, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hda
      (mul_neg_of_neg_of_pos hP_d_neg hP_a_pos)
  obtain ⟨r₂, ha_r₂, hr₂_e, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hae
      (mul_neg_of_pos_of_neg hP_a_pos hP_e_neg)
  have hleft_r₁ : c < r₁ := lt_trans hcd hd_r₁
  have h12 : r₁ < r₂ := lt_trans hr₁_a ha_r₂
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_e he0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Boundary case where the two lower cubic roots coincide. -/
lemma xSubQuadraticCubicSplits_of_lower_cubic_double_root
    {a b c e μ : ℝ} (hca : c < a) (hab : a ≤ b) (hbe : b < e)
    (he0 : e < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C c) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C c) * (X - C e))
  have hcb : c < b := lt_of_lt_of_le hca hab
  have hae : a < e := lt_of_le_of_lt hab hbe
  have hb0 : b < 0 := lt_trans hbe he0
  have ha0 : a < 0 := lt_of_le_of_lt hab hb0
  have hc0 : c < 0 := lt_trans hca ha0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have hae_neg : a - e < 0 := sub_neg.mpr hae
    have hhead_pos : 0 < (a - c) * (a - c) := mul_pos hac_pos hac_pos
    have hG_neg : (a - c) * (a - c) * (a - e) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos hae_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbe_neg : b - e < 0 := sub_neg.mpr hbe
    have hhead_pos : 0 < (b - c) * (b - c) := mul_pos hbc_pos hbc_pos
    have hG_neg : (b - c) * (b - c) * (b - e) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos hbe_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_e_neg : P.eval e < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have heb_pos : 0 < e - b := sub_pos.mpr hbe
    have hprod_pos : 0 < (e - a) * (e - b) := mul_pos hea_pos heb_pos
    have hleft_neg : e * ((e - a) * (e - b)) < 0 :=
      mul_neg_of_neg_of_pos he0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - c) := mul_pos hzc_pos hzc_pos
    have hG_pos : 0 < (0 - c) * (0 - c) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, hc_r₁, hr₁_a, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hca
      (mul_neg_of_neg_of_pos hP_c_neg hP_a_pos)
  obtain ⟨r₂, hb_r₂, hr₂_e, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hbe
      (mul_neg_of_pos_of_neg hP_b_pos hP_e_neg)
  have h12 : r₁ < r₂ := lt_trans hr₁_a (lt_of_le_of_lt hab hb_r₂)
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_e he0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hc_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Boundary case where the two lower cubic roots coincide and the remaining
cubic root lies below the upper quadratic root. -/
lemma xSubQuadraticCubicSplits_of_lower_cubic_double_root_right
    {a b c e μ : ℝ} (hca : c < a) (hae : a < e) (heb : e < b)
    (hb0 : b < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C c) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C c) * (X - C e))
  have hcb : c < b := lt_trans hca (lt_trans hae heb)
  have he0 : e < 0 := lt_trans heb hb0
  have ha0 : a < 0 := lt_trans hae he0
  have hc0 : c < 0 := lt_trans hca ha0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have hae_neg : a - e < 0 := sub_neg.mpr hae
    have hhead_pos : 0 < (a - c) * (a - c) := mul_pos hac_pos hac_pos
    have hG_neg : (a - c) * (a - c) * (a - e) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos hae_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_e_pos : 0 < P.eval e := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have heb_neg : e - b < 0 := sub_neg.mpr heb
    have hprod_neg : (e - a) * (e - b) < 0 :=
      mul_neg_of_pos_of_neg hea_pos heb_neg
    have hleft_pos : 0 < e * ((e - a) * (e - b)) :=
      mul_pos_of_neg_of_neg he0 hprod_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbe_pos : 0 < b - e := sub_pos.mpr heb
    have hhead_pos : 0 < (b - c) * (b - c) := mul_pos hbc_pos hbc_pos
    have hG_pos : 0 < (b - c) * (b - c) * (b - e) :=
      mul_pos hhead_pos hbe_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - c) := mul_pos hzc_pos hzc_pos
    have hG_pos : 0 < (0 - c) * (0 - c) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, hc_r₁, hr₁_a, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hca
      (mul_neg_of_neg_of_pos hP_c_neg hP_a_pos)
  obtain ⟨r₂, he_r₂, hr₂_b, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg heb
      (mul_neg_of_pos_of_neg hP_e_pos hP_b_neg)
  have h12 : r₁ < r₂ := lt_trans hr₁_a (lt_trans hae he_r₂)
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_b hb0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hc_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Boundary case where the two upper cubic roots coincide. -/
lemma xSubQuadraticCubicSplits_of_upper_cubic_double_root
    {a b c d μ : ℝ} (hca : c < a) (had : a < d) (hdb : d < b)
    (hb0 : b < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C d))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d) * (X - C d))
  have hcd : c < d := lt_trans hca had
  have hcb : c < b := lt_trans hcd hdb
  have hd0 : d < 0 := lt_trans hdb hb0
  have ha0 : a < 0 := lt_trans had hd0
  have hc0 : c < 0 := lt_trans hca ha0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_neg : a - d < 0 := sub_neg.mpr had
    have htail_pos : 0 < (a - d) * (a - d) :=
      mul_pos_of_neg_of_neg had_neg had_neg
    have hG_pos : 0 < (a - c) * (a - d) * (a - d) := by nlinarith [mul_pos hac_pos htail_pos]
    nlinarith [mul_pos hμ hG_pos]
  have hP_d_pos : 0 < P.eval d := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hda_pos : 0 < d - a := sub_pos.mpr had
    have hdb_neg : d - b < 0 := sub_neg.mpr hdb
    have hprod_neg : (d - a) * (d - b) < 0 :=
      mul_neg_of_pos_of_neg hda_pos hdb_neg
    have hleft_pos : 0 < d * ((d - a) * (d - b)) :=
      mul_pos_of_neg_of_neg hd0 hprod_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbd_pos : 0 < b - d := sub_pos.mpr hdb
    have htail_pos : 0 < (b - d) * (b - d) := mul_pos hbd_pos hbd_pos
    have hG_pos : 0 < (b - c) * (b - d) * (b - d) := by nlinarith [mul_pos hbc_pos htail_pos]
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hzd_pos : 0 < 0 - d := sub_pos.mpr hd0
    have hhead_pos : 0 < (0 - c) * (0 - d) := mul_pos hzc_pos hzd_pos
    have hG_pos : 0 < (0 - c) * (0 - d) * (0 - d) :=
      mul_pos hhead_pos hzd_pos
    nlinarith [mul_pos hμ hG_pos]
  obtain ⟨r₁, ha_r₁, hr₁_d, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg had
      (mul_neg_of_neg_of_pos hP_a_neg hP_d_pos)
  obtain ⟨r₂, hd_r₂, hr₂_b, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hdb
      (mul_neg_of_pos_of_neg hP_d_pos hP_b_neg)
  have hleft_r₁ : c < r₁ := lt_trans hca ha_r₁
  have h12 : r₁ < r₂ := lt_trans hr₁_d hd_r₂
  have hr₂_zero : r₂ < 0 := lt_trans hr₂_b hb0
  exact xSubQuadraticCubic_splits_of_two_ordered_roots_and_eval_neg
    hP_c_neg hP_zero_neg hleft_r₁ h12 hr₂_zero hr₁_root hr₂_root

/-- Boundary case where the upper quadratic root is zero and no middle root is
shared. -/
lemma xSubQuadraticCubicSplits_of_left_root_zero
    {a c d e μ : ℝ} (hcd : c ≤ d) (hca : c < a) (hde : d ≤ e)
    (hae : a < e) (he0 : e < 0) (had_ne : a ≠ d) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C 0)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C 0)) -
      C μ * ((X - C c) * (X - C d) * (X - C e))
  have hd0 : d < 0 := lt_of_le_of_lt hde he0
  have ha0 : a < 0 := lt_trans hae he0
  have hc0 : c < 0 := lt_trans hca ha0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hc_neg : c - 0 < 0 := by simpa using hc0
    have hprod_pos : 0 < (c - a) * (c - 0) :=
      mul_pos_of_neg_of_neg hca_neg hc_neg
    have hleft_neg : c * ((c - a) * (c - 0)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hzc_pos : 0 < 0 - c := sub_pos.mpr hc0
    have hzd_pos : 0 < 0 - d := sub_pos.mpr hd0
    have hze_pos : 0 < 0 - e := sub_pos.mpr he0
    have hhead_pos : 0 < (0 - c) * (0 - d) := mul_pos hzc_pos hzd_pos
    have hG_pos : 0 < (0 - c) * (0 - d) * (0 - e) :=
      mul_pos hhead_pos hze_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_e_pos : 0 < P.eval e := by
    dsimp [P]
    rw [eval_xSubQuadraticCubic]
    have hea_pos : 0 < e - a := sub_pos.mpr hae
    have he_neg : e - 0 < 0 := by simpa using he0
    have hprod_neg : (e - a) * (e - 0) < 0 :=
      mul_neg_of_pos_of_neg hea_pos he_neg
    have hleft_pos : 0 < e * ((e - a) * (e - 0)) :=
      mul_pos_of_neg_of_neg he0 hprod_neg
    nlinarith
  rcases lt_or_gt_of_ne had_ne with had | hda
  · have hP_a_neg : P.eval a < 0 := by
      dsimp [P]
      rw [eval_xSubQuadraticCubic]
      have hac_pos : 0 < a - c := sub_pos.mpr hca
      have had_neg : a - d < 0 := sub_neg.mpr had
      have hae_neg : a - e < 0 := sub_neg.mpr hae
      have htail_pos : 0 < (a - d) * (a - e) :=
        mul_pos_of_neg_of_neg had_neg hae_neg
      have hG_pos : 0 < (a - c) * (a - d) * (a - e) := by nlinarith [mul_pos hac_pos htail_pos]
      nlinarith [mul_pos hμ hG_pos]
    have hP_d_pos : 0 < P.eval d := by
      dsimp [P]
      rw [eval_xSubQuadraticCubic]
      have hda_pos : 0 < d - a := sub_pos.mpr had
      have hd_neg : d - 0 < 0 := by simpa using hd0
      have hprod_neg : (d - a) * (d - 0) < 0 :=
        mul_neg_of_pos_of_neg hda_pos hd_neg
      have hleft_pos : 0 < d * ((d - a) * (d - 0)) :=
        mul_pos_of_neg_of_neg hd0 hprod_neg
      nlinarith
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
      dsimp [P]
      rw [eval_xSubQuadraticCubic]
      have hda_neg : d - a < 0 := sub_neg.mpr hda
      have hd_neg : d - 0 < 0 := by simpa using hd0
      have hprod_pos : 0 < (d - a) * (d - 0) :=
        mul_pos_of_neg_of_neg hda_neg hd_neg
      have hleft_neg : d * ((d - a) * (d - 0)) < 0 :=
        mul_neg_of_neg_of_pos hd0 hprod_pos
      nlinarith
    have hP_a_pos : 0 < P.eval a := by
      dsimp [P]
      rw [eval_xSubQuadraticCubic]
      have hac_pos : 0 < a - c := sub_pos.mpr hca
      have had_pos : 0 < a - d := sub_pos.mpr hda
      have hae_neg : a - e < 0 := sub_neg.mpr hae
      have hhead_pos : 0 < (a - c) * (a - d) := mul_pos hac_pos had_pos
      have hG_neg : (a - c) * (a - d) * (a - e) < 0 :=
        mul_neg_of_pos_of_neg hhead_pos hae_neg
      nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
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

/-- The normalized monic quadratic/cubic x-subtraction leaf. -/
theorem xSubQuadraticCubicSplits :
    xSubQuadraticCubicSplitsStatement := by
  intro a b c d e μ hab hcd hde hca hdb hae hb0 he0 hμ
  by_cases he_zero : e = 0
  · subst e
    simpa using xSubQuadraticCubicSplits_of_right_root_zero
      (a := a) (b := b) (c := c) (d := d) (μ := μ) hab hcd hca hdb hμ
  have he_lt : e < 0 := lt_of_le_of_ne he0 he_zero
  by_cases hca_eq : c = a
  · subst c
    exact xSubQuadraticCubicSplits_of_lower_common_root hde hdb hb0 he0 hμ
  by_cases had_eq : a = d
  · subst d
    exact xSubQuadraticCubicSplits_of_middle_common_root hca hab hae hb0 he0 hμ
  by_cases hae_eq : a = e
  · subst e
    have hda : d ≤ a := by simpa using hde
    exact xSubQuadraticCubicSplits_of_left_upper_common_root
      hcd hca hda hab hb0 hμ
  by_cases hdb_eq : d = b
  · subst b
    have hce : c ≤ e := hcd.trans hde
    exact xSubQuadraticCubicSplits_of_right_middle_common_root
      hab hce hca hb0 he0 hμ
  by_cases hbe_eq : b = e
  · subst e
    exact xSubQuadraticCubicSplits_of_upper_common_root
      hab hcd hca hdb hb0 hμ
  by_cases hb_zero : b = 0
  · subst b
    have hca_lt : c < a := lt_of_le_of_ne hca hca_eq
    have hae_lt : a < e := lt_of_le_of_ne hae hae_eq
    have hsplits := xSubQuadraticCubicSplits_of_left_root_zero
      hcd hca_lt hde hae_lt he_lt had_eq hμ
    simpa using hsplits
  have hb_lt : b < 0 := lt_of_le_of_ne hb0 hb_zero
  by_cases hcd_eq : c = d
  · subst d
    have hca_lt : c < a := lt_of_le_of_ne hca hca_eq
    rcases lt_or_gt_of_ne hbe_eq with hbe | heb
    · exact xSubQuadraticCubicSplits_of_lower_cubic_double_root
        hca_lt hab hbe he_lt hμ
    · have hae_lt : a < e := lt_of_le_of_ne hae hae_eq
      exact xSubQuadraticCubicSplits_of_lower_cubic_double_root_right
        hca_lt hae_lt heb hb_lt hμ
  by_cases hde_eq : d = e
  · subst e
    have hca_lt : c < a := lt_of_le_of_ne hca hca_eq
    have had_lt : a < d := lt_of_le_of_ne hae had_eq
    have hdb_lt : d < b := lt_of_le_of_ne hdb hdb_eq
    exact xSubQuadraticCubicSplits_of_upper_cubic_double_root
      hca_lt had_lt hdb_lt hb_lt hμ
  by_cases hab_eq : a = b
  · subst b
    have hcd_lt : c < d := lt_of_le_of_ne hcd hcd_eq
    have hda_lt : d < a := lt_of_le_of_ne hdb hdb_eq
    have hae_lt : a < e := lt_of_le_of_ne hae hae_eq
    exact xSubQuadraticCubicSplits_of_left_double_root
      hcd_lt hda_lt hae_lt he_lt hμ
  have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
  have hcd_lt : c < d := lt_of_le_of_ne hcd hcd_eq
  have hde_lt : d < e := lt_of_le_of_ne hde hde_eq
  have hca_lt : c < a := lt_of_le_of_ne hca hca_eq
  have hdb_lt : d < b := lt_of_le_of_ne hdb hdb_eq
  have hae_lt : a < e := lt_of_le_of_ne hae hae_eq
  exact xSubQuadraticCubicSplits_of_strict_no_common_middle_roots
    hab_lt hcd_lt hde_lt hca_lt hdb_lt hae_lt had_eq hbe_eq hb_lt he_lt hμ

/-- The normalized monic quadratic/cubic x-subtraction leaf implies the
degree-two/degree-three positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement)
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 2) (hqdeg : q.natDegree = 3)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  obtain ⟨a, b, c, d, e, hab, hcd, hde, hproots, hqroots,
      hpfac, hqfac, hca, hdb, hae⟩ :=
    exists_roots_order_of_positiveSplitRootCountPair_two_three
      hpair hpdeg hqdeg
  have hb0 : b ≤ 0 := by
    have hb_mem : b ∈ p.roots := by
      rw [hproots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hpnn b hb_mem
  have he0 : e ≤ 0 := by
    have he_mem : e ∈ q.roots := by
      rw [hqroots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hqnn e he_mem
  let A : ℝ := p.leadingCoeff
  let B : ℝ := q.leadingCoeff
  have hA_pos : 0 < A := by
    dsimp [A]
    exact hpair.left_pos
  have hB_pos : 0 < B := by
    dsimp [B]
    exact hpair.right_pos
  let ν : ℝ := μ * B / A
  have hν_pos : 0 < ν := by
    dsimp [ν]
    exact div_pos (mul_pos hμ hB_pos) hA_pos
  let inner : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C ν * ((X - C c) * (X - C d) * (X - C e))
  have hinner_splits : inner.Splits := by
    dsimp [inner]
    exact hmono hab hcd hde hca hdb hae hb0 he0 hν_pos
  have hpoly : X * p - C μ * q = C A * inner := by
    rw [hpfac, hqfac]
    dsimp [inner, ν, A, B]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    field_simp [hpair.left_pos.ne']
  rw [hpoly]
  exact hinner_splits.C_mul A

/-- Degree-two/degree-three positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_three
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 2) (hqdeg : q.natDegree = 3)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits :=
  splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_three_of_monic
    xSubQuadraticCubicSplits hpair hpnn hqnn hpdeg hqdeg hμ

/-- Degree-three right endpoint case for the right-successor sign-normalized
x-subtraction leaf, modulo the normalized monic quadratic/cubic leaf. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement)
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
  exact splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_three_of_monic
    hmono (hpair.comp_X_add_C r) hfnn hgnn hFdeg hGdeg hμ

/-- Degree-three right endpoint case for the right-successor sign-normalized
x-subtraction leaf. -/
theorem positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
    xSubQuadraticCubicSplits hpair hfnn hgnn hdeg hgdeg

/-- Endpoint cases through right degree three for the right-successor
sign-normalized x-subtraction leaf, modulo the normalized monic
quadratic/cubic leaf. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement)
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
    exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
      hmono hpair hfnn hgnn hdeg hthree

/-- Endpoint cases through right degree three for the right-successor
sign-normalized x-subtraction leaf. -/
theorem positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
    xSubQuadraticCubicSplits hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-three right endpoint terminal as a predicate-restricted
right-successor positive-split x-sub family, modulo the normalized monic
quadratic/cubic leaf. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement) :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact
    positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
      hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-three right endpoint terminal as a predicate-restricted
right-successor positive-split x-sub family. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
    xSubQuadraticCubicSplits

/-- Compatibility alias for the shorter historical degree-three predicate
name. -/
theorem
    positiveSplitRightSuccXSubFamilyPredicate_of_right_natDegree_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement) :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
    hmono

/-- Compatibility alias for the shorter historical degree-three predicate
name. -/
theorem positiveSplitRightSuccXSubFamilyPredicate_of_right_natDegree_three :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three

/-- Pack the endpoint cases through degree three as a predicate-restricted
right-successor positive-split x-sub family, modulo the normalized monic
quadratic/cubic leaf. -/
theorem
positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement) :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact
    positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
      hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the endpoint cases through degree three as a predicate-restricted
right-successor positive-split x-sub family. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three
    hpair hfnn hgnn hdeg hgdeg

/-- Compatibility alias for the shorter historical degree-three predicate
name. -/
theorem
    positiveSplitRightSuccXSubFamilyPredicate_of_right_natDegree_le_three_of_monic
    (hmono : xSubQuadraticCubicSplitsStatement) :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact
    positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
      hmono hpair hfnn hgnn hdeg hgdeg

/-- Compatibility alias for the shorter historical degree-three predicate
name. -/
theorem positiveSplitRightSuccXSubFamilyPredicate_of_right_natDegree_le_three :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) :=
  positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three

end LiuOppositeSigns
end RealRooted
