import RealRooted.LiuOppositeSigns.XSub.LinearQuadratic
import RealRooted.LiuOppositeSigns.XSub.SplittingTools

/-!
# Liu quadratic/quadratic x-subtraction leaf

This module contains the normalized quadratic/quadratic positive-split
x-subtraction leaf used by the same-degree right-degree-two endpoint.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- In the `(2, 2)` positive split root-count case, the two ordered root
intervals overlap. -/
lemma roots_overlap_of_positiveSplitRootCountPair_two_two
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hfroots : f.roots = {a, b}) (hgroots : g.roots = {c, d}) :
    a ≤ d ∧ c ≤ b := by
  constructor
  · by_contra had
    have hda : d < a := lt_of_not_ge had
    let x : ℝ := (a + d) / 2
    have hdx : d < x := by
      dsimp [x]
      linarith
    have hxa : x ≤ a := by
      dsimp [x]
      linarith
    have hxb : x ≤ b := hxa.trans hab
    have hcx : c < x := lt_of_le_of_lt hcd hdx
    have hcount := h.count.left_sub_le_one x
    have hf_count : rootCountAtOrAbove f x = 2 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons]
      rw [Multiset.filter_cons_of_pos ({b} : Multiset ℝ) hxa]
      rw [Multiset.filter_singleton (fun r : ℝ => x ≤ r), if_pos hxb]
      simp
    have hg_count : rootCountAtOrAbove g x = 0 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xc : ¬ x ≤ c := not_le.mpr hcx
      have hnot_xd : ¬ x ≤ d := not_le.mpr hdx
      simp [hnot_xc, hnot_xd]
    rw [hf_count, hg_count] at hcount
    norm_num at hcount
  · by_contra hcb
    have hbc : b < c := lt_of_not_ge hcb
    let x : ℝ := (b + c) / 2
    have hbx : b < x := by
      dsimp [x]
      linarith
    have hxc : x ≤ c := by
      dsimp [x]
      linarith
    have hxd : x ≤ d := hxc.trans hcd
    have hax : a < x := lt_of_le_of_lt hab hbx
    have hcount := h.count.right_sub_le_one x
    have hf_count : rootCountAtOrAbove f x = 0 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xa : ¬ x ≤ a := not_le.mpr hax
      have hnot_xb : ¬ x ≤ b := not_le.mpr hbx
      simp [hnot_xa, hnot_xb]
    have hg_count : rootCountAtOrAbove g x = 2 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons]
      rw [Multiset.filter_cons_of_pos ({d} : Multiset ℝ) hxc]
      rw [Multiset.filter_singleton (fun r : ℝ => x ≤ r), if_pos hxd]
      simp
    rw [hf_count, hg_count] at hcount
    norm_num at hcount

/-- Normalized monic arithmetic leaf for the degree-two/degree-two
x-subtraction endpoint. -/
def xSubQuadraticQuadraticSplitsStatement : Prop :=
  ∀ {a b c d μ : ℝ},
    a ≤ b → c ≤ d → a ≤ d → c ≤ b → b ≤ 0 → d ≤ 0 → 0 < μ →
      (X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d))).Splits

/-- A monic quadratic minus a positive multiple of a linear factor splits
whenever the linear root lies weakly below the upper quadratic root. -/
lemma quadraticSubLinear_splits_of_right_root_le_upper
    {a b c μ : ℝ} (hab : a ≤ b) (hcb : c ≤ b) (hμ : 0 < μ) :
    (((X - C a) * (X - C b)) - C μ * (X - C c)).Splits := by
  have hpoly :
      ((X - C a) * (X - C b)) - C μ * (X - C c) =
        C 1 * X ^ 2 + C (-(a + b + μ)) * X + C (a * b + μ * c) := by
    simp only [C_add, C_mul, C_neg, C_1]
    ring
  have hdisc : 0 ≤ discrim 1 (-(a + b + μ)) (a * b + μ * c) := by
    by_cases hac : a ≤ c
    · let u : ℝ := c - a
      let v : ℝ := b - c
      have hu : 0 ≤ u := by
        dsimp [u]
        linarith
      have hv : 0 ≤ v := by
        dsimp [v]
        linarith
      have hdisc_eq :
          discrim 1 (-(a + b + μ)) (a * b + μ * c) =
            (μ + v - u) ^ 2 + 4 * u * v := by
        dsimp [u, v]
        unfold discrim
        ring_nf
      rw [hdisc_eq]
      positivity
    · have hca : c ≤ a := le_of_not_ge hac
      let u : ℝ := a - c
      let v : ℝ := b - a
      have hu : 0 ≤ u := by
        dsimp [u]
        linarith
      have hv : 0 ≤ v := by
        dsimp [v]
        linarith
      have hdisc_eq :
          discrim 1 (-(a + b + μ)) (a * b + μ * c) =
            μ ^ 2 + 4 * μ * u + 2 * μ * v + v ^ 2 := by
        dsimp [u, v]
        unfold discrim
        ring_nf
      rw [hdisc_eq]
      positivity
  simpa [hpoly] using quadraticPoly_splits_of_discrim_nonneg one_ne_zero hdisc

/-- Boundary case of the quadratic/quadratic leaf when the right endpoint has
root zero.  Factoring out `X` leaves a quadratic-minus-linear pencil. -/
lemma xSubQuadraticQuadraticSplits_of_right_root_zero
    {a b c μ : ℝ} (hab : a ≤ b) (hcb : c ≤ b) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * X)).Splits := by
  have hquad : (((X - C a) * (X - C b)) - C μ * (X - C c)).Splits :=
    quadraticSubLinear_splits_of_right_root_le_upper hab hcb hμ
  have hfactor :
      X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * X) =
          X * (((X - C a) * (X - C b)) - C μ * (X - C c)) := by
    ring
  rw [hfactor]
  exact Polynomial.Splits.X.mul hquad

/-- Boundary case of the quadratic/quadratic leaf when the two quadratic
endpoints share a root. -/
lemma xSubQuadraticQuadraticSplits_of_common_root
    {r s t μ : ℝ} (hs0 : s ≤ 0) (ht0 : t ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C r) * (X - C s)) -
      C μ * ((X - C r) * (X - C t))).Splits := by
  have hquad₀ :
      (((X - C s) * (X - C 0)) - C μ * (X - C t)).Splits :=
    quadraticSubLinear_splits_of_right_root_le_upper
      (a := s) (b := 0) (c := t) hs0 ht0 hμ
  have hquad : (X * (X - C s) - C μ * (X - C t)).Splits := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hquad₀
  have hfactor :
      X * ((X - C r) * (X - C s)) -
        C μ * ((X - C r) * (X - C t)) =
          (X - C r) * (X * (X - C s) - C μ * (X - C t)) := by
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C r).mul hquad

/-- The normalized quadratic/quadratic x-subtraction polynomial is a genuine
cubic. -/
lemma natDegree_xSubQuadraticQuadratic (a b c d μ : ℝ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).natDegree = 3 := by
  compute_degree <;> norm_num

/-- The normalized quadratic/quadratic x-subtraction polynomial is nonzero. -/
lemma xSubQuadraticQuadratic_ne_zero (a b c d μ : ℝ) :
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d)) ≠ 0 := by
  intro hzero
  have hdeg := natDegree_xSubQuadraticQuadratic a b c d μ
  rw [hzero] at hdeg
  norm_num at hdeg

/-- The normalized quadratic/quadratic x-subtraction polynomial has positive
leading coefficient. -/
lemma hasPosLeadingCoeff_xSubQuadraticQuadratic (a b c d μ : ℝ) :
    HasPosLeadingCoeff
      (X * ((X - C a) * (X - C b)) -
        C μ * ((X - C c) * (X - C d))) := by
  have hquad_pos : HasPosLeadingCoeff ((X - C a) * (X - C b)) :=
    (hasPosLeadingCoeff_X_sub_C a).mul (hasPosLeadingCoeff_X_sub_C b)
  have hleft_pos : HasPosLeadingCoeff (X * ((X - C a) * (X - C b))) :=
    hquad_pos.X_mul
  have hleft_deg : (X * ((X - C a) * (X - C b))).natDegree = 3 := by compute_degree <;> norm_num
  have hdeg_lt : (C μ * ((X - C c) * (X - C d))).natDegree <
      (X * ((X - C a) * (X - C b))).natDegree := by
    rw [hleft_deg]
    compute_degree
    norm_num
  unfold HasPosLeadingCoeff at hleft_pos ⊢
  have hdegree_lt : degree (C μ * ((X - C c) * (X - C d))) <
      degree (X * ((X - C a) * (X - C b))) :=
    degree_lt_degree hdeg_lt
  rw [leadingCoeff_sub_of_degree_lt hdegree_lt]
  exact hleft_pos

/-- Evaluation form of the normalized quadratic/quadratic x-subtraction leaf. -/
lemma eval_xSubQuadraticQuadratic (a b c d μ x : ℝ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).eval x =
      x * ((x - a) * (x - b)) - μ * ((x - c) * (x - d)) := by
  simp only [eval_sub, eval_mul, eval_X, eval_C]

/-- The normalized quadratic/quadratic x-subtraction polynomial tends to
`-∞` at `-∞`. -/
lemma tendsto_eval_xSubQuadraticQuadratic_atBot_atBot (a b c d μ : ℝ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C d))).eval x)
      atBot atBot := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubQuadraticQuadratic a b c d μ
  have hP_deg : P.natDegree = 3 := by
    dsimp [P]
    exact natDegree_xSubQuadraticQuadratic a b c d μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      rw [hP_deg]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  have hP_odd : Odd P.natDegree := by
    rw [hP_deg]
    norm_num
  exact tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hP_pos hP_deg_pos hP_odd

/-- The normalized quadratic/quadratic x-subtraction polynomial tends to
`+∞` at `+∞`. -/
lemma tendsto_eval_xSubQuadraticQuadratic_atTop_atTop (a b c d μ : ℝ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b)) -
          C μ * ((X - C c) * (X - C d))).eval x)
      atTop atTop := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubQuadraticQuadratic a b c d μ
  have hP_deg : P.natDegree = 3 := by
    dsimp [P]
    exact natDegree_xSubQuadraticQuadratic a b c d μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      rw [hP_deg]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  exact P.tendsto_atTop_of_leadingCoeff_nonneg hP_deg_pos hP_pos.le

/-- Strict order case `a < c < b < d < 0` for the normalized
quadratic/quadratic leaf. -/
lemma xSubQuadraticQuadraticSplits_of_order_a_c_b_d
    {a b c d μ : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d)
    (hd0 : d < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))
  have had : a < d := lt_trans hac (lt_trans hcb hbd)
  have hc0 : c < 0 := lt_trans hcb (lt_trans hbd hd0)
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hG : 0 < (a - c) * (a - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hac) (sub_neg.mpr had)
    nlinarith [mul_pos hμ hG]
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hca_pos : 0 < c - a := sub_pos.mpr hac
    have hcb_neg : c - b < 0 := sub_neg.mpr hcb
    have hprod_neg : (c - a) * (c - b) < 0 :=
      mul_neg_of_pos_of_neg hca_pos hcb_neg
    have hleft_pos : 0 < c * ((c - a) * (c - b)) :=
      mul_pos_of_neg_of_neg hc0 hprod_neg
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hbc_pos : 0 < b - c := sub_pos.mpr hcb
    have hbd_neg : b - d < 0 := sub_neg.mpr hbd
    have hG_neg : (b - c) * (b - d) < 0 :=
      mul_neg_of_pos_of_neg hbc_pos hbd_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hda_pos : 0 < d - a := sub_pos.mpr had
    have hdb_pos : 0 < d - b := sub_pos.mpr hbd
    have hprod_pos : 0 < (d - a) * (d - b) := mul_pos hda_pos hdb_pos
    have hleft_neg : d * ((d - a) * (d - b)) < 0 :=
      mul_neg_of_neg_of_pos hd0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hG : 0 < (0 - c) * (0 - d) :=
      mul_pos (sub_pos.mpr hc0) (sub_pos.mpr hd0)
    nlinarith [mul_pos hμ hG]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubQuadraticQuadratic_atTop_atTop a b c d μ
  obtain ⟨r₁, ha_r₁, hr₁_c, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hac
      (mul_neg_of_neg_of_pos hP_a_neg hP_c_pos)
  obtain ⟨r₂, hb_r₂, hr₂_d, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hbd
      (mul_neg_of_pos_of_neg hP_b_pos hP_d_neg)
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
      (le_of_lt hP_zero_neg) ht_top
  have h12 : r₁ < r₂ := lt_trans hr₁_c (lt_trans hcb hb_r₂)
  have h2R : r₂ < rR :=
    lt_of_lt_of_le (lt_trans hr₂_d hd0) hrR_ge
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubQuadraticQuadratic_ne_zero a b c d μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_xSubQuadraticQuadratic]
  have hsplits := splits_of_three_ordered_roots_of_natDegree_le
    hP_ne hdeg_le h12 h2R hr₁_root hr₂_root hrR_root
  simpa [P] using hsplits

/-- Strict order case `a < c ≤ d < b ≤ 0` for the normalized
quadratic/quadratic leaf. -/
lemma xSubQuadraticQuadraticSplits_of_order_a_c_d_b
    {a b c d μ : ℝ} (hac : a < c) (hcd : c ≤ d) (hdb : d < b)
    (hb0 : b ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))
  have had : a < d := lt_of_lt_of_le hac hcd
  have hc0 : c < 0 := lt_of_le_of_lt hcd (lt_of_lt_of_le hdb hb0)
  have hd0 : d < 0 := lt_of_lt_of_le hdb hb0
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hG : 0 < (a - c) * (a - d) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hac) (sub_neg.mpr had)
    nlinarith [mul_pos hμ hG]
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hca_pos : 0 < c - a := sub_pos.mpr hac
    have hcb_neg : c - b < 0 :=
      sub_neg.mpr (lt_of_le_of_lt hcd hdb)
    have hprod_neg : (c - a) * (c - b) < 0 :=
      mul_neg_of_pos_of_neg hca_pos hcb_neg
    have hleft_pos : 0 < c * ((c - a) * (c - b)) :=
      mul_pos_of_neg_of_neg hc0 hprod_neg
    nlinarith
  have hP_d_pos : 0 < P.eval d := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hda_pos : 0 < d - a := sub_pos.mpr had
    have hdb_neg : d - b < 0 := sub_neg.mpr hdb
    have hprod_neg : (d - a) * (d - b) < 0 :=
      mul_neg_of_pos_of_neg hda_pos hdb_neg
    have hleft_pos : 0 < d * ((d - a) * (d - b)) :=
      mul_pos_of_neg_of_neg hd0 hprod_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hbc_pos : 0 < b - c := sub_pos.mpr (lt_of_le_of_lt hcd hdb)
    have hbd_pos : 0 < b - d := sub_pos.mpr hdb
    have hG : 0 < (b - c) * (b - d) := mul_pos hbc_pos hbd_pos
    nlinarith [mul_pos hμ hG]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hG : 0 < (0 - c) * (0 - d) :=
      mul_pos (sub_pos.mpr hc0) (sub_pos.mpr hd0)
    nlinarith [mul_pos hμ hG]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubQuadraticQuadratic_atTop_atTop a b c d μ
  obtain ⟨r₁, ha_r₁, hr₁_c, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hac
      (mul_neg_of_neg_of_pos hP_a_neg hP_c_pos)
  obtain ⟨r₂, hd_r₂, hr₂_b, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hdb
      (mul_neg_of_pos_of_neg hP_d_pos hP_b_neg)
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
      (le_of_lt hP_zero_neg) ht_top
  have h12 : r₁ < r₂ := lt_trans hr₁_c (lt_of_le_of_lt hcd hd_r₂)
  have h2R : r₂ < rR :=
    lt_of_lt_of_le (lt_of_lt_of_le hr₂_b hb0) hrR_ge
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubQuadraticQuadratic_ne_zero a b c d μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_xSubQuadraticQuadratic]
  have hsplits := splits_of_three_ordered_roots_of_natDegree_le
    hP_ne hdeg_le h12 h2R hr₁_root hr₂_root hrR_root
  simpa [P] using hsplits

/-- Strict order case `c < a ≤ b < d < 0` for the normalized
quadratic/quadratic leaf. -/
lemma xSubQuadraticQuadraticSplits_of_order_c_a_b_d
    {a b c d μ : ℝ} (hca : c < a) (hab : a ≤ b) (hbd : b < d)
    (hd0 : d < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))
  have cad : c < d := lt_trans hca (lt_of_le_of_lt hab hbd)
  have ha0 : a < 0 := lt_of_le_of_lt (hab.trans (le_of_lt hbd)) hd0
  have hc0 : c < 0 := lt_trans hca ha0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr (lt_of_lt_of_le hca hab)
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_neg : a - d < 0 := sub_neg.mpr (lt_of_le_of_lt hab hbd)
    have hG_neg : (a - c) * (a - d) < 0 :=
      mul_neg_of_pos_of_neg hac_pos had_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hbc_pos : 0 < b - c := sub_pos.mpr (lt_of_lt_of_le hca hab)
    have hbd_neg : b - d < 0 := sub_neg.mpr hbd
    have hG_neg : (b - c) * (b - d) < 0 :=
      mul_neg_of_pos_of_neg hbc_pos hbd_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hda_pos : 0 < d - a := sub_pos.mpr (lt_of_le_of_lt hab hbd)
    have hdb_pos : 0 < d - b := sub_pos.mpr hbd
    have hprod_pos : 0 < (d - a) * (d - b) := mul_pos hda_pos hdb_pos
    have hleft_neg : d * ((d - a) * (d - b)) < 0 :=
      mul_neg_of_neg_of_pos hd0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hG : 0 < (0 - c) * (0 - d) :=
      mul_pos (sub_pos.mpr hc0) (sub_pos.mpr hd0)
    nlinarith [mul_pos hμ hG]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubQuadraticQuadratic_atTop_atTop a b c d μ
  obtain ⟨r₁, hc_r₁, hr₁_a, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hca
      (mul_neg_of_neg_of_pos hP_c_neg hP_a_pos)
  obtain ⟨r₂, hb_r₂, hr₂_d, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hbd
      (mul_neg_of_pos_of_neg hP_b_pos hP_d_neg)
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
      (le_of_lt hP_zero_neg) ht_top
  have h12 : r₁ < r₂ := lt_trans hr₁_a (lt_of_le_of_lt hab hb_r₂)
  have h2R : r₂ < rR :=
    lt_of_lt_of_le (lt_trans hr₂_d hd0) hrR_ge
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubQuadraticQuadratic_ne_zero a b c d μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_xSubQuadraticQuadratic]
  have hsplits := splits_of_three_ordered_roots_of_natDegree_le
    hP_ne hdeg_le h12 h2R hr₁_root hr₂_root hrR_root
  simpa [P] using hsplits

/-- Strict order case `c < a < d < b ≤ 0` for the normalized
quadratic/quadratic leaf. -/
lemma xSubQuadraticQuadraticSplits_of_order_c_a_d_b
    {a b c d μ : ℝ} (hca : c < a) (had : a < d) (hdb : d < b)
    (hb0 : b ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b)) -
      C μ * ((X - C c) * (X - C d))
  have ha0 : a < 0 := lt_trans had (lt_of_lt_of_le hdb hb0)
  have hc0 : c < 0 := lt_trans hca ha0
  have hd0 : d < 0 := lt_of_lt_of_le hdb hb0
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hca_neg : c - a < 0 := sub_neg.mpr hca
    have hcb_neg : c - b < 0 := sub_neg.mpr (lt_trans hca (lt_trans had hdb))
    have hprod_pos : 0 < (c - a) * (c - b) :=
      mul_pos_of_neg_of_neg hca_neg hcb_neg
    have hleft_neg : c * ((c - a) * (c - b)) < 0 :=
      mul_neg_of_neg_of_pos hc0 hprod_pos
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have had_neg : a - d < 0 := sub_neg.mpr had
    have hG_neg : (a - c) * (a - d) < 0 :=
      mul_neg_of_pos_of_neg hac_pos had_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_d_pos : 0 < P.eval d := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hda_pos : 0 < d - a := sub_pos.mpr had
    have hdb_neg : d - b < 0 := sub_neg.mpr hdb
    have hprod_neg : (d - a) * (d - b) < 0 :=
      mul_neg_of_pos_of_neg hda_pos hdb_neg
    have hleft_pos : 0 < d * ((d - a) * (d - b)) :=
      mul_pos_of_neg_of_neg hd0 hprod_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hbc_pos : 0 < b - c := sub_pos.mpr (lt_trans hca (lt_trans had hdb))
    have hbd_pos : 0 < b - d := sub_pos.mpr hdb
    have hG : 0 < (b - c) * (b - d) := mul_pos hbc_pos hbd_pos
    nlinarith [mul_pos hμ hG]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubQuadraticQuadratic]
    have hG : 0 < (0 - c) * (0 - d) :=
      mul_pos (sub_pos.mpr hc0) (sub_pos.mpr hd0)
    nlinarith [mul_pos hμ hG]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubQuadraticQuadratic_atTop_atTop a b c d μ
  obtain ⟨r₁, hc_r₁, hr₁_a, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hca
      (mul_neg_of_neg_of_pos hP_c_neg hP_a_pos)
  obtain ⟨r₂, hd_r₂, hr₂_b, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hdb
      (mul_neg_of_pos_of_neg hP_d_pos hP_b_neg)
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
      (le_of_lt hP_zero_neg) ht_top
  have h12 : r₁ < r₂ := lt_trans hr₁_a (lt_trans had hd_r₂)
  have h2R : r₂ < rR :=
    lt_of_lt_of_le (lt_of_lt_of_le hr₂_b hb0) hrR_ge
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubQuadraticQuadratic_ne_zero a b c d μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_xSubQuadraticQuadratic]
  have hsplits := splits_of_three_ordered_roots_of_natDegree_le
    hP_ne hdeg_le h12 h2R hr₁_root hr₂_root hrR_root
  simpa [P] using hsplits

/-- The normalized monic quadratic/quadratic x-subtraction leaf. -/
theorem xSubQuadraticQuadraticSplits :
    xSubQuadraticQuadraticSplitsStatement := by
  intro a b c d μ hab hcd had hcb hb0 hd0 hμ
  by_cases hd_zero : d = 0
  · subst d
    simpa using xSubQuadraticQuadraticSplits_of_right_root_zero
      hab hcb hμ
  by_cases hac_eq : a = c
  · subst c
    exact xSubQuadraticQuadraticSplits_of_common_root
      (r := a) (s := b) (t := d) hb0 hd0 hμ
  by_cases had_eq : a = d
  · subst d
    have hc0 : c ≤ 0 := hcd.trans hd0
    have hsplits := xSubQuadraticQuadraticSplits_of_common_root
      (r := a) (s := b) (t := c) hb0 hc0 hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  by_cases hbc_eq : b = c
  · subst c
    have ha0 : a ≤ 0 := hab.trans hb0
    have hsplits := xSubQuadraticQuadraticSplits_of_common_root
      (r := b) (s := a) (t := d) ha0 hd0 hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  by_cases hbd_eq : b = d
  · subst d
    have ha0 : a ≤ 0 := hab.trans hb0
    have hc0 : c ≤ 0 := hcd.trans hb0
    have hsplits := xSubQuadraticQuadraticSplits_of_common_root
      (r := b) (s := a) (t := c) ha0 hc0 hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  have hdlt : d < 0 := lt_of_le_of_ne hd0 hd_zero
  rcases lt_or_gt_of_ne hac_eq with hac | hca
  · rcases lt_or_gt_of_ne hbd_eq with hbd | hdb
    · have hcb_lt : c < b := by exact lt_of_le_of_ne hcb (by intro h; exact hbc_eq h.symm)
      exact xSubQuadraticQuadraticSplits_of_order_a_c_b_d
        hac hcb_lt hbd hdlt hμ
    · exact xSubQuadraticQuadraticSplits_of_order_a_c_d_b
        hac hcd hdb hb0 hμ
  · rcases lt_or_gt_of_ne hbd_eq with hbd | hdb
    · exact xSubQuadraticQuadraticSplits_of_order_c_a_b_d
        hca hab hbd hdlt hμ
    · have had_lt : a < d := lt_of_le_of_ne had had_eq
      exact xSubQuadraticQuadraticSplits_of_order_c_a_d_b
        hca had_lt hdb hb0 hμ

/-- The normalized monic quadratic/quadratic x-subtraction leaf implies the
degree-two/degree-two positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement)
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 2) (hqdeg : q.natDegree = 2)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  obtain ⟨a, b, hab, hproots, hpfac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hpair.left_splits hpdeg
  obtain ⟨c, d, hcd, hqroots, hqfac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hpair.right_splits hqdeg
  obtain ⟨had, hcb⟩ :=
    roots_overlap_of_positiveSplitRootCountPair_two_two
      hpair hab hcd hproots hqroots
  have hb0 : b ≤ 0 := by
    have hb_mem : b ∈ p.roots := by
      rw [hproots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hpnn b hb_mem
  have hd0 : d ≤ 0 := by
    have hd_mem : d ∈ q.roots := by
      rw [hqroots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hqnn d hd_mem
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
    X * ((X - C a) * (X - C b)) - C ν * ((X - C c) * (X - C d))
  have hinner_splits : inner.Splits := by
    dsimp [inner]
    exact hmono hab hcd had hcb hb0 hd0 hν_pos
  have hpfacA : p = C A * ((X - C a) * (X - C b)) := by simpa [A] using hpfac
  have hqfacB : q = C B * ((X - C c) * (X - C d)) := by simpa [B] using hqfac
  have hpoly : X * p - C μ * q = C A * inner := by
    rw [hpfacA, hqfacB]
    dsimp [inner, ν]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    field_simp [hA_pos.ne']
  rw [hpoly]
  exact hinner_splits.C_mul A

/-- Degree-two/degree-two positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_two
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 2) (hqdeg : q.natDegree = 2)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits :=
  splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_two_of_monic
    xSubQuadraticQuadraticSplits hpair hpnn hqnn hpdeg hqdeg hμ

/-- Degree-two right endpoint reduction for the same-degree sign-normalized
x-subtraction leaf, modulo the normalized monic quadratic/quadratic leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg : f.natDegree = 2 := by lia
  have hFdeg : (f.comp (X + C r)).natDegree = 2 := by simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 2 := by simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_two_of_monic
    hmono (hpair.comp_X_add_C r) hfnn hgnn hFdeg hGdeg hμ

/-- Degree-two right endpoint case for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_two
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_two_of_monic
    xSubQuadraticQuadraticSplits hpair hfnn hgnn hdeg hgdeg

/-- Endpoint cases through right degree two for the same-degree
sign-normalized x-subtraction leaf, modulo the normalized monic
quadratic/quadratic leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree ≤ 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hle_one : g.natDegree ≤ 1
  · exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_one
      hpair hfnn hgnn hdeg hle_one
  · have htwo : g.natDegree = 2 := by lia
    exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_two_of_monic
      hmono hpair hfnn hgnn hdeg htwo

/-- Endpoint cases through right degree two for the same-degree
sign-normalized x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree ≤ 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two_of_monic
    xSubQuadraticQuadraticSplits hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-two right endpoint reduction as a predicate-restricted
same-degree sign-normalized x-subtraction target, modulo the normalized monic
quadratic/quadratic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement) :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 2) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_two_of_monic
    hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-two right endpoint terminal as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 2) :=
  positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two_of_monic
    xSubQuadraticQuadraticSplits

/-- Pack the endpoint cases through degree two as a predicate-restricted
same-degree sign-normalized x-subtraction target, modulo the normalized monic
quadratic/quadratic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two_of_monic
    (hmono : xSubQuadraticQuadraticSplitsStatement) :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 2) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two_of_monic
    hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the endpoint cases through degree two as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 2) :=
  positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two_of_monic
    xSubQuadraticQuadraticSplits


end LiuOppositeSigns
end RealRooted
