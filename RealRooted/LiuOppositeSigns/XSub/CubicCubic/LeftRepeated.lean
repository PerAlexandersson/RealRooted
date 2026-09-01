import RealRooted.LiuOppositeSigns.XSub.CubicCubic.RightRepeated

/-!
# Cubic/cubic x-subtraction repeated left-endpoint and terminal cases.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`u < a = b < v ≤ w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_a_v_w_c {a c u v w μ : ℝ}
    (hua : u < a) (hav : a < v) (hvw : v ≤ w) (hwc : w < c)
    (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C a) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C a) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have haw : a < w := lt_of_lt_of_le hav hvw
  have huc : u < c := lt_trans hua (lt_trans haw hwc)
  have hvc : v < c := lt_of_le_of_lt hvw hwc
  have ha0 : a < 0 := lt_of_lt_of_le (lt_trans haw hwc) hc0
  have hu0 : u < 0 := lt_trans hua ha0
  have hv0 : v < 0 := lt_of_lt_of_le hvc hc0
  have hw0 : w < 0 := lt_of_lt_of_le hwc hc0
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hsq_pos : 0 < (u - a) * (u - a) :=
      mul_pos_of_neg_of_neg hua_neg hua_neg
    have hprod_neg : (u - a) * (u - a) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos huc_neg
    have hleft_pos : 0 < u * ((u - a) * (u - a) * (u - c)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have htail_pos : 0 < (a - v) * (a - w) :=
      mul_pos_of_neg_of_neg hav_neg haw_neg
    have hG_pos : 0 < (a - u) * ((a - v) * (a - w)) :=
      mul_pos hau_pos htail_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have hsq_pos : 0 < (v - a) * (v - a) := mul_pos hva_pos hva_pos
    have hprod_neg : (v - a) * (v - a) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hvc_neg
    have hleft_pos : 0 < v * ((v - a) * (v - a) * (v - c)) :=
      mul_pos_of_neg_of_neg hv0 hprod_neg
    nlinarith
  have hP_w_pos : 0 < P.eval w := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwc_neg : w - c < 0 := sub_neg.mpr hwc
    have hsq_pos : 0 < (w - a) * (w - a) := mul_pos hwa_pos hwa_pos
    have hprod_neg : (w - a) * (w - a) * (w - c) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hwc_neg
    have hleft_pos : 0 < w * ((w - a) * (w - a) * (w - c)) :=
      mul_pos_of_neg_of_neg hw0 hprod_neg
    nlinarith
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_pos : 0 < c - w := sub_pos.mpr hwc
    have hhead_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_pos : 0 < (c - u) * (c - v) * (c - w) :=
      mul_pos hhead_pos hcw_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have hhead_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos hhead_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a a c u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a a c u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hua hav hwc (le_refl a) hvw hc0
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_a_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_w_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`u < a = b < v < c < w < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_a_v_c_w {a c u v w μ : ℝ}
    (hua : u < a) (hav : a < v) (hvc : v < c) (hcw : c < w)
    (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C a) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C a) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hac : a < c := lt_trans hav hvc
  have haw : a < w := lt_trans hac hcw
  have huc : u < c := lt_trans hua hac
  have hu0 : u < 0 := lt_trans hua (lt_trans haw hw0)
  have hv0 : v < 0 := lt_trans hvc (lt_trans hcw hw0)
  have hc0 : c < 0 := lt_trans hcw hw0
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hsq_pos : 0 < (u - a) * (u - a) :=
      mul_pos_of_neg_of_neg hua_neg hua_neg
    have hprod_neg : (u - a) * (u - a) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos huc_neg
    have hleft_pos : 0 < u * ((u - a) * (u - a) * (u - c)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have htail_pos : 0 < (a - v) * (a - w) :=
      mul_pos_of_neg_of_neg hav_neg haw_neg
    have hG_pos : 0 < (a - u) * ((a - v) * (a - w)) :=
      mul_pos hau_pos htail_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have hsq_pos : 0 < (v - a) * (v - a) := mul_pos hva_pos hva_pos
    have hprod_neg : (v - a) * (v - a) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hvc_neg
    have hleft_pos : 0 < v * ((v - a) * (v - a) * (v - c)) :=
      mul_pos_of_neg_of_neg hv0 hprod_neg
    nlinarith
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have hhead_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_neg : (c - u) * (c - v) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg : P.eval w < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hsq_pos : 0 < (w - a) * (w - a) := mul_pos hwa_pos hwa_pos
    have hprod_pos : 0 < (w - a) * (w - a) * (w - c) :=
      mul_pos hsq_pos hwc_pos
    have hleft_neg : w * ((w - a) * (w - a) * (w - c)) < 0 :=
      mul_neg_of_neg_of_pos hw0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have hhead_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos hhead_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a a c u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a a c u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hua hav hcw (le_refl a) (le_of_lt hvc) (le_of_lt hw0)
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_a_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_c_pos hP_w_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict-upper-endpoint package for the repeated lower left root `a = b`.
Common-root endpoint coincidences are factored out; the remaining two orders use
the adjacent-interval sign-change lemmas above. -/
lemma xSubCubicCubicSplits_of_lower_left_double_root {a c u v w μ : ℝ}
    (hac : a < c) (huv : u ≤ v) (hvw : v ≤ w)
    (hua : u ≤ a) (hvc : v ≤ c) (hav : a ≤ v) (haw : a ≤ w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C a) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases hua_eq : u = a
  · subst u
    exact xSubCubicCubicSplits_of_lower_common_root
      (le_of_lt hac) hvw hvc haw hc0 (le_of_lt hw0) hμ
  by_cases hva_eq : v = a
  · subst v
    exact xSubCubicCubicSplits_of_middle_common_root
      (le_refl a) (le_of_lt hac) hua haw hc0 (le_of_lt hw0) hμ
  by_cases hvc_eq : v = c
  · subst v
    have huw : u ≤ w := huv.trans hvw
    have ha0 : a ≤ 0 := (le_of_lt hac).trans hc0
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := c) (a := a) (b := a) (c := u) (d := w)
      (le_refl a) huw haw hua ha0 (le_of_lt hw0) hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hwc_eq : w = c
  · subst w
    exact xSubCubicCubicSplits_of_upper_common_root
      (le_refl a) (le_of_lt hac) huv hua hav hvc hc0 hμ
  have hua_lt : u < a := lt_of_le_of_ne hua hua_eq
  have hav_lt : a < v := lt_of_le_of_ne hav (by intro h; exact hva_eq h.symm)
  have hvc_lt : v < c := lt_of_le_of_ne hvc hvc_eq
  by_cases hwc : w < c
  · exact xSubCubicCubicSplits_of_order_u_a_a_v_w_c
      hua_lt hav_lt hvw hwc hc0 hμ
  · have hcw : c < w :=
      lt_of_le_of_ne (le_of_not_gt hwc) (by intro h; exact hwc_eq h.symm)
    exact xSubCubicCubicSplits_of_order_u_a_a_v_c_w
      hua_lt hav_lt hvc_lt hcw hw0 hμ

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`u < a < v < b = c < w < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_v_b_b_w {a b u v w μ : ℝ}
    (hua : u < a) (hav : a < v) (hvb : v < b) (hbw : b < w)
    (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C b)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C b)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hab : a < b := lt_trans hav hvb
  have haw : a < w := lt_trans hab hbw
  have hub : u < b := lt_trans hua hab
  have hu0 : u < 0 := lt_trans hua (lt_trans haw hw0)
  have hv0 : v < 0 := lt_trans hvb (lt_trans hbw hw0)
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have hsq_pos : 0 < (u - b) * (u - b) :=
      mul_pos_of_neg_of_neg hub_neg hub_neg
    have hprod_neg : (u - a) * ((u - b) * (u - b)) < 0 :=
      mul_neg_of_neg_of_pos hua_neg hsq_pos
    have hleft_pos : 0 < u * ((u - a) * ((u - b) * (u - b))) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have htail_pos : 0 < (a - v) * (a - w) :=
      mul_pos_of_neg_of_neg hav_neg haw_neg
    have hG_pos : 0 < (a - u) * ((a - v) * (a - w)) :=
      mul_pos hau_pos htail_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_neg : v - b < 0 := sub_neg.mpr hvb
    have hsq_pos : 0 < (v - b) * (v - b) :=
      mul_pos_of_neg_of_neg hvb_neg hvb_neg
    have hprod_pos : 0 < (v - a) * ((v - b) * (v - b)) :=
      mul_pos hva_pos hsq_pos
    have hleft_neg : v * ((v - a) * ((v - b) * (v - b))) < 0 :=
      mul_neg_of_neg_of_pos hv0 hprod_pos
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_pos : 0 < b - v := sub_pos.mpr hvb
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have hhead_pos : 0 < (b - u) * (b - v) := mul_pos hbu_pos hbv_pos
    have hG_neg : (b - u) * (b - v) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg : P.eval w < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hsq_pos : 0 < (w - b) * (w - b) := mul_pos hwb_pos hwb_pos
    have hprod_pos : 0 < (w - a) * ((w - b) * (w - b)) :=
      mul_pos hwa_pos hsq_pos
    have hleft_neg : w * ((w - a) * ((w - b) * (w - b))) < 0 :=
      mul_neg_of_neg_of_pos hw0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have hhead_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos hhead_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b b u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b b u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hua hvb hbw (le_of_lt hav) (le_refl b) (le_of_lt hw0)
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_v_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_b_pos hP_w_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`a < u ≤ v < b = c < w < 0`. -/
lemma xSubCubicCubicSplits_of_order_a_u_v_b_b_w {a b u v w μ : ℝ}
    (hau : a < u) (huv : u ≤ v) (hvb : v < b) (hbw : b < w)
    (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C b)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C b)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hav : a < v := lt_of_lt_of_le hau huv
  have hab : a < b := lt_trans hav hvb
  have haw : a < w := lt_trans hab hbw
  have hub : u < b := lt_of_le_of_lt huv hvb
  have hu0 : u < 0 := lt_trans hub (lt_trans hbw hw0)
  have hv0 : v < 0 := lt_trans hvb (lt_trans hbw hw0)
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have hhead_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have hsq_pos : 0 < (u - b) * (u - b) :=
      mul_pos_of_neg_of_neg hub_neg hub_neg
    have hprod_pos : 0 < (u - a) * ((u - b) * (u - b)) :=
      mul_pos hua_pos hsq_pos
    have hleft_neg : u * ((u - a) * ((u - b) * (u - b))) < 0 :=
      mul_neg_of_neg_of_pos hu0 hprod_pos
    nlinarith
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_neg : v - b < 0 := sub_neg.mpr hvb
    have hsq_pos : 0 < (v - b) * (v - b) :=
      mul_pos_of_neg_of_neg hvb_neg hvb_neg
    have hprod_pos : 0 < (v - a) * ((v - b) * (v - b)) :=
      mul_pos hva_pos hsq_pos
    have hleft_neg : v * ((v - a) * ((v - b) * (v - b))) < 0 :=
      mul_neg_of_neg_of_pos hv0 hprod_pos
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_pos : 0 < b - v := sub_pos.mpr hvb
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have hhead_pos : 0 < (b - u) * (b - v) := mul_pos hbu_pos hbv_pos
    have hG_neg : (b - u) * (b - v) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg hhead_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg : P.eval w < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hsq_pos : 0 < (w - b) * (w - b) := mul_pos hwb_pos hwb_pos
    have hprod_pos : 0 < (w - a) * ((w - b) * (w - b)) :=
      mul_pos hwa_pos hsq_pos
    have hleft_neg : w * ((w - a) * ((w - b) * (w - b))) < 0 :=
      mul_neg_of_neg_of_pos hw0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have hhead_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos hhead_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b b u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b b u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hau hvb hbw huv (le_refl b) (le_of_lt hw0)
      (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
      (mul_neg_of_neg_of_pos hP_v_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_b_pos hP_w_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict-upper-endpoint package for the repeated upper left root `b = c`.
Common-root endpoint coincidences are factored out; the remaining two orders use
the adjacent-interval sign-change lemmas above. -/
lemma xSubCubicCubicSplits_of_upper_left_double_root {a b u v w μ : ℝ}
    (hab : a < b) (huv : u ≤ v) (hvw : v ≤ w)
    (hub : u ≤ b) (hvb : v ≤ b) (hav : a ≤ v) (hbw : b ≤ w)
    (hb0 : b < 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C b)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases hua_eq : u = a
  · subst u
    exact xSubCubicCubicSplits_of_lower_common_root
      (le_refl b) hvw hvb hbw (le_of_lt hb0) (le_of_lt hw0) hμ
  by_cases hva_eq : v = a
  · subst v
    have huw : u ≤ w := huv.trans hvw
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := a) (a := b) (b := b) (c := u) (d := w)
      (le_refl b) huw hbw hub (le_of_lt hb0) (le_of_lt hw0) hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hvb_eq : v = b
  · subst v
    exact xSubCubicCubicSplits_of_middle_common_root
      (le_of_lt hab) (le_refl b) hub hbw (le_of_lt hb0) (le_of_lt hw0) hμ
  by_cases hwb_eq : w = b
  · subst w
    exact xSubCubicCubicSplits_of_upper_common_root
      (le_of_lt hab) (le_refl b) huv hub hav hvb (le_of_lt hb0) hμ
  have hav_lt : a < v := lt_of_le_of_ne hav (by intro h; exact hva_eq h.symm)
  have hvb_lt : v < b := lt_of_le_of_ne hvb hvb_eq
  have hbw_lt : b < w := lt_of_le_of_ne hbw (by intro h; exact hwb_eq h.symm)
  by_cases hua : u < a
  · exact xSubCubicCubicSplits_of_order_u_a_v_b_b_w
      hua hav_lt hvb_lt hbw_lt hw0 hμ
  · have hau : a < u :=
      lt_of_le_of_ne (le_of_not_gt hua) (by intro h; exact hua_eq h.symm)
    exact xSubCubicCubicSplits_of_order_a_u_v_b_b_w
      hau huv hvb_lt hbw_lt hw0 hμ

/-- Boundary case where both upper endpoint roots are zero.  Factoring out
`X` reduces the cubic/cubic leaf to the proved quadratic/quadratic leaf. -/
lemma xSubCubicCubicSplits_of_upper_roots_zero {a b u v μ : ℝ}
    (hab : a ≤ b) (huv : u ≤ v) (hav : a ≤ v) (hub : u ≤ b)
    (hb0 : b ≤ 0) (hv0 : v ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * X) -
      C μ * ((X - C u) * (X - C v) * X)).Splits := by
  let Q : ℝ[X] := X * ((X - C a) * (X - C b)) -
    C μ * ((X - C u) * (X - C v))
  have hQ : Q.Splits := by
    dsimp [Q]
    exact xSubQuadraticQuadraticSplits hab huv hav hub hb0 hv0 hμ
  have hfactor :
      X * ((X - C a) * (X - C b) * X) -
        C μ * ((X - C u) * (X - C v) * X) = X * Q := by
    dsimp [Q]
    ring
  rw [hfactor]
  exact Polynomial.Splits.X.mul hQ

/-- Boundary case where the upper right root is zero.  Factoring out `X`
reduces the cubic/cubic leaf to the cubic-minus-quadratic pencil above. -/
lemma xSubCubicCubicSplits_of_right_upper_root_zero {a b c u v μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v)
    (hub : u ≤ b) (hvc : v ≤ c) (hav : a ≤ v) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * X)).Splits := by
  let Q : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hQ : Q.Splits := by
    dsimp [Q]
    exact cubicSubQuadratic_splits_of_roots_le hab hbc huv hub hvc hav hμ
  have hfactor :
      X * ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v) * X) = X * Q := by
    dsimp [Q]
    ring
  rw [hfactor]
  exact Polynomial.Splits.X.mul hQ

/-- Normalized cubic/cubic leaf with weak left-root order, nonpositive upper
left endpoint, and strictly negative upper right endpoint.  This dispatcher
packages the strict-left-root case, the two left repeated-root boundaries, and
the triple-left-root common-root boundary. -/
lemma xSubCubicCubicSplits_of_negative_endpoints {a b c u v w μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v) (hvw : v ≤ w)
    (hub : u ≤ b) (hvc : v ≤ c) (hav : a ≤ v) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases hab_eq : a = b
  · subst b
    by_cases hac_eq : a = c
    · subst c
      have hvc_eq : v = a := le_antisymm hvc hav
      subst v
      exact xSubCubicCubicSplits_of_middle_common_root
        (le_refl a) (le_refl a) hub hbw hc0 (le_of_lt hw0) hμ
    · have hac_lt : a < c := lt_of_le_of_ne hbc hac_eq
      exact xSubCubicCubicSplits_of_lower_left_double_root
        hac_lt huv hvw hub hvc hav hbw hc0 hw0 hμ
  by_cases hbc_eq : b = c
  · subst c
    have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
    have hb0 : b < 0 := lt_of_le_of_lt hbw hw0
    exact xSubCubicCubicSplits_of_upper_left_double_root
      hab_lt huv hvw hub hvc hav hbw hb0 hw0 hμ
  have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
  have hbc_lt : b < c := lt_of_le_of_ne hbc hbc_eq
  exact xSubCubicCubicSplits_of_strict_left_roots
    hab_lt hbc_lt huv hvw hub hvc hav hbw hc0 hw0 hμ
end LiuOppositeSigns
end RealRooted
