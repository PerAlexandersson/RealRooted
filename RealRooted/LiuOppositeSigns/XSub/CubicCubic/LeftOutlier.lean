import RealRooted.LiuOppositeSigns.XSub.CubicCubic.Basic

/-!
# Cubic/cubic x-subtraction cases with a left right-endpoint outlier.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns
/-- Strict nonordinary subcase of the normalized cubic/cubic leaf where the
left root of the right endpoint lies left of the left endpoint roots, and the
last right-endpoint root still lies before the upper left endpoint root:
`u < a < v < b < w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_v_b_w_c {a b c u v w μ : ℝ}
    (hua : u < a) (hav : a < v) (hvb : v < b) (hbw : b < w)
    (hwc : w < c) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hab : a < b := lt_trans hav hvb
  have hac : a < c := lt_trans hab (lt_trans hbw hwc)
  have haw : a < w := lt_trans hab hbw
  have hub : u < b := lt_trans hua hab
  have huc : u < c := lt_trans hua hac
  have hvc : v < c := lt_trans hvb (lt_trans hbw hwc)
  have hb0 : b < 0 := lt_of_lt_of_le (lt_trans hbw hwc) hc0
  have hw0 : w < 0 := lt_of_lt_of_le hwc hc0
  have ha0 : a < 0 := lt_trans hab hb0
  have hu0 : u < 0 := lt_trans hua ha0
  have hv0 : v < 0 := lt_trans hvb hb0
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_pos : 0 < (u - a) * (u - b) :=
      mul_pos_of_neg_of_neg hua_neg hub_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    have hleft_pos : 0 < u * ((u - a) * (u - b) * (u - c)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_neg : (a - u) * (a - v) < 0 :=
      mul_neg_of_pos_of_neg hau_pos hav_neg
    have hG_pos : 0 < (a - u) * (a - v) * (a - w) :=
      mul_pos_of_neg_of_neg h12_neg haw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_neg : v - b < 0 := sub_neg.mpr hvb
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_neg : (v - a) * (v - b) < 0 :=
      mul_neg_of_pos_of_neg hva_pos hvb_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos_of_neg_of_neg h12_neg hvc_neg
    have hleft_neg : v * ((v - a) * (v - b) * (v - c)) < 0 :=
      mul_neg_of_neg_of_pos hv0 hprod_pos
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_pos : 0 < b - v := sub_pos.mpr hvb
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_pos : 0 < (b - u) * (b - v) := mul_pos hbu_pos hbv_pos
    have hG_neg : (b - u) * (b - v) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_pos : 0 < P.eval w := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_neg : w - c < 0 := sub_neg.mpr hwc
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hwc_neg
    have hleft_pos : 0 < w * ((w - a) * (w - b) * (w - c)) :=
      mul_pos_of_neg_of_neg hw0 hprod_neg
    nlinarith
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_pos : 0 < c - w := sub_pos.mpr hwc
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_pos : 0 < (c - u) * (c - v) * (c - w) :=
      mul_pos h12_pos hcw_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have h12_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos h12_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hua hvb hwc hav hbw hc0
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_v_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_w_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict nonordinary subcase of the normalized cubic/cubic leaf with order
`u < a < v < b < c < w < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_v_b_c_w {a b c u v w μ : ℝ}
    (hua : u < a) (hav : a < v) (hvb : v < b) (hbc : b < c)
    (hcw : c < w) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hab : a < b := lt_trans hav hvb
  have hac : a < c := lt_trans hab hbc
  have haw : a < w := lt_trans hac hcw
  have hub : u < b := lt_trans hua hab
  have huc : u < c := lt_trans hua hac
  have hvc : v < c := lt_trans hvb hbc
  have hbw : b < w := lt_trans hbc hcw
  have hc0 : c < 0 := lt_trans hcw hw0
  have hb0 : b < 0 := lt_trans hbc hc0
  have ha0 : a < 0 := lt_trans hab hb0
  have hu0 : u < 0 := lt_trans hua ha0
  have hv0 : v < 0 := lt_trans hvb hb0
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_pos : 0 < (u - a) * (u - b) :=
      mul_pos_of_neg_of_neg hua_neg hub_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    have hleft_pos : 0 < u * ((u - a) * (u - b) * (u - c)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_neg : (a - u) * (a - v) < 0 :=
      mul_neg_of_pos_of_neg hau_pos hav_neg
    have hG_pos : 0 < (a - u) * (a - v) * (a - w) :=
      mul_pos_of_neg_of_neg h12_neg haw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_neg : v - b < 0 := sub_neg.mpr hvb
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_neg : (v - a) * (v - b) < 0 :=
      mul_neg_of_pos_of_neg hva_pos hvb_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos_of_neg_of_neg h12_neg hvc_neg
    have hleft_neg : v * ((v - a) * (v - b) * (v - c)) < 0 :=
      mul_neg_of_neg_of_pos hv0 hprod_pos
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_pos : 0 < b - v := sub_pos.mpr hvb
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_pos : 0 < (b - u) * (b - v) := mul_pos hbu_pos hbv_pos
    have hG_neg : (b - u) * (b - v) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_neg : (c - u) * (c - v) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg : P.eval w < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hprod_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos (mul_pos hwa_pos hwb_pos) hwc_pos
    have hleft_neg : w * ((w - a) * (w - b) * (w - c)) < 0 :=
      mul_neg_of_neg_of_pos hw0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have h12_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos h12_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hua hvb hcw hav hbc (le_of_lt hw0)
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_v_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_c_pos hP_w_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict nonordinary subcase of the normalized cubic/cubic leaf with order
`u < a < b < v < w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_b_v_w_c {a b c u v w μ : ℝ}
    (hua : u < a) (hab : a < b) (hbv : b < v) (hvw : v < w)
    (hwc : w < c) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hac : a < c := lt_trans hab (lt_trans hbv (lt_trans hvw hwc))
  have haw : a < w := lt_trans hab (lt_trans hbv hvw)
  have hub : u < b := lt_trans hua hab
  have huc : u < c := lt_trans hua hac
  have hvc : v < c := lt_trans hvw hwc
  have hbw : b < w := lt_trans hbv hvw
  have hw0 : w < 0 := lt_of_lt_of_le hwc hc0
  have hv0 : v < 0 := lt_trans hvw hw0
  have hb0 : b < 0 := lt_trans hbv hv0
  have ha0 : a < 0 := lt_trans hab hb0
  have hu0 : u < 0 := lt_trans hua ha0
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_pos : 0 < (u - a) * (u - b) :=
      mul_pos_of_neg_of_neg hua_neg hub_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    have hleft_pos : 0 < u * ((u - a) * (u - b) * (u - c)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr (lt_trans hab hbv)
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_neg : (a - u) * (a - v) < 0 :=
      mul_neg_of_pos_of_neg hau_pos hav_neg
    have hG_pos : 0 < (a - u) * (a - v) * (a - w) :=
      mul_pos_of_neg_of_neg h12_neg haw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg hbu_pos hbv_neg
    have hG_pos : 0 < (b - u) * (b - v) * (b - w) :=
      mul_pos_of_neg_of_neg h12_neg hbw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr (lt_trans hab hbv)
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    have hleft_pos : 0 < v * ((v - a) * (v - b) * (v - c)) :=
      mul_pos_of_neg_of_neg hv0 hprod_neg
    nlinarith
  have hP_w_pos : 0 < P.eval w := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_neg : w - c < 0 := sub_neg.mpr hwc
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hwc_neg
    have hleft_pos : 0 < w * ((w - a) * (w - b) * (w - c)) :=
      mul_pos_of_neg_of_neg hw0 hprod_neg
    nlinarith
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_pos : 0 < c - w := sub_pos.mpr hwc
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_pos : 0 < (c - u) * (c - v) * (c - w) :=
      mul_pos h12_pos hcw_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have h12_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos h12_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hua hbv hwc hab hvw hc0
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_b_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_w_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict nonordinary subcase of the normalized cubic/cubic leaf with order
`u < a < b < v < c < w < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_b_v_c_w {a b c u v w μ : ℝ}
    (hua : u < a) (hab : a < b) (hbv : b < v) (hvc : v < c)
    (hcw : c < w) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hac : a < c := lt_trans hab (lt_trans hbv hvc)
  have haw : a < w := lt_trans hac hcw
  have hub : u < b := lt_trans hua hab
  have huc : u < c := lt_trans hua hac
  have hbw : b < w := lt_trans (lt_trans hbv hvc) hcw
  have hc0 : c < 0 := lt_trans hcw hw0
  have hb0 : b < 0 := lt_trans (lt_trans hbv hvc) hc0
  have ha0 : a < 0 := lt_trans hab hb0
  have hu0 : u < 0 := lt_trans hua ha0
  have hv0 : v < 0 := lt_trans hvc hc0
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_pos : 0 < (u - a) * (u - b) :=
      mul_pos_of_neg_of_neg hua_neg hub_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    have hleft_pos : 0 < u * ((u - a) * (u - b) * (u - c)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr (lt_trans hab hbv)
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_neg : (a - u) * (a - v) < 0 :=
      mul_neg_of_pos_of_neg hau_pos hav_neg
    have hG_pos : 0 < (a - u) * (a - v) * (a - w) :=
      mul_pos_of_neg_of_neg h12_neg haw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg hbu_pos hbv_neg
    have hG_pos : 0 < (b - u) * (b - v) * (b - w) :=
      mul_pos_of_neg_of_neg h12_neg hbw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr (lt_trans hab hbv)
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    have hleft_pos : 0 < v * ((v - a) * (v - b) * (v - c)) :=
      mul_pos_of_neg_of_neg hv0 hprod_neg
    nlinarith
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_neg : (c - u) * (c - v) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg : P.eval w < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hprod_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos (mul_pos hwa_pos hwb_pos) hwc_pos
    have hleft_neg : w * ((w - a) * (w - b) * (w - c)) < 0 :=
      mul_neg_of_neg_of_pos hw0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have h12_pos : 0 < (0 - u) * (0 - v) := mul_pos h0u_pos h0v_pos
    have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
      mul_pos h12_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u v w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u v w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hua hbv hcw hab hvc (le_of_lt hw0)
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_b_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_c_pos hP_w_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Dispatcher for the strict left-outlier cubic/cubic subcases with no middle
boundary equalities.  The four branches correspond to the positions of `v`
relative to `b` and `w` relative to `c`. -/
lemma xSubCubicCubicSplits_of_left_root_left_strict_distinct {a b c u v w μ : ℝ}
    (hua : u < a) (hab : a < b) (hbc : b < c)
    (hav : a < v) (hvc : v < c) (hvw : v < w) (hbw : b < w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hvb_ne : v ≠ b) (hwc_ne : w ≠ c)
    (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  rcases lt_or_gt_of_ne hvb_ne with hvb | hbv
  · rcases lt_or_gt_of_ne hwc_ne with hwc | hcw
    · exact xSubCubicCubicSplits_of_order_u_a_v_b_w_c
        hua hav hvb hbw hwc hc0 hμ
    · exact xSubCubicCubicSplits_of_order_u_a_v_b_c_w
        hua hav hvb hbc hcw hw0 hμ
  · rcases lt_or_gt_of_ne hwc_ne with hwc | hcw
    · exact xSubCubicCubicSplits_of_order_u_a_b_v_w_c
        hua hab hbv hvw hwc hc0 hμ
    · exact xSubCubicCubicSplits_of_order_u_a_b_v_c_w
        hua hab hbv hvc hcw hw0 hμ

/-- Dispatcher for the strict left-outlier cubic/cubic subcases with weak
middle boundary inequalities.  Boundary equalities reduce to the common-root
quadratic/quadratic endpoint; the remaining case is the strict dispatcher. -/
lemma xSubCubicCubicSplits_of_left_root_left_strict_roots {a b c u v w μ : ℝ}
    (hua : u < a) (hab : a < b) (hbc : b < c)
    (hav : a ≤ v) (hvc : v ≤ c) (hvw : v < w) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases hva : v = a
  · subst v
    have huw : u ≤ w := by exact (le_of_lt hua).trans ((le_of_lt hab).trans hbw)
    have huc : u ≤ c := by exact (le_of_lt hua).trans ((le_of_lt hab).trans (le_of_lt hbc))
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := a) (a := b) (b := c) (c := u) (d := w)
      (le_of_lt hbc) huw hbw huc hc0 (le_of_lt hw0) hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hvb : v = b
  · subst v
    have hub : u ≤ b := (le_of_lt hua).trans (le_of_lt hab)
    exact xSubCubicCubicSplits_of_middle_common_root
      (le_of_lt hab) (le_of_lt hbc) hub hbw hc0 (le_of_lt hw0) hμ
  by_cases hvc_eq : v = c
  · subst v
    have huw : u ≤ w := by exact (le_of_lt hua).trans ((le_of_lt hab).trans hbw)
    have haw : a ≤ w := (le_of_lt hab).trans hbw
    have hub : u ≤ b := (le_of_lt hua).trans (le_of_lt hab)
    have hb0 : b ≤ 0 := (le_of_lt hbc).trans hc0
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := c) (a := a) (b := b) (c := u) (d := w)
      (le_of_lt hab) huw haw hub hb0 (le_of_lt hw0) hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hwb : w = b
  · subst w
    have hac : a ≤ c := (le_of_lt hab).trans (le_of_lt hbc)
    have huv : u ≤ v := (le_of_lt hua).trans hav
    have huc : u ≤ c := by exact (le_of_lt hua).trans ((le_of_lt hab).trans (le_of_lt hbc))
    have hv0 : v ≤ 0 := hvc.trans hc0
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := b) (a := a) (b := c) (c := u) (d := v)
      hac huv hav huc hc0 hv0 hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hwc : w = c
  · subst w
    have huv : u ≤ v := (le_of_lt hua).trans hav
    have hub : u ≤ b := (le_of_lt hua).trans (le_of_lt hab)
    exact xSubCubicCubicSplits_of_upper_common_root
      (le_of_lt hab) (le_of_lt hbc) huv hub hav hvc hc0 hμ
  have hav_lt : a < v := by exact lt_of_le_of_ne hav (by intro h; exact hva h.symm)
  have hvc_lt : v < c := by exact lt_of_le_of_ne hvc hvc_eq
  have hbw_lt : b < w := by exact lt_of_le_of_ne hbw (by intro h; exact hwb h.symm)
  exact xSubCubicCubicSplits_of_left_root_left_strict_distinct
    hua hab hbc hav_lt hvc_lt hvw hbw_lt hc0 hw0 hvb hwc hμ
end LiuOppositeSigns
end RealRooted
