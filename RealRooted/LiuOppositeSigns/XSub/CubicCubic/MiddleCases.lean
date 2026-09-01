import RealRooted.LiuOppositeSigns.XSub.CubicCubic.LeftOutlier

/-!
# Cubic/cubic x-subtraction middle and repeated-middle cases.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Strict nonordinary subcase of the normalized cubic/cubic leaf with order
`a < u < b < v < w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_a_u_b_v_w_c {a b c u v w μ : ℝ}
    (hau : a < u) (hub : u < b) (hbv : b < v) (hvw : v < w)
    (hwc : w < c) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hab : a < b := lt_trans hau hub
  have hac : a < c := lt_trans hab (lt_trans hbv (lt_trans hvw hwc))
  have huv : u < v := lt_trans hub hbv
  have huc : u < c := lt_trans hub (lt_trans hbv (lt_trans hvw hwc))
  have hbc : b < c := lt_trans hbv (lt_trans hvw hwc)
  have hvc : v < c := lt_trans hvw hwc
  have hb0 : b < 0 := lt_of_lt_of_le hbc hc0
  have hu0 : u < 0 := lt_trans hub hb0
  have hv0 : v < 0 := lt_of_lt_of_le hvc hc0
  have hw0 : w < 0 := lt_of_lt_of_le hwc hc0
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr (lt_trans hau huv)
    have haw_neg : a - w < 0 := sub_neg.mpr (lt_trans (lt_trans hau huv) hvw)
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hleft_neg : u * ((u - a) * (u - b) * (u - c)) < 0 :=
      mul_neg_of_neg_of_pos hu0 hprod_pos
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hbw_neg : b - w < 0 := sub_neg.mpr (lt_trans hbv hvw)
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
    have hwa_pos : 0 < w - a := sub_pos.mpr (lt_trans (lt_trans hab hbv) hvw)
    have hwb_pos : 0 < w - b := sub_pos.mpr (lt_trans hbv hvw)
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
      hP_ne hdeg_le hau hbv hwc hub hvw hc0
      (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
      (mul_neg_of_neg_of_pos hP_b_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_w_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict nonordinary subcase of the normalized cubic/cubic leaf with order
`a < u < v < b < c < w < 0`. -/
lemma xSubCubicCubicSplits_of_order_a_u_v_b_c_w {a b c u v w μ : ℝ}
    (hau : a < u) (huv : u < v) (hvb : v < b) (hbc : b < c)
    (hcw : c < w) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hab : a < b := lt_trans (lt_trans hau huv) hvb
  have hac : a < c := lt_trans hab hbc
  have haw : a < w := lt_trans hac hcw
  have hub : u < b := lt_trans huv hvb
  have huc : u < c := lt_trans hub hbc
  have hvw : v < w := lt_trans hvb (lt_trans hbc hcw)
  have hvc : v < c := lt_trans hvb hbc
  have hbw : b < w := lt_trans hbc hcw
  have hc0 : c < 0 := lt_trans hcw hw0
  have hb0 : b < 0 := lt_trans hbc hc0
  have hu0 : u < 0 := lt_trans hub hb0
  have hv0 : v < 0 := lt_trans hvb hb0
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr (lt_trans hau huv)
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hleft_neg : u * ((u - a) * (u - b) * (u - c)) < 0 :=
      mul_neg_of_neg_of_pos hu0 hprod_pos
    nlinarith
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr (lt_trans hau huv)
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
      hP_ne hdeg_le hau hvb hcw huv hbc (le_of_lt hw0)
      (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
      (mul_neg_of_neg_of_pos hP_v_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_c_pos hP_w_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict nonordinary subcase of the normalized cubic/cubic leaf with order
`a < u < v < b < w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_a_u_v_b_w_c {a b c u v w μ : ℝ}
    (hau : a < u) (huv : u < v) (hvb : v < b) (hbw : b < w)
    (hwc : w < c) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hab : a < b := lt_trans (lt_trans hau huv) hvb
  have hac : a < c := lt_trans hab (lt_trans hbw hwc)
  have haw : a < w := lt_trans hab hbw
  have hub : u < b := lt_trans huv hvb
  have huc : u < c := lt_trans hub (lt_trans hbw hwc)
  have hvc : v < c := lt_trans hvb (lt_trans hbw hwc)
  have hbc : b < c := lt_trans hbw hwc
  have hw0 : w < 0 := lt_of_lt_of_le hwc hc0
  have hb0 : b < 0 := lt_trans hbw hw0
  have hu0 : u < 0 := lt_trans hub hb0
  have hv0 : v < 0 := lt_trans hvb hb0
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr (lt_trans hau huv)
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hleft_neg : u * ((u - a) * (u - b) * (u - c)) < 0 :=
      mul_neg_of_neg_of_pos hu0 hprod_pos
    nlinarith
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr (lt_trans hau huv)
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
      hP_ne hdeg_le hau hvb hwc huv hbw hc0
      (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
      (mul_neg_of_neg_of_pos hP_v_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_w_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`a < u = v < b < w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_a_u_u_b_w_c {a b c u w μ : ℝ}
    (hau : a < u) (hub : u < b) (hbw : b < w) (hwc : w < c)
    (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C u) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C u) * (X - C w))
  have hab : a < b := lt_trans hau hub
  have haw : a < w := lt_trans hab hbw
  have huc : u < c := lt_trans hub (lt_trans hbw hwc)
  have hbc : b < c := lt_trans hbw hwc
  have hw0 : w < 0 := lt_of_lt_of_le hwc hc0
  have hb0 : b < 0 := lt_trans hbw hw0
  have hu0 : u < 0 := lt_trans hub hb0
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have hsq_pos : 0 < (a - u) * (a - u) :=
      mul_pos_of_neg_of_neg hau_neg hau_neg
    have hG_neg : (a - u) * (a - u) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hleft_neg : u * ((u - a) * (u - b) * (u - c)) < 0 :=
      mul_neg_of_neg_of_pos hu0 hprod_pos
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have hsq_pos : 0 < (b - u) * (b - u) := mul_pos hbu_pos hbu_pos
    have hG_neg : (b - u) * (b - u) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hbw_neg
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
    have hcw_pos : 0 < c - w := sub_pos.mpr hwc
    have hsq_pos : 0 < (c - u) * (c - u) := mul_pos hcu_pos hcu_pos
    have hG_pos : 0 < (c - u) * (c - u) * (c - w) :=
      mul_pos hsq_pos hcw_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have hsq_pos : 0 < (0 - u) * (0 - u) := mul_pos h0u_pos h0u_pos
    have hG_pos : 0 < (0 - u) * (0 - u) * (0 - w) :=
      mul_pos hsq_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u u w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u u w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hau hub hwc (le_refl u) (le_of_lt hbw) hc0
      (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
      (mul_neg_of_neg_of_pos hP_u_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_w_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`a < u = v < b < c < w < 0`. -/
lemma xSubCubicCubicSplits_of_order_a_u_u_b_c_w {a b c u w μ : ℝ}
    (hau : a < u) (hub : u < b) (hbc : b < c) (hcw : c < w)
    (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C u) * (X - C w))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C u) * (X - C w))
  have hab : a < b := lt_trans hau hub
  have hac : a < c := lt_trans hab hbc
  have haw : a < w := lt_trans hac hcw
  have huc : u < c := lt_trans hub hbc
  have hbw : b < w := lt_trans hbc hcw
  have hc0 : c < 0 := lt_trans hcw hw0
  have hb0 : b < 0 := lt_trans hbc hc0
  have hu0 : u < 0 := lt_trans hub hb0
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have hsq_pos : 0 < (a - u) * (a - u) :=
      mul_pos_of_neg_of_neg hau_neg hau_neg
    have hG_neg : (a - u) * (a - u) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hleft_neg : u * ((u - a) * (u - b) * (u - c)) < 0 :=
      mul_neg_of_neg_of_pos hu0 hprod_pos
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have hsq_pos : 0 < (b - u) * (b - u) := mul_pos hbu_pos hbu_pos
    have hG_neg : (b - u) * (b - u) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have hsq_pos : 0 < (c - u) * (c - u) := mul_pos hcu_pos hcu_pos
    have hG_neg : (c - u) * (c - u) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hcw_neg
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
    have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
    have hsq_pos : 0 < (0 - u) * (0 - u) := mul_pos h0u_pos h0u_pos
    have hG_pos : 0 < (0 - u) * (0 - u) * (0 - w) :=
      mul_pos hsq_pos h0w_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u u w μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u u w μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hau hub hcw (le_refl u) (le_of_lt hbc) (le_of_lt hw0)
      (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
      (mul_neg_of_neg_of_pos hP_u_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_c_pos hP_w_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict-left-root boundary package for the repeated lower right root
`u = v`.  The endpoint coincidences `w = b` and `w = c` reduce to common-root
quadratic/quadratic endpoints; the remaining two orders use adjacent
sign-change intervals. -/
lemma xSubCubicCubicSplits_of_lower_right_double_root {a b c u w μ : ℝ}
    (hab : a < b) (hbc : b < c) (hau : a < u) (hub : u < b)
    (hbw : b ≤ w) (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C u) * (X - C w))).Splits := by
  by_cases hwb : w = b
  · subst w
    have hac : a ≤ c := (le_of_lt hab).trans (le_of_lt hbc)
    have huc : u ≤ c := (le_of_lt hub).trans (le_of_lt hbc)
    have hu0 : u ≤ 0 :=
      (le_of_lt hub).trans ((le_of_lt hbc).trans hc0)
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := b) (a := a) (b := c) (c := u) (d := u)
      hac (le_refl u) (le_of_lt hau) huc hc0 hu0 hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hwc : w = c
  · subst w
    have huc : u ≤ c := (le_of_lt hub).trans (le_of_lt hbc)
    exact xSubCubicCubicSplits_of_upper_common_root
      (le_of_lt hab) (le_of_lt hbc) (le_refl u) (le_of_lt hub)
      (le_of_lt hau) huc hc0 hμ
  by_cases hwc_lt : w < c
  · have hbw_lt : b < w := lt_of_le_of_ne hbw (by intro h; exact hwb h.symm)
    exact xSubCubicCubicSplits_of_order_a_u_u_b_w_c
      hau hub hbw_lt hwc_lt hc0 hμ
  · have hcw : c < w :=
      lt_of_le_of_ne (le_of_not_gt hwc_lt) (by intro h; exact hwc h.symm)
    exact xSubCubicCubicSplits_of_order_a_u_u_b_c_w
      hau hub hbc hcw hw0 hμ
end LiuOppositeSigns
end RealRooted
