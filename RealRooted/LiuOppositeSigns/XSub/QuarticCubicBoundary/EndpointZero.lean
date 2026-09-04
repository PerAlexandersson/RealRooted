import RealRooted.LiuOppositeSigns.XSub.QuarticCubicBoundary.RepeatedLeft
import RealRooted.LiuOppositeSigns.XSub.QuarticCubicBoundary.RepeatedRight

/-!
# Endpoint-zero quartic/cubic boundary

The left-only and combined endpoint-zero normalized quartic/cubic packages.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- At the left endpoint-zero boundary, the origin is a strict negative value
as soon as the right roots are strictly negative. -/
lemma eval_xSubQuarticCubic_at_left_endpoint_zero_neg
    {a b c u v w μ : ℝ} (hu0 : u < 0) (hv0 : v < 0)
    (hw0 : w < 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval 0 < 0 := by
  rw [eval_xSubQuarticCubic]
  have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
  have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
  have h0w_pos : 0 < 0 - w := sub_pos.mpr hw0
  have hhead_pos : 0 < (0 - u) * (0 - v) :=
    mul_pos h0u_pos h0v_pos
  have hG_pos : 0 < (0 - u) * (0 - v) * (0 - w) :=
    mul_pos hhead_pos h0w_pos
  nlinarith [mul_pos hμ hG_pos]

/-- Strict endpoint order `a < u < b < v < c < w < 0` for the normalized
quartic/cubic terminal with left endpoint zero. -/
lemma xSubQuarticCubicSplits_of_order_a_u_b_v_c_w_zero
    {a b c u v w μ : ℝ} (hau : a < u) (hub : u < b)
    (hbv : b < v) (hvc : v < c) (hcw : c < w) (hw0 : w < 0)
    (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c 0 u v w μ).Splits := by
  have hav : a < v := lt_trans hau (lt_trans hub hbv)
  have hac : a < c := lt_trans hav hvc
  have haw : a < w := lt_trans hac hcw
  have hbw : b < w := lt_trans hbv (lt_trans hvc hcw)
  have huv : u < v := lt_trans hub hbv
  have huc : u < c := lt_trans huv hvc
  have hvw : v < w := lt_trans hvc hcw
  have hu0 : u < 0 := lt_trans huc (lt_trans hcw hw0)
  have hv0 : v < 0 := lt_trans hvw hw0
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval a := by
    rw [eval_xSubQuarticCubic_at_a]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval u := by
    rw [eval_xSubQuarticCubic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hu_zero_neg : u - 0 < 0 := sub_neg.mpr hu0
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have h123_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) * (u - 0) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hu_zero_neg
    exact mul_pos_of_neg_of_neg hu0 hprod_neg
  have hP_b_neg :
      (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval b < 0 := by
    rw [eval_xSubQuarticCubic_at_b]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg hbu_pos hbv_neg
    have hG_pos : 0 < (b - u) * (b - v) * (b - w) :=
      mul_pos_of_neg_of_neg h12_neg hbw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_neg :
      (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval v < 0 := by
    rw [eval_xSubQuarticCubic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have hv_zero_neg : v - 0 < 0 := sub_neg.mpr hv0
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) * (v - 0) :=
      mul_pos_of_neg_of_neg h123_neg hv_zero_neg
    exact mul_neg_of_neg_of_pos hv0 hprod_pos
  have hP_c_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval c := by
    rw [eval_xSubQuarticCubic_at_c]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_neg : (c - u) * (c - v) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval w := by
    rw [eval_xSubQuarticCubic_at_w]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hw_zero_neg : w - 0 < 0 := sub_neg.mpr hw0
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have h123_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos h12_pos hwc_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) * (w - 0) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hw_zero_neg
    exact mul_pos_of_neg_of_neg hw0 hprod_neg
  have hP_zero_neg :
      (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval 0 < 0 :=
    eval_xSubQuarticCubic_at_left_endpoint_zero_neg hu0 hv0 hw0 hμ
  exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
    (le_of_lt huv) (le_of_lt hvw) (le_of_lt hw0) hμ (le_of_lt hau) hub hvc
    hw0 (le_of_lt hbv) (le_of_lt hcw) le_rfl (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_u_pos hP_b_neg)
    (mul_neg_of_neg_of_pos hP_v_neg hP_c_pos)
    (mul_neg_of_pos_of_neg hP_w_pos hP_zero_neg)

/-- Strict endpoint order `a < u < b < c < v < w < 0` for the normalized
quartic/cubic terminal with left endpoint zero. -/
lemma xSubQuarticCubicSplits_of_order_a_u_b_c_v_w_zero
    {a b c u v w μ : ℝ} (hau : a < u) (hub : u < b)
    (hbc : b < c) (hcv : c < v) (hvw : v < w) (hw0 : w < 0)
    (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c 0 u v w μ).Splits := by
  have hav : a < v := lt_trans hau (lt_trans hub (lt_trans hbc hcv))
  have hac : a < c := lt_trans hau (lt_trans hub hbc)
  have haw : a < w := lt_trans hav hvw
  have hbw : b < w := lt_trans hbc (lt_trans hcv hvw)
  have hcw : c < w := lt_trans hcv hvw
  have huv : u < v := lt_trans hub (lt_trans hbc hcv)
  have huc : u < c := lt_trans hub hbc
  have hu0 : u < 0 := lt_trans huc (lt_trans hcw hw0)
  have hv0 : v < 0 := lt_trans hvw hw0
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval a := by
    rw [eval_xSubQuarticCubic_at_a]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval u := by
    rw [eval_xSubQuarticCubic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hu_zero_neg : u - 0 < 0 := sub_neg.mpr hu0
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have h123_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) * (u - 0) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hu_zero_neg
    exact mul_pos_of_neg_of_neg hu0 hprod_neg
  have hP_b_neg :
      (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval b < 0 := by
    rw [eval_xSubQuarticCubic_at_b]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr (lt_trans hbc hcv)
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg hbu_pos hbv_neg
    have hG_pos : 0 < (b - u) * (b - v) * (b - w) :=
      mul_pos_of_neg_of_neg h12_neg hbw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_c_neg :
      (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval c < 0 := by
    rw [eval_xSubQuarticCubic_at_c]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_neg : c - v < 0 := sub_neg.mpr hcv
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have h12_neg : (c - u) * (c - v) < 0 :=
      mul_neg_of_pos_of_neg hcu_pos hcv_neg
    have hG_pos : 0 < (c - u) * (c - v) * (c - w) :=
      mul_pos_of_neg_of_neg h12_neg hcw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval v := by
    rw [eval_xSubQuarticCubic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr (lt_trans hbc hcv)
    have hvc_pos : 0 < v - c := sub_pos.mpr hcv
    have hv_zero_neg : v - 0 < 0 := sub_neg.mpr hv0
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos h12_pos hvc_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) * (v - 0) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hv_zero_neg
    exact mul_pos_of_neg_of_neg hv0 hprod_neg
  have hP_w_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval w := by
    rw [eval_xSubQuarticCubic_at_w]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hw_zero_neg : w - 0 < 0 := sub_neg.mpr hw0
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have h123_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos h12_pos hwc_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) * (w - 0) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hw_zero_neg
    exact mul_pos_of_neg_of_neg hw0 hprod_neg
  have hP_zero_neg :
      (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval 0 < 0 :=
    eval_xSubQuarticCubic_at_left_endpoint_zero_neg hu0 hv0 hw0 hμ
  exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
    (le_of_lt huv) (le_of_lt hvw) (le_of_lt hw0) hμ (le_of_lt hau) hub hcv
    hw0 (le_of_lt hbc) (le_of_lt hvw) le_rfl (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_u_pos hP_b_neg)
    (mul_neg_of_neg_of_pos hP_c_neg hP_v_pos)
    (mul_neg_of_pos_of_neg hP_w_pos hP_zero_neg)

/-- Strict endpoint order `a < b < u < v < c < w < 0` for the normalized
quartic/cubic terminal with left endpoint zero. -/
lemma xSubQuarticCubicSplits_of_order_a_b_u_v_c_w_zero
    {a b c u v w μ : ℝ} (hab : a < b) (hbu : b < u)
    (huv : u < v) (hvc : v < c) (hcw : c < w) (hw0 : w < 0)
    (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c 0 u v w μ).Splits := by
  have hau : a < u := lt_trans hab hbu
  have hav : a < v := lt_trans hau huv
  have hac : a < c := lt_trans hav hvc
  have haw : a < w := lt_trans hac hcw
  have hbv : b < v := lt_trans hbu huv
  have hbw : b < w := lt_trans hbv (lt_trans hvc hcw)
  have huc : u < c := lt_trans huv hvc
  have hvw : v < w := lt_trans hvc hcw
  have hu0 : u < 0 := lt_trans huc (lt_trans hcw hw0)
  have hv0 : v < 0 := lt_trans hvw hw0
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval a := by
    rw [eval_xSubQuarticCubic_at_a]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_b_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval b := by
    rw [eval_xSubQuarticCubic_at_b]
    have hbu_neg : b - u < 0 := sub_neg.mpr hbu
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_pos : 0 < (b - u) * (b - v) :=
      mul_pos_of_neg_of_neg hbu_neg hbv_neg
    have hG_neg : (b - u) * (b - v) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg :
      (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval u < 0 := by
    rw [eval_xSubQuarticCubic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_pos : 0 < u - b := sub_pos.mpr hbu
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hu_zero_neg : u - 0 < 0 := sub_neg.mpr hu0
    have h12_pos : 0 < (u - a) * (u - b) := mul_pos hua_pos hub_pos
    have h123_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) * (u - 0) :=
      mul_pos_of_neg_of_neg h123_neg hu_zero_neg
    exact mul_neg_of_neg_of_pos hu0 hprod_pos
  have hP_v_neg :
      (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval v < 0 := by
    rw [eval_xSubQuarticCubic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have hv_zero_neg : v - 0 < 0 := sub_neg.mpr hv0
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) * (v - 0) :=
      mul_pos_of_neg_of_neg h123_neg hv_zero_neg
    exact mul_neg_of_neg_of_pos hv0 hprod_pos
  have hP_c_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval c := by
    rw [eval_xSubQuarticCubic_at_c]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_neg : (c - u) * (c - v) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval w := by
    rw [eval_xSubQuarticCubic_at_w]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hw_zero_neg : w - 0 < 0 := sub_neg.mpr hw0
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have h123_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos h12_pos hwc_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) * (w - 0) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hw_zero_neg
    exact mul_pos_of_neg_of_neg hw0 hprod_neg
  have hP_zero_neg :
      (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval 0 < 0 :=
    eval_xSubQuarticCubic_at_left_endpoint_zero_neg hu0 hv0 hw0 hμ
  exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
    (le_of_lt huv) (le_of_lt hvw) (le_of_lt hw0) hμ (le_of_lt hab) hbu hvc
    hw0 (le_of_lt huv) (le_of_lt hcw) le_rfl (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_b_pos hP_u_neg)
    (mul_neg_of_neg_of_pos hP_v_neg hP_c_pos)
    (mul_neg_of_pos_of_neg hP_w_pos hP_zero_neg)

/-- Strict endpoint order `a < b < u < c < v < w < 0` for the normalized
quartic/cubic terminal with left endpoint zero. -/
lemma xSubQuarticCubicSplits_of_order_a_b_u_c_v_w_zero
    {a b c u v w μ : ℝ} (hab : a < b) (hbu : b < u)
    (huc : u < c) (hcv : c < v) (hvw : v < w) (hw0 : w < 0)
    (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c 0 u v w μ).Splits := by
  have hau : a < u := lt_trans hab hbu
  have hav : a < v := lt_trans hau (lt_trans huc hcv)
  have haw : a < w := lt_trans hav hvw
  have hbv : b < v := lt_trans hbu (lt_trans huc hcv)
  have hbw : b < w := lt_trans hbv hvw
  have huv : u < v := lt_trans huc hcv
  have hcw : c < w := lt_trans hcv hvw
  have hu0 : u < 0 := lt_trans huc (lt_trans hcw hw0)
  have hv0 : v < 0 := lt_trans hvw hw0
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval a := by
    rw [eval_xSubQuarticCubic_at_a]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_b_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval b := by
    rw [eval_xSubQuarticCubic_at_b]
    have hbu_neg : b - u < 0 := sub_neg.mpr hbu
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_pos : 0 < (b - u) * (b - v) :=
      mul_pos_of_neg_of_neg hbu_neg hbv_neg
    have hG_neg : (b - u) * (b - v) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg :
      (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval u < 0 := by
    rw [eval_xSubQuarticCubic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_pos : 0 < u - b := sub_pos.mpr hbu
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hu_zero_neg : u - 0 < 0 := sub_neg.mpr hu0
    have h12_pos : 0 < (u - a) * (u - b) := mul_pos hua_pos hub_pos
    have h123_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) * (u - 0) :=
      mul_pos_of_neg_of_neg h123_neg hu_zero_neg
    exact mul_neg_of_neg_of_pos hu0 hprod_pos
  have hP_c_neg :
      (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval c < 0 := by
    rw [eval_xSubQuarticCubic_at_c]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_neg : c - v < 0 := sub_neg.mpr hcv
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have h12_neg : (c - u) * (c - v) < 0 :=
      mul_neg_of_pos_of_neg hcu_pos hcv_neg
    have hG_pos : 0 < (c - u) * (c - v) * (c - w) :=
      mul_pos_of_neg_of_neg h12_neg hcw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval v := by
    rw [eval_xSubQuarticCubic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_pos : 0 < v - c := sub_pos.mpr hcv
    have hv_zero_neg : v - 0 < 0 := sub_neg.mpr hv0
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos h12_pos hvc_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) * (v - 0) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hv_zero_neg
    exact mul_pos_of_neg_of_neg hv0 hprod_neg
  have hP_w_pos :
      0 < (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval w := by
    rw [eval_xSubQuarticCubic_at_w]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hw_zero_neg : w - 0 < 0 := sub_neg.mpr hw0
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have h123_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos h12_pos hwc_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) * (w - 0) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hw_zero_neg
    exact mul_pos_of_neg_of_neg hw0 hprod_neg
  have hP_zero_neg :
      (xSubQuarticCubicPolynomial a b c 0 u v w μ).eval 0 < 0 :=
    eval_xSubQuarticCubic_at_left_endpoint_zero_neg hu0 hv0 hw0 hμ
  exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
    (le_of_lt huv) (le_of_lt hvw) (le_of_lt hw0) hμ (le_of_lt hab) hbu hcv
    hw0 (le_of_lt huc) (le_of_lt hvw) le_rfl (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_b_pos hP_u_neg)
    (mul_neg_of_neg_of_pos hP_c_neg hP_v_pos)
    (mul_neg_of_pos_of_neg hP_w_pos hP_zero_neg)

/-- The left-only endpoint-zero quartic/cubic boundary package. -/
theorem xSubQuarticCubicLeftOnlyEndpointZeroBoundaryCases :
    xSubQuarticCubicLeftOnlyEndpointZeroBoundaryCasesStatement := by
  intro a b c d u v w μ hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
    hd_eq hw_ne
  subst d
  by_cases hab_eq : a = b
  · exact xSubQuarticCubicRepeatedLeftBoundaryCases
      hab hbc hcd huv hvw hau hbv hcw huc hvd le_rfl hw0 hμ
      (Or.inl hab_eq)
  by_cases hbc_eq : b = c
  · exact xSubQuarticCubicRepeatedLeftBoundaryCases
      hab hbc hcd huv hvw hau hbv hcw huc hvd le_rfl hw0 hμ
      (Or.inr (Or.inl hbc_eq))
  by_cases hc_zero : c = 0
  · exact xSubQuarticCubicRepeatedLeftBoundaryCases
      hab hbc hcd huv hvw hau hbv hcw huc hvd le_rfl hw0 hμ
      (Or.inr (Or.inr hc_zero))
  have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
  have hbc_lt : b < c := lt_of_le_of_ne hbc hbc_eq
  have hc0_lt : c < 0 := lt_of_le_of_ne hcd hc_zero
  have hw0_lt : w < 0 := lt_of_le_of_ne hw0 hw_ne
  have hcommon_dispatch :
      (u = a ∨ u = b ∨ u = c ∨ v = b ∨ v = c ∨ v = 0 ∨
          w = c ∨ w = 0) →
        (xSubQuarticCubicPolynomial a b c 0 u v w μ).Splits := by
    intro hcommon
    exact xSubQuarticCubicSplits_of_common_root_cases
      (le_of_lt hab_lt) (le_of_lt hbc_lt) (le_of_lt hc0_lt) huv hvw
      hau hbv hcw huc hvd le_rfl hw0 hμ hcommon
  by_cases hua_eq : u = a
  · exact hcommon_dispatch (by simp [hua_eq])
  by_cases hub_eq : u = b
  · exact hcommon_dispatch (by simp [hub_eq])
  by_cases huc_eq : u = c
  · exact hcommon_dispatch (by simp [huc_eq])
  by_cases hvb_eq : v = b
  · exact hcommon_dispatch (by simp [hvb_eq])
  by_cases hvc_eq : v = c
  · exact hcommon_dispatch (by simp [hvc_eq])
  by_cases hv_zero : v = 0
  · exact hcommon_dispatch (by simp [hv_zero])
  by_cases hwc_eq : w = c
  · exact hcommon_dispatch (by simp [hwc_eq])
  by_cases huv_eq : u = v
  · exact xSubQuarticCubicStrictLeftRepeatedRightBoundaryCases
      hab_lt hbc_lt hc0_lt huv hvw hau hbv hcw huc hvd le_rfl hw0_lt hμ
      (Or.inl huv_eq)
  by_cases hvw_eq : v = w
  · exact xSubQuarticCubicStrictLeftRepeatedRightBoundaryCases
      hab_lt hbc_lt hc0_lt huv hvw hau hbv hcw huc hvd le_rfl hw0_lt hμ
      (Or.inr hvw_eq)
  have huv_lt : u < v := lt_of_le_of_ne huv huv_eq
  have hvw_lt : v < w := lt_of_le_of_ne hvw hvw_eq
  have hau_lt : a < u := lt_of_le_of_ne hau (by intro h; exact hua_eq h.symm)
  have hbv_lt : b < v := lt_of_le_of_ne hbv (by intro h; exact hvb_eq h.symm)
  have hcw_lt : c < w := lt_of_le_of_ne hcw (by intro h; exact hwc_eq h.symm)
  have huc_lt : u < c := lt_of_le_of_ne huc huc_eq
  by_cases hub_lt : u < b
  · by_cases hvc_lt : v < c
    · exact xSubQuarticCubicSplits_of_order_a_u_b_v_c_w_zero
        hau_lt hub_lt hbv_lt hvc_lt hcw_lt hw0_lt hμ
    · have hcv_lt : c < v :=
        lt_of_le_of_ne (le_of_not_gt hvc_lt) (by intro h; exact hvc_eq h.symm)
      exact xSubQuarticCubicSplits_of_order_a_u_b_c_v_w_zero
        hau_lt hub_lt hbc_lt hcv_lt hvw_lt hw0_lt hμ
  · have hbu_lt : b < u :=
      lt_of_le_of_ne (le_of_not_gt hub_lt) (by intro h; exact hub_eq h.symm)
    by_cases hvc_lt : v < c
    · exact xSubQuarticCubicSplits_of_order_a_b_u_v_c_w_zero
        hab_lt hbu_lt huv_lt hvc_lt hcw_lt hw0_lt hμ
    · have hcv_lt : c < v :=
        lt_of_le_of_ne (le_of_not_gt hvc_lt) (by intro h; exact hvc_eq h.symm)
      exact xSubQuarticCubicSplits_of_order_a_b_u_c_v_w_zero
        hab_lt hbu_lt huc_lt hcv_lt hvw_lt hw0_lt hμ

/-- The endpoint-zero quartic/cubic boundary follows from the two disjoint
single-endpoint packages; the double-zero corner is already factored to the
cubic/quadratic leaf. -/
theorem xSubQuarticCubicEndpointZeroBoundaryCases_of_single_endpoint_packages
    (hleft :
      xSubQuarticCubicLeftOnlyEndpointZeroBoundaryCasesStatement)
    (hright :
      xSubQuarticCubicRightOnlyEndpointZeroBoundaryCasesStatement) :
    xSubQuarticCubicEndpointZeroBoundaryCasesStatement := by
  intro a b c d u v w μ hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ h
  rcases h with hd_eq | hw_eq
  · by_cases hw_zero : w = 0
    · subst d
      subst w
      exact xSubQuarticCubicSplits_of_endpoint_roots_zero
        hab hbc huv hau hbv huc hcd hvd hμ
    · exact hleft hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
        hd_eq hw_zero
  · by_cases hd_zero : d = 0
    · subst d
      subst w
      exact xSubQuarticCubicSplits_of_endpoint_roots_zero
        hab hbc huv hau hbv huc hcd hvd hμ
    · exact hright hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
        hw_eq hd_zero

/-- The endpoint-zero quartic/cubic boundary follows from the left-only
endpoint-zero package and the quartic-minus-quadratic right endpoint factor. -/
theorem
    xSubQuarticCubicEndpointZeroBoundaryCases_of_left_endpoint_quarticSubQuadratic
    (hleft :
      xSubQuarticCubicLeftOnlyEndpointZeroBoundaryCasesStatement)
    (hquad : quarticSubQuadraticSplitsStatement) :
    xSubQuarticCubicEndpointZeroBoundaryCasesStatement :=
  xSubQuarticCubicEndpointZeroBoundaryCases_of_single_endpoint_packages hleft
    (xSubQuarticCubicRightOnlyEndpointZeroBoundaryCases_of_quarticSubQuadratic
      hquad)

/-- The endpoint-zero quartic/cubic boundary follows from the left-only
endpoint-zero package; the right-only endpoint-zero package is proved by the
quartic-minus-quadratic factor theorem. -/
theorem xSubQuarticCubicEndpointZeroBoundaryCases_of_left_endpoint_package
    (hleft :
      xSubQuarticCubicLeftOnlyEndpointZeroBoundaryCasesStatement) :
    xSubQuarticCubicEndpointZeroBoundaryCasesStatement :=
  xSubQuarticCubicEndpointZeroBoundaryCases_of_left_endpoint_quarticSubQuadratic
    hleft quarticSubQuadraticSplits


end LiuOppositeSigns
end RealRooted
