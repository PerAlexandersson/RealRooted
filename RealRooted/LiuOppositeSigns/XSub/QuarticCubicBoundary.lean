import RealRooted.LiuOppositeSigns.XSub.QuarticCubicCommonRoot

/-!
# Liu quartic/cubic x-subtraction boundary package

This module contains the repeated-root, endpoint-zero, quartic/quadratic
boundary support, and final assembler for the normalized quartic/cubic
x-subtraction leaf.  Positive-split translated-family wrappers live downstream.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Strict-left-root boundary subcase with order
`a < b < u = v < c < w < d ≤ 0`. -/
lemma xSubQuarticCubicSplits_of_order_a_b_u_u_c_w_d
    {a b c d u w μ : ℝ} (hab : a < b) (hbu : b < u)
    (huc : u < c) (hcw : c < w) (hwd : w < d)
    (hd0 : d ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u u w μ).Splits := by
  have hau : a < u := lt_trans hab hbu
  have hac : a < c := lt_trans hau huc
  have haw : a < w := lt_trans hac hcw
  have hud : u < d := lt_trans huc (lt_trans hcw hwd)
  have hw0 : w < 0 := lt_of_lt_of_le hwd hd0
  have hu0 : u < 0 := lt_of_lt_of_le hud hd0
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u u w μ).eval a := by
    rw [eval_xSubQuarticCubic_at_a]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have hsq_pos : 0 < (a - u) * (a - u) :=
      mul_pos_of_neg_of_neg hau_neg hau_neg
    have hG_neg : (a - u) * (a - u) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_b_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u u w μ).eval b := by
    rw [eval_xSubQuarticCubic_at_b]
    have hbu_neg : b - u < 0 := sub_neg.mpr hbu
    have hbw_neg : b - w < 0 := sub_neg.mpr (lt_trans hbu (lt_trans huc hcw))
    have hsq_pos : 0 < (b - u) * (b - u) :=
      mul_pos_of_neg_of_neg hbu_neg hbu_neg
    have hG_neg : (b - u) * (b - u) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg :
      (xSubQuarticCubicPolynomial a b c d u u w μ).eval u < 0 := by
    rw [eval_xSubQuarticCubic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_pos : 0 < u - b := sub_pos.mpr hbu
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hud_neg : u - d < 0 := sub_neg.mpr hud
    have h12_pos : 0 < (u - a) * (u - b) := mul_pos hua_pos hub_pos
    have h123_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) * (u - d) :=
      mul_pos_of_neg_of_neg h123_neg hud_neg
    exact mul_neg_of_neg_of_pos hu0 hprod_pos
  have hP_c_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u u w μ).eval c := by
    rw [eval_xSubQuarticCubic_at_c]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have hsq_pos : 0 < (c - u) * (c - u) := mul_pos hcu_pos hcu_pos
    have hG_neg : (c - u) * (c - u) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u u w μ).eval w := by
    rw [eval_xSubQuarticCubic_at_w]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr (lt_trans hbu (lt_trans huc hcw))
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hwd_neg : w - d < 0 := sub_neg.mpr hwd
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have h123_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos h12_pos hwc_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) * (w - d) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hwd_neg
    exact mul_pos_of_neg_of_neg hw0 hprod_neg
  have hP_d_neg :
      (xSubQuarticCubicPolynomial a b c d u u w μ).eval d < 0 := by
    rw [eval_xSubQuarticCubic_at_d]
    have hdu_pos : 0 < d - u := sub_pos.mpr hud
    have hdw_pos : 0 < d - w := sub_pos.mpr hwd
    have hsq_pos : 0 < (d - u) * (d - u) := mul_pos hdu_pos hdu_pos
    have hG_pos : 0 < (d - u) * (d - u) * (d - w) :=
      mul_pos hsq_pos hdw_pos
    nlinarith [mul_pos hμ hG_pos]
  exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
    (le_refl u) (le_of_lt (lt_trans huc hcw)) (le_of_lt hw0) hμ
    (le_of_lt hab) hbu huc hwd (le_refl u) (le_of_lt hcw) hd0
    (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_b_pos hP_u_neg)
    (mul_neg_of_neg_of_pos hP_u_neg hP_c_pos)
    (mul_neg_of_pos_of_neg hP_w_pos hP_d_neg)

/-- Strict-left-root boundary subcase with order
`a < b < u = v < c < d < w < 0`. -/
lemma xSubQuarticCubicSplits_of_order_a_b_u_u_c_d_w
    {a b c d u w μ : ℝ} (hab : a < b) (hbu : b < u)
    (huc : u < c) (hcd : c < d) (hdw : d < w)
    (hw0 : w < 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u u w μ).Splits := by
  have hau : a < u := lt_trans hab hbu
  have hac : a < c := lt_trans hau huc
  have haw : a < w := lt_trans hac (lt_trans hcd hdw)
  have hud : u < d := lt_trans huc hcd
  have hu0 : u < 0 := lt_trans hud (lt_trans hdw hw0)
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u u w μ).eval a := by
    rw [eval_xSubQuarticCubic_at_a]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have hsq_pos : 0 < (a - u) * (a - u) :=
      mul_pos_of_neg_of_neg hau_neg hau_neg
    have hG_neg : (a - u) * (a - u) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_b_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u u w μ).eval b := by
    rw [eval_xSubQuarticCubic_at_b]
    have hbu_neg : b - u < 0 := sub_neg.mpr hbu
    have hbw_neg : b - w < 0 :=
      sub_neg.mpr (lt_trans hbu (lt_trans huc (lt_trans hcd hdw)))
    have hsq_pos : 0 < (b - u) * (b - u) :=
      mul_pos_of_neg_of_neg hbu_neg hbu_neg
    have hG_neg : (b - u) * (b - u) * (b - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hbw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg :
      (xSubQuarticCubicPolynomial a b c d u u w μ).eval u < 0 := by
    rw [eval_xSubQuarticCubic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_pos : 0 < u - b := sub_pos.mpr hbu
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hud_neg : u - d < 0 := sub_neg.mpr hud
    have h12_pos : 0 < (u - a) * (u - b) := mul_pos hua_pos hub_pos
    have h123_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) * (u - d) :=
      mul_pos_of_neg_of_neg h123_neg hud_neg
    exact mul_neg_of_neg_of_pos hu0 hprod_pos
  have hP_c_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u u w μ).eval c := by
    rw [eval_xSubQuarticCubic_at_c]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcw_neg : c - w < 0 := sub_neg.mpr (lt_trans hcd hdw)
    have hsq_pos : 0 < (c - u) * (c - u) := mul_pos hcu_pos hcu_pos
    have hG_neg : (c - u) * (c - u) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_d_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u u w μ).eval d := by
    rw [eval_xSubQuarticCubic_at_d]
    have hdu_pos : 0 < d - u := sub_pos.mpr hud
    have hdw_neg : d - w < 0 := sub_neg.mpr hdw
    have hsq_pos : 0 < (d - u) * (d - u) := mul_pos hdu_pos hdu_pos
    have hG_neg : (d - u) * (d - u) * (d - w) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos hdw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg :
      (xSubQuarticCubicPolynomial a b c d u u w μ).eval w < 0 := by
    rw [eval_xSubQuarticCubic_at_w]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b :=
      sub_pos.mpr (lt_trans hbu (lt_trans huc (lt_trans hcd hdw)))
    have hwc_pos : 0 < w - c := sub_pos.mpr (lt_trans hcd hdw)
    have hwd_pos : 0 < w - d := sub_pos.mpr hdw
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have h123_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos h12_pos hwc_pos
    have hprod_pos : 0 < (w - a) * (w - b) * (w - c) * (w - d) :=
      mul_pos h123_pos hwd_pos
    exact mul_neg_of_neg_of_pos hw0 hprod_pos
  exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
    (le_refl u) (le_of_lt (lt_trans huc (lt_trans hcd hdw))) (le_of_lt hw0)
    hμ (le_of_lt hab) hbu huc hdw (le_refl u) (le_of_lt hcd)
    (le_of_lt hw0) (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_b_pos hP_u_neg)
    (mul_neg_of_neg_of_pos hP_u_neg hP_c_pos)
    (mul_neg_of_pos_of_neg hP_d_pos hP_w_neg)

/-- Strict-left-root boundary subcase with order
`a < u < b < c < v = w < d ≤ 0`. -/
lemma xSubQuarticCubicSplits_of_order_a_u_b_c_v_v_d
    {a b c d u v μ : ℝ} (hau : a < u) (hub : u < b)
    (hbc : b < c) (hcv : c < v) (hvd : v < d)
    (hd0 : d ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u v v μ).Splits := by
  have hab : a < b := lt_trans hau hub
  have hac : a < c := lt_trans hab hbc
  have hav : a < v := lt_trans hac hcv
  have hud : u < d := lt_trans hub (lt_trans hbc (lt_trans hcv hvd))
  have hu0 : u < 0 := lt_of_lt_of_le hud hd0
  have hv0 : v < 0 := lt_of_lt_of_le hvd hd0
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v v μ).eval a := by
    rw [eval_xSubQuarticCubic_at_a]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have hsq_pos : 0 < (a - v) * (a - v) :=
      mul_pos_of_neg_of_neg hav_neg hav_neg
    have hG_neg : (a - u) * ((a - v) * (a - v)) < 0 :=
      mul_neg_of_neg_of_pos hau_neg hsq_pos
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v v μ).eval u := by
    rw [eval_xSubQuarticCubic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr (lt_trans hub hbc)
    have hud_neg : u - d < 0 := sub_neg.mpr hud
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have h123_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) * (u - d) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hud_neg
    exact mul_pos_of_neg_of_neg hu0 hprod_neg
  have hP_b_neg :
      (xSubQuarticCubicPolynomial a b c d u v v μ).eval b < 0 := by
    rw [eval_xSubQuarticCubic_at_b]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr (lt_trans hbc hcv)
    have hsq_pos : 0 < (b - v) * (b - v) :=
      mul_pos_of_neg_of_neg hbv_neg hbv_neg
    have hG_pos : 0 < (b - u) * ((b - v) * (b - v)) :=
      mul_pos hbu_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_c_neg :
      (xSubQuarticCubicPolynomial a b c d u v v μ).eval c < 0 := by
    rw [eval_xSubQuarticCubic_at_c]
    have hcu_pos : 0 < c - u := sub_pos.mpr (lt_trans hub hbc)
    have hcv_neg : c - v < 0 := sub_neg.mpr hcv
    have hsq_pos : 0 < (c - v) * (c - v) :=
      mul_pos_of_neg_of_neg hcv_neg hcv_neg
    have hG_pos : 0 < (c - u) * ((c - v) * (c - v)) :=
      mul_pos hcu_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v v μ).eval v := by
    rw [eval_xSubQuarticCubic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr (lt_trans hbc hcv)
    have hvc_pos : 0 < v - c := sub_pos.mpr hcv
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos h12_pos hvc_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) * (v - d) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hvd_neg
    exact mul_pos_of_neg_of_neg hv0 hprod_neg
  have hP_d_neg :
      (xSubQuarticCubicPolynomial a b c d u v v μ).eval d < 0 := by
    rw [eval_xSubQuarticCubic_at_d]
    have hdu_pos : 0 < d - u := sub_pos.mpr hud
    have hdv_pos : 0 < d - v := sub_pos.mpr hvd
    have hsq_pos : 0 < (d - v) * (d - v) := mul_pos hdv_pos hdv_pos
    have hG_pos : 0 < (d - u) * ((d - v) * (d - v)) :=
      mul_pos hdu_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
    (le_of_lt (lt_trans hub (lt_trans hbc hcv))) (le_refl v)
    (le_of_lt hv0) hμ (le_of_lt hau) hub hcv hvd
    (le_of_lt hbc) (le_refl v) hd0 (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_u_pos hP_b_neg)
    (mul_neg_of_neg_of_pos hP_c_neg hP_v_pos)
    (mul_neg_of_pos_of_neg hP_v_pos hP_d_neg)

/-- Strict-left-root boundary subcase with order
`a < b < u < c < v = w < d ≤ 0`. -/
lemma xSubQuarticCubicSplits_of_order_a_b_u_c_v_v_d
    {a b c d u v μ : ℝ} (hab : a < b) (hbu : b < u)
    (huc : u < c) (hcv : c < v) (hvd : v < d)
    (hd0 : d ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u v v μ).Splits := by
  have hau : a < u := lt_trans hab hbu
  have hbc : b < c := lt_trans hbu huc
  have hac : a < c := lt_trans hab hbc
  have hav : a < v := lt_trans hac hcv
  have hud : u < d := lt_trans huc (lt_trans hcv hvd)
  have hu0 : u < 0 := lt_of_lt_of_le hud hd0
  have hv0 : v < 0 := lt_of_lt_of_le hvd hd0
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v v μ).eval a := by
    rw [eval_xSubQuarticCubic_at_a]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have hsq_pos : 0 < (a - v) * (a - v) :=
      mul_pos_of_neg_of_neg hav_neg hav_neg
    have hG_neg : (a - u) * ((a - v) * (a - v)) < 0 :=
      mul_neg_of_neg_of_pos hau_neg hsq_pos
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_b_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v v μ).eval b := by
    rw [eval_xSubQuarticCubic_at_b]
    have hbu_neg : b - u < 0 := sub_neg.mpr hbu
    have hbv_neg : b - v < 0 := sub_neg.mpr (lt_trans hbu (lt_trans huc hcv))
    have hsq_pos : 0 < (b - v) * (b - v) :=
      mul_pos_of_neg_of_neg hbv_neg hbv_neg
    have hG_neg : (b - u) * ((b - v) * (b - v)) < 0 :=
      mul_neg_of_neg_of_pos hbu_neg hsq_pos
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg :
      (xSubQuarticCubicPolynomial a b c d u v v μ).eval u < 0 := by
    rw [eval_xSubQuarticCubic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_pos : 0 < u - b := sub_pos.mpr hbu
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hud_neg : u - d < 0 := sub_neg.mpr hud
    have h12_pos : 0 < (u - a) * (u - b) := mul_pos hua_pos hub_pos
    have h123_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) * (u - d) :=
      mul_pos_of_neg_of_neg h123_neg hud_neg
    exact mul_neg_of_neg_of_pos hu0 hprod_pos
  have hP_c_neg :
      (xSubQuarticCubicPolynomial a b c d u v v μ).eval c < 0 := by
    rw [eval_xSubQuarticCubic_at_c]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_neg : c - v < 0 := sub_neg.mpr hcv
    have hsq_pos : 0 < (c - v) * (c - v) :=
      mul_pos_of_neg_of_neg hcv_neg hcv_neg
    have hG_pos : 0 < (c - u) * ((c - v) * (c - v)) :=
      mul_pos hcu_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v v μ).eval v := by
    rw [eval_xSubQuarticCubic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr (lt_trans hbu (lt_trans huc hcv))
    have hvc_pos : 0 < v - c := sub_pos.mpr hcv
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos h12_pos hvc_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) * (v - d) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hvd_neg
    exact mul_pos_of_neg_of_neg hv0 hprod_neg
  have hP_d_neg :
      (xSubQuarticCubicPolynomial a b c d u v v μ).eval d < 0 := by
    rw [eval_xSubQuarticCubic_at_d]
    have hdu_pos : 0 < d - u := sub_pos.mpr hud
    have hdv_pos : 0 < d - v := sub_pos.mpr hvd
    have hsq_pos : 0 < (d - v) * (d - v) := mul_pos hdv_pos hdv_pos
    have hG_pos : 0 < (d - u) * ((d - v) * (d - v)) :=
      mul_pos hdu_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
    (le_of_lt (lt_trans huc hcv)) (le_refl v) (le_of_lt hv0) hμ
    (le_of_lt hab) hbu hcv hvd (le_of_lt huc) (le_refl v) hd0
    (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_b_pos hP_u_neg)
    (mul_neg_of_neg_of_pos hP_c_neg hP_v_pos)
    (mul_neg_of_pos_of_neg hP_v_pos hP_d_neg)

/-- Strict-left-root part of the quartic/cubic repeated-right boundary.  Shared
roots are delegated to the common-root dispatcher; the remaining `u = v` and
`v = w` cases are handled by the four adjacent sign-change leaves above. -/
lemma xSubQuarticCubicSplits_of_strict_left_repeated_right_boundary
    {a b c d u v w μ : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (huv : u ≤ v) (hvw : v ≤ w) (hau : a ≤ u) (hbv : b ≤ v)
    (hcw : c ≤ w) (huc : u ≤ c) (hvd : v ≤ d)
    (hd0 : d ≤ 0) (hw0 : w < 0) (hμ : 0 < μ)
    (hrep : u = v ∨ v = w) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  by_cases hua : u = a
  · exact xSubQuarticCubicSplits_of_common_root_cases
      (le_of_lt hab) (le_of_lt hbc) (le_of_lt hcd) huv hvw hau hbv hcw huc
      hvd hd0 (le_of_lt hw0) hμ (by simp [hua])
  by_cases hub : u = b
  · exact xSubQuarticCubicSplits_of_common_root_cases
      (le_of_lt hab) (le_of_lt hbc) (le_of_lt hcd) huv hvw hau hbv hcw huc
      hvd hd0 (le_of_lt hw0) hμ (by simp [hub])
  by_cases huc_eq : u = c
  · exact xSubQuarticCubicSplits_of_common_root_cases
      (le_of_lt hab) (le_of_lt hbc) (le_of_lt hcd) huv hvw hau hbv hcw huc
      hvd hd0 (le_of_lt hw0) hμ (by simp [huc_eq])
  by_cases hvb : v = b
  · exact xSubQuarticCubicSplits_of_common_root_cases
      (le_of_lt hab) (le_of_lt hbc) (le_of_lt hcd) huv hvw hau hbv hcw huc
      hvd hd0 (le_of_lt hw0) hμ (by simp [hvb])
  by_cases hvc : v = c
  · exact xSubQuarticCubicSplits_of_common_root_cases
      (le_of_lt hab) (le_of_lt hbc) (le_of_lt hcd) huv hvw hau hbv hcw huc
      hvd hd0 (le_of_lt hw0) hμ (by simp [hvc])
  by_cases hvd_eq : v = d
  · exact xSubQuarticCubicSplits_of_common_root_cases
      (le_of_lt hab) (le_of_lt hbc) (le_of_lt hcd) huv hvw hau hbv hcw huc
      hvd hd0 (le_of_lt hw0) hμ (by simp [hvd_eq])
  by_cases hwc : w = c
  · exact xSubQuarticCubicSplits_of_common_root_cases
      (le_of_lt hab) (le_of_lt hbc) (le_of_lt hcd) huv hvw hau hbv hcw huc
      hvd hd0 (le_of_lt hw0) hμ (by simp [hwc])
  by_cases hwd : w = d
  · exact xSubQuarticCubicSplits_of_common_root_cases
      (le_of_lt hab) (le_of_lt hbc) (le_of_lt hcd) huv hvw hau hbv hcw huc
      hvd hd0 (le_of_lt hw0) hμ (by simp [hwd])
  rcases hrep with huv_eq | hvw_eq
  · subst v
    have hbu : b < u := lt_of_le_of_ne hbv (by intro h; exact hub h.symm)
    have huc_lt : u < c := lt_of_le_of_ne huc huc_eq
    have hcw_lt : c < w :=
      lt_of_le_of_ne hcw (by intro h; exact hwc h.symm)
    rcases lt_or_gt_of_ne hwd with hwd_lt | hdw
    · exact xSubQuarticCubicSplits_of_order_a_b_u_u_c_w_d
        hab hbu huc_lt hcw_lt hwd_lt hd0 hμ
    · exact xSubQuarticCubicSplits_of_order_a_b_u_u_c_d_w
        hab hbu huc_lt hcd hdw hw0 hμ
  · subst w
    have hau_lt : a < u := lt_of_le_of_ne hau (by intro h; exact hua h.symm)
    have hcv : c < v := lt_of_le_of_ne hcw (by intro h; exact hvc h.symm)
    have hvd_lt : v < d := lt_of_le_of_ne hvd hvd_eq
    by_cases hub_lt : u < b
    · exact xSubQuarticCubicSplits_of_order_a_u_b_c_v_v_d
        hau_lt hub_lt hbc hcv hvd_lt hd0 hμ
    · have hbu : b < u :=
        lt_of_le_of_ne (le_of_not_gt hub_lt) (by intro h; exact hub h.symm)
      have huc_lt : u < c := lt_of_le_of_ne huc huc_eq
      exact xSubQuarticCubicSplits_of_order_a_b_u_c_v_v_d
        hab hbu huc_lt hcv hvd_lt hd0 hμ

/-- Strict-left-root and strictly negative right endpoint part of the remaining
quartic/cubic repeated-right boundary package. -/
def xSubQuarticCubicStrictLeftRepeatedRightBoundaryCasesStatement : Prop :=
  ∀ {a b c d u v w μ : ℝ},
    a < b → b < c → c < d → u ≤ v → v ≤ w →
      a ≤ u → b ≤ v → c ≤ w → u ≤ c → v ≤ d →
        d ≤ 0 → w < 0 → 0 < μ →
          (u = v ∨ v = w) →
            (xSubQuarticCubicPolynomial a b c d u v w μ).Splits

/-- The strict-left repeated-right quartic/cubic boundary package. -/
theorem xSubQuarticCubicStrictLeftRepeatedRightBoundaryCases :
    xSubQuarticCubicStrictLeftRepeatedRightBoundaryCasesStatement := by
  intro a b c d u v w μ hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ h
  exact xSubQuarticCubicSplits_of_strict_left_repeated_right_boundary
    hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ h

/-- Remaining boundary package for the normalized quartic/cubic terminal after
shared roots and the strict-side-root branch have been separated. -/
def xSubQuarticCubicSideBoundaryCasesStatement : Prop :=
  ∀ {a b c d u v w μ : ℝ},
    a ≤ b → b ≤ c → c ≤ d → u ≤ v → v ≤ w →
      a ≤ u → b ≤ v → c ≤ w → u ≤ c → v ≤ d →
        d ≤ 0 → w ≤ 0 → 0 < μ →
          (a = b ∨ b = c ∨ c = d ∨ u = v ∨ v = w ∨ d = 0 ∨ w = 0) →
            (xSubQuarticCubicPolynomial a b c d u v w μ).Splits

/-- Repeated-left-root part of the remaining normalized quartic/cubic
boundary package. -/
def xSubQuarticCubicRepeatedLeftBoundaryCasesStatement : Prop :=
  ∀ {a b c d u v w μ : ℝ},
    a ≤ b → b ≤ c → c ≤ d → u ≤ v → v ≤ w →
      a ≤ u → b ≤ v → c ≤ w → u ≤ c → v ≤ d →
        d ≤ 0 → w ≤ 0 → 0 < μ →
          (a = b ∨ b = c ∨ c = d) →
            (xSubQuarticCubicPolynomial a b c d u v w μ).Splits

/-- Repeated-right-root part of the remaining normalized quartic/cubic
boundary package. -/
def xSubQuarticCubicRepeatedRightBoundaryCasesStatement : Prop :=
  ∀ {a b c d u v w μ : ℝ},
    a ≤ b → b ≤ c → c ≤ d → u ≤ v → v ≤ w →
      a ≤ u → b ≤ v → c ≤ w → u ≤ c → v ≤ d →
        d ≤ 0 → w ≤ 0 → 0 < μ →
          (u = v ∨ v = w) →
            (xSubQuarticCubicPolynomial a b c d u v w μ).Splits

/-- Endpoint-zero part of the remaining normalized quartic/cubic boundary
package. -/
def xSubQuarticCubicEndpointZeroBoundaryCasesStatement : Prop :=
  ∀ {a b c d u v w μ : ℝ},
    a ≤ b → b ≤ c → c ≤ d → u ≤ v → v ≤ w →
      a ≤ u → b ≤ v → c ≤ w → u ≤ c → v ≤ d →
        d ≤ 0 → w ≤ 0 → 0 < μ →
          (d = 0 ∨ w = 0) →
            (xSubQuarticCubicPolynomial a b c d u v w μ).Splits

/-- Left-only endpoint-zero part of the normalized quartic/cubic boundary
package.  The right endpoint is assumed nonzero so that the double-zero corner
can be handled once, separately. -/
def xSubQuarticCubicLeftOnlyEndpointZeroBoundaryCasesStatement : Prop :=
  ∀ {a b c d u v w μ : ℝ},
    a ≤ b → b ≤ c → c ≤ d → u ≤ v → v ≤ w →
      a ≤ u → b ≤ v → c ≤ w → u ≤ c → v ≤ d →
        d ≤ 0 → w ≤ 0 → 0 < μ →
          d = 0 → w ≠ 0 →
            (xSubQuarticCubicPolynomial a b c d u v w μ).Splits

/-- Right-only endpoint-zero part of the normalized quartic/cubic boundary
package.  The left endpoint is assumed nonzero so that the double-zero corner
can be handled once, separately. -/
def xSubQuarticCubicRightOnlyEndpointZeroBoundaryCasesStatement : Prop :=
  ∀ {a b c d u v w μ : ℝ},
    a ≤ b → b ≤ c → c ≤ d → u ≤ v → v ≤ w →
      a ≤ u → b ≤ v → c ≤ w → u ≤ c → v ≤ d →
        d ≤ 0 → w ≤ 0 → 0 < μ →
          w = 0 → d ≠ 0 →
            (xSubQuarticCubicPolynomial a b c d u v w μ).Splits

/-- The normalized quartic-minus-quadratic endpoint factor. -/
noncomputable def quarticSubQuadraticPolynomial (a b c d u v μ : ℝ) : ℝ[X] :=
  ((X - C a) * (X - C b) * (X - C c) * (X - C d)) -
    C μ * ((X - C u) * (X - C v))

/-- Normalized monic arithmetic leaf for the quartic-minus-quadratic factor
that remains in the right-only endpoint-zero quartic/cubic boundary. -/
def quarticSubQuadraticSplitsStatement : Prop :=
  ∀ {a b c d u v μ : ℝ},
    a ≤ b → b ≤ c → c ≤ d → u ≤ v →
      a ≤ u → b ≤ v → u ≤ c → v ≤ d →
        d ≤ 0 → v ≤ 0 → 0 < μ →
          (quarticSubQuadraticPolynomial a b c d u v μ).Splits

/-- The normalized quartic-minus-quadratic factor is a genuine quartic. -/
lemma natDegree_quarticSubQuadratic (a b c d u v μ : ℝ) :
    (quarticSubQuadraticPolynomial a b c d u v μ).natDegree = 4 := by
  unfold quarticSubQuadraticPolynomial
  compute_degree <;> norm_num

/-- The normalized quartic-minus-quadratic factor is nonzero. -/
lemma quarticSubQuadratic_ne_zero (a b c d u v μ : ℝ) :
    quarticSubQuadraticPolynomial a b c d u v μ ≠ 0 := by
  intro hzero
  have hdeg := natDegree_quarticSubQuadratic a b c d u v μ
  rw [hzero] at hdeg
  norm_num at hdeg

/-- The normalized quartic-minus-quadratic factor has positive leading
coefficient. -/
lemma hasPosLeadingCoeff_quarticSubQuadratic (a b c d u v μ : ℝ) :
    HasPosLeadingCoeff (quarticSubQuadraticPolynomial a b c d u v μ) := by
  unfold quarticSubQuadraticPolynomial
  have hquartic_pos :
      HasPosLeadingCoeff ((X - C a) * (X - C b) * (X - C c) * (X - C d)) := by
    exact (((hasPosLeadingCoeff_X_sub_C a).mul
      (hasPosLeadingCoeff_X_sub_C b)).mul
      (hasPosLeadingCoeff_X_sub_C c)).mul
      (hasPosLeadingCoeff_X_sub_C d)
  have hquartic_deg :
      ((X - C a) * (X - C b) * (X - C c) * (X - C d)).natDegree = 4 := by
    compute_degree <;> norm_num
  have hdeg_lt : (C μ * ((X - C u) * (X - C v))).natDegree <
      ((X - C a) * (X - C b) * (X - C c) * (X - C d)).natDegree := by
    rw [hquartic_deg]
    compute_degree
    norm_num
  unfold HasPosLeadingCoeff at hquartic_pos ⊢
  have hdegree_lt : degree (C μ * ((X - C u) * (X - C v))) <
      degree ((X - C a) * (X - C b) * (X - C c) * (X - C d)) :=
    degree_lt_degree hdeg_lt
  rw [leadingCoeff_sub_of_degree_lt hdegree_lt]
  exact hquartic_pos

/-- Evaluation form of the normalized quartic-minus-quadratic factor. -/
lemma eval_quarticSubQuadratic (a b c d u v μ x : ℝ) :
    (quarticSubQuadraticPolynomial a b c d u v μ).eval x =
      (x - a) * (x - b) * (x - c) * (x - d) - μ * ((x - u) * (x - v)) := by
  unfold quarticSubQuadraticPolynomial
  simp only [eval_sub, eval_mul, eval_X, eval_C]

/-- Evaluation at the first left root of the quartic-minus-quadratic factor. -/
lemma eval_quarticSubQuadratic_at_a (a b c d u v μ : ℝ) :
    (quarticSubQuadraticPolynomial a b c d u v μ).eval a =
      -μ * ((a - u) * (a - v)) := by
  rw [eval_quarticSubQuadratic]
  ring

/-- Evaluation at the second left root of the quartic-minus-quadratic factor. -/
lemma eval_quarticSubQuadratic_at_b (a b c d u v μ : ℝ) :
    (quarticSubQuadraticPolynomial a b c d u v μ).eval b =
      -μ * ((b - u) * (b - v)) := by
  rw [eval_quarticSubQuadratic]
  ring

/-- Evaluation at the third left root of the quartic-minus-quadratic factor. -/
lemma eval_quarticSubQuadratic_at_c (a b c d u v μ : ℝ) :
    (quarticSubQuadraticPolynomial a b c d u v μ).eval c =
      -μ * ((c - u) * (c - v)) := by
  rw [eval_quarticSubQuadratic]
  ring

/-- Evaluation at the fourth left root of the quartic-minus-quadratic factor. -/
lemma eval_quarticSubQuadratic_at_d (a b c d u v μ : ℝ) :
    (quarticSubQuadraticPolynomial a b c d u v μ).eval d =
      -μ * ((d - u) * (d - v)) := by
  rw [eval_quarticSubQuadratic]
  ring

/-- Evaluation at the first right root of the quartic-minus-quadratic factor. -/
lemma eval_quarticSubQuadratic_at_u (a b c d u v μ : ℝ) :
    (quarticSubQuadraticPolynomial a b c d u v μ).eval u =
      (u - a) * (u - b) * (u - c) * (u - d) := by
  rw [eval_quarticSubQuadratic]
  ring

/-- Evaluation at the second right root of the quartic-minus-quadratic factor. -/
lemma eval_quarticSubQuadratic_at_v (a b c d u v μ : ℝ) :
    (quarticSubQuadraticPolynomial a b c d u v μ).eval v =
      (v - a) * (v - b) * (v - c) * (v - d) := by
  rw [eval_quarticSubQuadratic]
  ring

/-- The quartic-minus-quadratic factor tends to `+∞` at `-∞`. -/
lemma tendsto_eval_quarticSubQuadratic_atBot_atTop (a b c d u v μ : ℝ) :
    Tendsto
      (fun x => (quarticSubQuadraticPolynomial a b c d u v μ).eval x)
      atBot atTop := by
  let P : ℝ[X] := quarticSubQuadraticPolynomial a b c d u v μ
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_quarticSubQuadratic a b c d u v μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      dsimp [P]
      rw [natDegree_quarticSubQuadratic]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  have hP_even : Even P.natDegree := by
    dsimp [P]
    rw [natDegree_quarticSubQuadratic]
    norm_num
  exact tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hP_pos hP_deg_pos hP_even

/-- The quartic-minus-quadratic factor tends to `+∞` at `+∞`. -/
lemma tendsto_eval_quarticSubQuadratic_atTop_atTop (a b c d u v μ : ℝ) :
    Tendsto
      (fun x => (quarticSubQuadraticPolynomial a b c d u v μ).eval x)
      atTop atTop := by
  let P : ℝ[X] := quarticSubQuadraticPolynomial a b c d u v μ
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_quarticSubQuadratic a b c d u v μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      dsimp [P]
      rw [natDegree_quarticSubQuadratic]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  exact P.tendsto_atTop_of_leadingCoeff_nonneg hP_deg_pos hP_pos.le

/-- Strict order case `a < u < b < v < c < d` for the normalized
quartic-minus-quadratic factor. -/
lemma quarticSubQuadraticSplits_of_order_a_u_b_v_c_d
    {a b c d u v μ : ℝ} (hau : a < u) (hub : u < b)
    (hbv : b < v) (hvc : v < c) (hcd : c < d) (hμ : 0 < μ) :
    (quarticSubQuadraticPolynomial a b c d u v μ).Splits := by
  let P : ℝ[X] := quarticSubQuadraticPolynomial a b c d u v μ
  have hab : a < b := lt_trans hau hub
  have hac : a < c := lt_trans hab (lt_trans hbv hvc)
  have had : a < d := lt_trans hac hcd
  have huv : u < v := lt_trans hub hbv
  have huc : u < c := lt_trans hub (lt_trans hbv hvc)
  have hud : u < d := lt_trans huc hcd
  have hbuc : b < c := lt_trans hbv hvc
  have hbd : b < d := lt_trans hbuc hcd
  have hvd : v < d := lt_trans hvc hcd
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_a]
    have hG_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hau) (sub_neg.mpr (lt_trans hau huv))
    nlinarith [mul_pos hμ hG_pos]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hud_neg : u - d < 0 := sub_neg.mpr hud
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have h123_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    exact mul_neg_of_pos_of_neg h123_pos hud_neg
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_b]
    have hG_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hub) (sub_neg.mpr hbv)
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr (lt_trans hau huv)
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    exact mul_pos_of_neg_of_neg h123_neg hvd_neg
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_c]
    have hG_pos : 0 < (c - u) * (c - v) :=
      mul_pos (sub_pos.mpr huc) (sub_pos.mpr hvc)
    nlinarith [mul_pos hμ hG_pos]
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_d]
    have hG_pos : 0 < (d - u) * (d - v) :=
      mul_pos (sub_pos.mpr hud) (sub_pos.mpr hvd)
    nlinarith [mul_pos hμ hG_pos]
  have hsplits :=
    splits_of_two_sign_change_intervals_and_both_tails_of_le
      (quarticSubQuadratic_ne_zero a b c d u v μ)
      (by rw [natDegree_quarticSubQuadratic])
      (le_of_lt hau) hub hvc (le_of_lt hbv) (le_of_lt hcd)
      (le_of_lt hP_a_neg)
      (mul_neg_of_neg_of_pos hP_u_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_v_pos hP_c_neg)
      (le_of_lt hP_d_neg)
      (tendsto_eval_quarticSubQuadratic_atBot_atTop a b c d u v μ)
      (tendsto_eval_quarticSubQuadratic_atTop_atTop a b c d u v μ)
  simpa [P] using hsplits

/-- Strict order case `a < u < b < c < v < d` for the normalized
quartic-minus-quadratic factor. -/
lemma quarticSubQuadraticSplits_of_order_a_u_b_c_v_d
    {a b c d u v μ : ℝ} (hau : a < u) (hub : u < b)
    (hbc : b < c) (hcv : c < v) (hvd : v < d) (hμ : 0 < μ) :
    (quarticSubQuadraticPolynomial a b c d u v μ).Splits := by
  let P : ℝ[X] := quarticSubQuadraticPolynomial a b c d u v μ
  have hbv : b < v := lt_trans hbc hcv
  have huv : u < v := lt_trans hub hbv
  have hav : a < v := lt_trans hau huv
  have huc : u < c := lt_trans hub hbc
  have hud : u < d := lt_trans huv hvd
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_a]
    have hG_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hau) (sub_neg.mpr hav)
    nlinarith [mul_pos hμ hG_pos]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hud_neg : u - d < 0 := sub_neg.mpr hud
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have h123_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    exact mul_neg_of_pos_of_neg h123_pos hud_neg
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_b]
    have hG_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hub) (sub_neg.mpr hbv)
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_c]
    have hG_neg : (c - u) * (c - v) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr huc) (sub_neg.mpr hcv)
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_pos : 0 < v - c := sub_pos.mpr hcv
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd
    have h123_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos (mul_pos hva_pos hvb_pos) hvc_pos
    exact mul_neg_of_pos_of_neg h123_pos hvd_neg
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_d]
    have hG_pos : 0 < (d - u) * (d - v) :=
      mul_pos (sub_pos.mpr hud) (sub_pos.mpr hvd)
    nlinarith [mul_pos hμ hG_pos]
  have hsplits :=
    splits_of_two_sign_change_intervals_and_both_tails_of_le
      (quarticSubQuadratic_ne_zero a b c d u v μ)
      (by rw [natDegree_quarticSubQuadratic])
      (le_of_lt hau) hub hcv (le_of_lt hbc) (le_of_lt hvd)
      (le_of_lt hP_a_neg)
      (mul_neg_of_neg_of_pos hP_u_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_c_pos hP_v_neg)
      (le_of_lt hP_d_neg)
      (tendsto_eval_quarticSubQuadratic_atBot_atTop a b c d u v μ)
      (tendsto_eval_quarticSubQuadratic_atTop_atTop a b c d u v μ)
  simpa [P] using hsplits

/-- Strict order case `a < b < u ≤ v < c < d` for the normalized
quartic-minus-quadratic factor. -/
lemma quarticSubQuadraticSplits_of_order_a_b_u_v_c_d
    {a b c d u v μ : ℝ} (hab : a < b) (hbu : b < u)
    (huv : u ≤ v) (hvc : v < c) (hcd : c < d) (hμ : 0 < μ) :
    (quarticSubQuadraticPolynomial a b c d u v μ).Splits := by
  let P : ℝ[X] := quarticSubQuadraticPolynomial a b c d u v μ
  have hau : a < u := lt_trans hab hbu
  have hbv : b < v := lt_of_lt_of_le hbu huv
  have hav : a < v := lt_trans hab hbv
  have huc : u < c := lt_of_le_of_lt huv hvc
  have hud : u < d := lt_trans huc hcd
  have hvd : v < d := lt_trans hvc hcd
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_a]
    have hG_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hau) (sub_neg.mpr hav)
    nlinarith [mul_pos hμ hG_pos]
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_b]
    have hG_pos : 0 < (b - u) * (b - v) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hbu) (sub_neg.mpr hbv)
    nlinarith [mul_pos hμ hG_pos]
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_pos : 0 < u - b := sub_pos.mpr hbu
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hud_neg : u - d < 0 := sub_neg.mpr hud
    have h12_pos : 0 < (u - a) * (u - b) := mul_pos hua_pos hub_pos
    have h123_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    exact mul_pos_of_neg_of_neg h123_neg hud_neg
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    exact mul_pos_of_neg_of_neg h123_neg hvd_neg
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_c]
    have hG_pos : 0 < (c - u) * (c - v) :=
      mul_pos (sub_pos.mpr huc) (sub_pos.mpr hvc)
    nlinarith [mul_pos hμ hG_pos]
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_d]
    have hG_pos : 0 < (d - u) * (d - v) :=
      mul_pos (sub_pos.mpr hud) (sub_pos.mpr hvd)
    nlinarith [mul_pos hμ hG_pos]
  have hsplits :=
    splits_of_two_sign_change_intervals_and_both_tails_of_le
      (quarticSubQuadratic_ne_zero a b c d u v μ)
      (by rw [natDegree_quarticSubQuadratic])
      (le_of_lt hab) hbu hvc huv (le_of_lt hcd)
      (le_of_lt hP_a_neg)
      (mul_neg_of_neg_of_pos hP_b_neg hP_u_pos)
      (mul_neg_of_pos_of_neg hP_v_pos hP_c_neg)
      (le_of_lt hP_d_neg)
      (tendsto_eval_quarticSubQuadratic_atBot_atTop a b c d u v μ)
      (tendsto_eval_quarticSubQuadratic_atTop_atTop a b c d u v μ)
  simpa [P] using hsplits

/-- Strict order case `a < b < u < c < v < d` for the normalized
quartic-minus-quadratic factor. -/
lemma quarticSubQuadraticSplits_of_order_a_b_u_c_v_d
    {a b c d u v μ : ℝ} (hab : a < b) (hbu : b < u)
    (huc : u < c) (hcv : c < v) (hvd : v < d) (hμ : 0 < μ) :
    (quarticSubQuadraticPolynomial a b c d u v μ).Splits := by
  let P : ℝ[X] := quarticSubQuadraticPolynomial a b c d u v μ
  have hau : a < u := lt_trans hab hbu
  have hbv : b < v := lt_trans hbu (lt_trans huc hcv)
  have hav : a < v := lt_trans hab hbv
  have hud : u < d := lt_trans (lt_trans huc hcv) hvd
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_a]
    have hG_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hau) (sub_neg.mpr hav)
    nlinarith [mul_pos hμ hG_pos]
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_b]
    have hG_pos : 0 < (b - u) * (b - v) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hbu) (sub_neg.mpr hbv)
    nlinarith [mul_pos hμ hG_pos]
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_pos : 0 < u - b := sub_pos.mpr hbu
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hud_neg : u - d < 0 := sub_neg.mpr hud
    have h12_pos : 0 < (u - a) * (u - b) := mul_pos hua_pos hub_pos
    have h123_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    exact mul_pos_of_neg_of_neg h123_neg hud_neg
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_c]
    have hG_neg : (c - u) * (c - v) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr huc) (sub_neg.mpr hcv)
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_pos : 0 < v - c := sub_pos.mpr hcv
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd
    have h123_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos (mul_pos hva_pos hvb_pos) hvc_pos
    exact mul_neg_of_pos_of_neg h123_pos hvd_neg
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_quarticSubQuadratic_at_d]
    have hG_pos : 0 < (d - u) * (d - v) :=
      mul_pos (sub_pos.mpr hud) (sub_pos.mpr hvd)
    nlinarith [mul_pos hμ hG_pos]
  have hsplits :=
    splits_of_two_sign_change_intervals_and_both_tails_of_le
      (quarticSubQuadratic_ne_zero a b c d u v μ)
      (by rw [natDegree_quarticSubQuadratic])
      (le_of_lt hab) hbu hcv (le_of_lt huc) (le_of_lt hvd)
      (le_of_lt hP_a_neg)
      (mul_neg_of_neg_of_pos hP_b_neg hP_u_pos)
      (mul_neg_of_pos_of_neg hP_c_pos hP_v_neg)
      (le_of_lt hP_d_neg)
      (tendsto_eval_quarticSubQuadratic_atBot_atTop a b c d u v μ)
      (tendsto_eval_quarticSubQuadratic_atTop_atTop a b c d u v μ)
  simpa [P] using hsplits

/-- Strict quartic-minus-quadratic root data reduce to the four linear-order
leaves according to the positions of `u` relative to `b` and `v` relative to
`c`. -/
lemma quarticSubQuadraticSplits_of_strict_root_data
    {a b c d u v μ : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (huv : u ≤ v) (hau : a < u) (huc : u < c) (hbv : b < v)
    (hvd : v < d) (hub_ne : u ≠ b) (hvc_ne : v ≠ c) (hμ : 0 < μ) :
    (quarticSubQuadraticPolynomial a b c d u v μ).Splits := by
  by_cases hub : u < b
  · by_cases hvc : v < c
    · exact quarticSubQuadraticSplits_of_order_a_u_b_v_c_d
        hau hub hbv hvc hcd hμ
    · have hcv : c < v := lt_of_le_of_ne (le_of_not_gt hvc) hvc_ne.symm
      exact quarticSubQuadraticSplits_of_order_a_u_b_c_v_d
        hau hub hbc hcv hvd hμ
  · have hbu : b < u := lt_of_le_of_ne (le_of_not_gt hub) hub_ne.symm
    by_cases hvc : v < c
    · exact quarticSubQuadraticSplits_of_order_a_b_u_v_c_d
        hab hbu huv hvc hcd hμ
    · have hcv : c < v := lt_of_le_of_ne (le_of_not_gt hvc) hvc_ne.symm
      exact quarticSubQuadraticSplits_of_order_a_b_u_c_v_d
        hab hbu huc hcv hvd hμ

/-- Closed right-root data over strictly ordered quartic roots.  Common-root
boundaries factor through the cubic-minus-linear closed-interval leaf; the
remaining case is the strict linear-order dispatcher. -/
lemma quarticSubQuadraticSplits_of_strict_left_roots
    {a b c d u v μ : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (huv : u ≤ v) (hau : a ≤ u) (hbv : b ≤ v) (huc : u ≤ c)
    (hvd : v ≤ d) (hμ : 0 < μ) :
    (quarticSubQuadraticPolynomial a b c d u v μ).Splits := by
  by_cases hua_eq : u = a
  · subst u
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := a) (a := b) (b := c) (c := d) (u := v)
      (le_of_lt hbc) (le_of_lt hcd) hbv hvd hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases hub_eq : u = b
  · subst u
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := b) (a := a) (b := c) (c := d) (u := v)
      (le_of_lt (lt_trans hab hbc)) (le_of_lt hcd)
      ((le_of_lt hab).trans hbv) hvd hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases huc_eq : u = c
  · subst u
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := c) (a := a) (b := b) (c := d) (u := v)
      (le_of_lt hab) ((le_of_lt hbc).trans (le_of_lt hcd))
      ((le_of_lt hab).trans hbv) hvd hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases hvb_eq : v = b
  · subst v
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := b) (a := a) (b := c) (c := d) (u := u)
      (le_of_lt (lt_trans hab hbc)) (le_of_lt hcd)
      hau (huc.trans (le_of_lt hcd)) hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases hvc_eq : v = c
  · subst v
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := c) (a := a) (b := b) (c := d) (u := u)
      (le_of_lt hab) ((le_of_lt hbc).trans (le_of_lt hcd))
      hau (huc.trans (le_of_lt hcd)) hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases hvd_eq : v = d
  · subst v
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := d) (a := a) (b := b) (c := c) (u := u)
      (le_of_lt hab) (le_of_lt hbc) hau huc hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  have hau_lt : a < u := lt_of_le_of_ne hau (by intro h; exact hua_eq h.symm)
  have huc_lt : u < c := lt_of_le_of_ne huc huc_eq
  have hbv_lt : b < v := lt_of_le_of_ne hbv (by intro h; exact hvb_eq h.symm)
  have hvd_lt : v < d := lt_of_le_of_ne hvd hvd_eq
  exact quarticSubQuadraticSplits_of_strict_root_data
    hab hbc hcd huv hau_lt huc_lt hbv_lt hvd_lt hub_eq hvc_eq hμ

/-- Lower repeated-left-root boundary `a = b` for the normalized
quartic-minus-quadratic factor. -/
lemma quarticSubQuadraticSplits_of_lower_left_repeated
    {a c d u v μ : ℝ} (hac : a < c) (hcd : c < d)
    (huv : u ≤ v) (hau : a ≤ u) (huc : u ≤ c) (hvd : v ≤ d)
    (hμ : 0 < μ) :
    (quarticSubQuadraticPolynomial a a c d u v μ).Splits := by
  by_cases hua_eq : u = a
  · subst u
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := a) (a := a) (b := c) (c := d) (u := v)
      (le_of_lt hac) (le_of_lt hcd) (hau.trans huv) hvd hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases huc_eq : u = c
  · subst u
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := c) (a := a) (b := a) (c := d) (u := v)
      le_rfl ((le_of_lt hac).trans (le_of_lt hcd))
      (hau.trans huv) hvd hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases hvc_eq : v = c
  · subst v
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := c) (a := a) (b := a) (c := d) (u := u)
      le_rfl ((le_of_lt hac).trans (le_of_lt hcd))
      hau (huc.trans (le_of_lt hcd)) hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases hvd_eq : v = d
  · subst v
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := d) (a := a) (b := a) (c := c) (u := u)
      le_rfl (le_of_lt hac) hau huc hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  have hau_lt : a < u := lt_of_le_of_ne hau (by intro h; exact hua_eq h.symm)
  have huc_lt : u < c := lt_of_le_of_ne huc huc_eq
  have hav_lt : a < v := lt_of_lt_of_le hau_lt huv
  have hvd_lt : v < d := lt_of_le_of_ne hvd hvd_eq
  have hud_lt : u < d := lt_trans huc_lt hcd
  have hP_a_neg :
      (quarticSubQuadraticPolynomial a a c d u v μ).eval a < 0 := by
    rw [eval_quarticSubQuadratic_at_a]
    have hG_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hau_lt) (sub_neg.mpr hav_lt)
    nlinarith [mul_pos hμ hG_pos]
  have hP_u_pos :
      0 < (quarticSubQuadraticPolynomial a a c d u v μ).eval u := by
    rw [eval_quarticSubQuadratic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau_lt
    have huc_neg : u - c < 0 := sub_neg.mpr huc_lt
    have hud_neg : u - d < 0 := sub_neg.mpr hud_lt
    have hsq_pos : 0 < (u - a) * (u - a) := mul_pos hua_pos hua_pos
    have h123_neg : (u - a) * (u - a) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos huc_neg
    exact mul_pos_of_neg_of_neg h123_neg hud_neg
  have hP_d_neg :
      (quarticSubQuadraticPolynomial a a c d u v μ).eval d < 0 := by
    rw [eval_quarticSubQuadratic_at_d]
    have hG_pos : 0 < (d - u) * (d - v) :=
      mul_pos (sub_pos.mpr hud_lt) (sub_pos.mpr hvd_lt)
    nlinarith [mul_pos hμ hG_pos]
  by_cases hvc : v < c
  · have hP_v_pos :
        0 < (quarticSubQuadraticPolynomial a a c d u v μ).eval v := by
      rw [eval_quarticSubQuadratic_at_v]
      have hva_pos : 0 < v - a := sub_pos.mpr hav_lt
      have hvc_neg : v - c < 0 := sub_neg.mpr hvc
      have hvd_neg : v - d < 0 := sub_neg.mpr hvd_lt
      have hsq_pos : 0 < (v - a) * (v - a) := mul_pos hva_pos hva_pos
      have h123_neg : (v - a) * (v - a) * (v - c) < 0 :=
        mul_neg_of_pos_of_neg hsq_pos hvc_neg
      exact mul_pos_of_neg_of_neg h123_neg hvd_neg
    have hP_c_neg :
        (quarticSubQuadraticPolynomial a a c d u v μ).eval c < 0 := by
      rw [eval_quarticSubQuadratic_at_c]
      have hG_pos : 0 < (c - u) * (c - v) :=
        mul_pos (sub_pos.mpr huc_lt) (sub_pos.mpr hvc)
      nlinarith [mul_pos hμ hG_pos]
    exact splits_of_two_sign_change_intervals_and_both_tails_of_le
      (quarticSubQuadratic_ne_zero a a c d u v μ)
      (by rw [natDegree_quarticSubQuadratic])
      le_rfl hau_lt hvc huv (le_of_lt hcd)
      (le_of_lt hP_a_neg)
      (mul_neg_of_neg_of_pos hP_a_neg hP_u_pos)
      (mul_neg_of_pos_of_neg hP_v_pos hP_c_neg)
      (le_of_lt hP_d_neg)
      (tendsto_eval_quarticSubQuadratic_atBot_atTop a a c d u v μ)
      (tendsto_eval_quarticSubQuadratic_atTop_atTop a a c d u v μ)
  · have hcv : c < v :=
      lt_of_le_of_ne (le_of_not_gt hvc) (by intro h; exact hvc_eq h.symm)
    have hP_c_pos :
        0 < (quarticSubQuadraticPolynomial a a c d u v μ).eval c := by
      rw [eval_quarticSubQuadratic_at_c]
      have hG_neg : (c - u) * (c - v) < 0 :=
        mul_neg_of_pos_of_neg (sub_pos.mpr huc_lt) (sub_neg.mpr hcv)
      nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
    have hP_v_neg :
        (quarticSubQuadraticPolynomial a a c d u v μ).eval v < 0 := by
      rw [eval_quarticSubQuadratic_at_v]
      have hva_pos : 0 < v - a := sub_pos.mpr hav_lt
      have hvc_pos : 0 < v - c := sub_pos.mpr hcv
      have hvd_neg : v - d < 0 := sub_neg.mpr hvd_lt
      have hsq_pos : 0 < (v - a) * (v - a) := mul_pos hva_pos hva_pos
      have h123_pos : 0 < (v - a) * (v - a) * (v - c) :=
        mul_pos hsq_pos hvc_pos
      exact mul_neg_of_pos_of_neg h123_pos hvd_neg
    exact splits_of_two_sign_change_intervals_and_both_tails_of_le
      (quarticSubQuadratic_ne_zero a a c d u v μ)
      (by rw [natDegree_quarticSubQuadratic])
      le_rfl hau_lt hcv huc (le_of_lt hvd_lt)
      (le_of_lt hP_a_neg)
      (mul_neg_of_neg_of_pos hP_a_neg hP_u_pos)
      (mul_neg_of_pos_of_neg hP_c_pos hP_v_neg)
      (le_of_lt hP_d_neg)
      (tendsto_eval_quarticSubQuadratic_atBot_atTop a a c d u v μ)
      (tendsto_eval_quarticSubQuadratic_atTop_atTop a a c d u v μ)

/-- Middle repeated-left-root boundary `b = c` for the normalized
quartic-minus-quadratic factor. -/
lemma quarticSubQuadraticSplits_of_middle_left_repeated
    {a b d u v μ : ℝ} (hab : a < b) (hbd : b < d)
    (huv : u ≤ v) (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvd : v ≤ d) (hμ : 0 < μ) :
    (quarticSubQuadraticPolynomial a b b d u v μ).Splits := by
  by_cases hua_eq : u = a
  · subst u
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := a) (a := b) (b := b) (c := d) (u := v)
      le_rfl (le_of_lt hbd) hbv hvd hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases hub_eq : u = b
  · subst u
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := b) (a := a) (b := b) (c := d) (u := v)
      (le_of_lt hab) (le_of_lt hbd) ((le_of_lt hab).trans hbv) hvd hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases hvb_eq : v = b
  · subst v
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := b) (a := a) (b := b) (c := d) (u := u)
      (le_of_lt hab) (le_of_lt hbd) hau (hub.trans (le_of_lt hbd)) hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases hvd_eq : v = d
  · subst v
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := d) (a := a) (b := b) (c := b) (u := u)
      (le_of_lt hab) le_rfl hau hub hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  have hau_lt : a < u := lt_of_le_of_ne hau (by intro h; exact hua_eq h.symm)
  have hub_lt : u < b := lt_of_le_of_ne hub hub_eq
  have hbv_lt : b < v := lt_of_le_of_ne hbv (by intro h; exact hvb_eq h.symm)
  have hvd_lt : v < d := lt_of_le_of_ne hvd hvd_eq
  have hav_lt : a < v := lt_trans hab hbv_lt
  have hud_lt : u < d := lt_trans hub_lt hbd
  have hP_a_neg :
      (quarticSubQuadraticPolynomial a b b d u v μ).eval a < 0 := by
    rw [eval_quarticSubQuadratic_at_a]
    have hG_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hau_lt) (sub_neg.mpr hav_lt)
    nlinarith [mul_pos hμ hG_pos]
  have hP_u_neg :
      (quarticSubQuadraticPolynomial a b b d u v μ).eval u < 0 := by
    rw [eval_quarticSubQuadratic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau_lt
    have hub_neg : u - b < 0 := sub_neg.mpr hub_lt
    have hud_neg : u - d < 0 := sub_neg.mpr hud_lt
    have hsq_pos : 0 < (u - b) * (u - b) := mul_pos_of_neg_of_neg hub_neg hub_neg
    have htail_neg : (u - a) * ((u - b) * (u - b)) * (u - d) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hua_pos hsq_pos) hud_neg
    nlinarith [htail_neg]
  have hP_b_pos :
      0 < (quarticSubQuadraticPolynomial a b b d u v μ).eval b := by
    rw [eval_quarticSubQuadratic_at_b]
    have hG_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hub_lt) (sub_neg.mpr hbv_lt)
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_v_neg :
      (quarticSubQuadraticPolynomial a b b d u v μ).eval v < 0 := by
    rw [eval_quarticSubQuadratic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav_lt
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv_lt
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd_lt
    have hsq_pos : 0 < (v - b) * (v - b) := mul_pos hvb_pos hvb_pos
    have htail_neg : (v - a) * ((v - b) * (v - b)) * (v - d) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hva_pos hsq_pos) hvd_neg
    nlinarith [htail_neg]
  have hP_d_neg :
      (quarticSubQuadraticPolynomial a b b d u v μ).eval d < 0 := by
    rw [eval_quarticSubQuadratic_at_d]
    have hG_pos : 0 < (d - u) * (d - v) :=
      mul_pos (sub_pos.mpr hud_lt) (sub_pos.mpr hvd_lt)
    nlinarith [mul_pos hμ hG_pos]
  exact splits_of_two_sign_change_intervals_and_both_tails_of_le
    (quarticSubQuadratic_ne_zero a b b d u v μ)
    (by rw [natDegree_quarticSubQuadratic])
    (le_of_lt hau_lt) hub_lt hbv_lt le_rfl (le_of_lt hvd_lt)
    (le_of_lt hP_a_neg)
    (mul_neg_of_neg_of_pos hP_u_neg hP_b_pos)
    (mul_neg_of_pos_of_neg hP_b_pos hP_v_neg)
    (le_of_lt hP_d_neg)
    (tendsto_eval_quarticSubQuadratic_atBot_atTop a b b d u v μ)
    (tendsto_eval_quarticSubQuadratic_atTop_atTop a b b d u v μ)

/-- Upper repeated-left-root boundary `c = d` for the normalized
quartic-minus-quadratic factor. -/
lemma quarticSubQuadraticSplits_of_upper_left_repeated
    {a b d u v μ : ℝ} (hab : a < b) (hbd : b < d)
    (huv : u ≤ v) (hau : a ≤ u) (hbv : b ≤ v) (hud : u ≤ d)
    (hvd : v ≤ d) (hμ : 0 < μ) :
    (quarticSubQuadraticPolynomial a b d d u v μ).Splits := by
  by_cases hua_eq : u = a
  · subst u
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := a) (a := b) (b := d) (c := d) (u := v)
      (le_of_lt hbd) le_rfl hbv hvd hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases hub_eq : u = b
  · subst u
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := b) (a := a) (b := d) (c := d) (u := v)
      (le_of_lt (lt_trans hab hbd)) le_rfl
      ((le_of_lt hab).trans hbv) hvd hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases hud_eq : u = d
  · subst u
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := d) (a := a) (b := b) (c := d) (u := v)
      (le_of_lt hab) (le_of_lt hbd) ((le_of_lt hab).trans hbv) hvd hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases hvb_eq : v = b
  · subst v
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := b) (a := a) (b := d) (c := d) (u := u)
      (le_of_lt (lt_trans hab hbd)) le_rfl hau hud hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases hvd_eq : v = d
  · subst v
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := d) (a := a) (b := b) (c := d) (u := u)
      (le_of_lt hab) (le_of_lt hbd) hau hud hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  have hau_lt : a < u := lt_of_le_of_ne hau (by intro h; exact hua_eq h.symm)
  have hud_lt : u < d := lt_of_le_of_ne hud hud_eq
  have hbv_lt : b < v := lt_of_le_of_ne hbv (by intro h; exact hvb_eq h.symm)
  have hvd_lt : v < d := lt_of_le_of_ne hvd hvd_eq
  have hav_lt : a < v := lt_trans hab hbv_lt
  have hP_a_neg :
      (quarticSubQuadraticPolynomial a b d d u v μ).eval a < 0 := by
    rw [eval_quarticSubQuadratic_at_a]
    have hG_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hau_lt) (sub_neg.mpr hav_lt)
    nlinarith [mul_pos hμ hG_pos]
  have hP_d_neg :
      (quarticSubQuadraticPolynomial a b d d u v μ).eval d < 0 := by
    rw [eval_quarticSubQuadratic_at_d]
    have hG_pos : 0 < (d - u) * (d - v) :=
      mul_pos (sub_pos.mpr hud_lt) (sub_pos.mpr hvd_lt)
    nlinarith [mul_pos hμ hG_pos]
  by_cases hub_lt : u < b
  · have hP_u_neg :
        (quarticSubQuadraticPolynomial a b d d u v μ).eval u < 0 := by
      rw [eval_quarticSubQuadratic_at_u]
      have hua_pos : 0 < u - a := sub_pos.mpr hau_lt
      have hub_neg : u - b < 0 := sub_neg.mpr hub_lt
      have hud_neg : u - d < 0 := sub_neg.mpr hud_lt
      have hsq_pos : 0 < (u - d) * (u - d) :=
        mul_pos_of_neg_of_neg hud_neg hud_neg
      have hhead_neg : (u - a) * (u - b) < 0 :=
        mul_neg_of_pos_of_neg hua_pos hub_neg
      nlinarith [mul_neg_of_neg_of_pos hhead_neg hsq_pos]
    have hP_b_pos :
        0 < (quarticSubQuadraticPolynomial a b d d u v μ).eval b := by
      rw [eval_quarticSubQuadratic_at_b]
      have hG_neg : (b - u) * (b - v) < 0 :=
        mul_neg_of_pos_of_neg (sub_pos.mpr hub_lt) (sub_neg.mpr hbv_lt)
      nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
    have hP_v_pos :
        0 < (quarticSubQuadraticPolynomial a b d d u v μ).eval v := by
      rw [eval_quarticSubQuadratic_at_v]
      have hva_pos : 0 < v - a := sub_pos.mpr hav_lt
      have hvb_pos : 0 < v - b := sub_pos.mpr hbv_lt
      have hvd_neg : v - d < 0 := sub_neg.mpr hvd_lt
      have hsq_pos : 0 < (v - d) * (v - d) :=
        mul_pos_of_neg_of_neg hvd_neg hvd_neg
      have hhead_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
      nlinarith [mul_pos hhead_pos hsq_pos]
    exact splits_of_two_sign_change_intervals_and_both_tails_of_le
      (quarticSubQuadratic_ne_zero a b d d u v μ)
      (by rw [natDegree_quarticSubQuadratic])
      (le_of_lt hau_lt) hub_lt hvd_lt hbv le_rfl
      (le_of_lt hP_a_neg)
      (mul_neg_of_neg_of_pos hP_u_neg hP_b_pos)
      (mul_neg_of_pos_of_neg hP_v_pos hP_d_neg)
      (le_of_lt hP_d_neg)
      (tendsto_eval_quarticSubQuadratic_atBot_atTop a b d d u v μ)
      (tendsto_eval_quarticSubQuadratic_atTop_atTop a b d d u v μ)
  · have hbu_lt : b < u :=
      lt_of_le_of_ne (le_of_not_gt hub_lt) (by intro h; exact hub_eq h.symm)
    have hP_b_neg :
        (quarticSubQuadraticPolynomial a b d d u v μ).eval b < 0 := by
      rw [eval_quarticSubQuadratic_at_b]
      have hG_pos : 0 < (b - u) * (b - v) :=
        mul_pos_of_neg_of_neg (sub_neg.mpr hbu_lt) (sub_neg.mpr hbv_lt)
      nlinarith [mul_pos hμ hG_pos]
    have hP_u_pos :
        0 < (quarticSubQuadraticPolynomial a b d d u v μ).eval u := by
      rw [eval_quarticSubQuadratic_at_u]
      have hua_pos : 0 < u - a := sub_pos.mpr hau_lt
      have hub_pos : 0 < u - b := sub_pos.mpr hbu_lt
      have hud_neg : u - d < 0 := sub_neg.mpr hud_lt
      have hsq_pos : 0 < (u - d) * (u - d) :=
        mul_pos_of_neg_of_neg hud_neg hud_neg
      have hhead_pos : 0 < (u - a) * (u - b) := mul_pos hua_pos hub_pos
      nlinarith [mul_pos hhead_pos hsq_pos]
    have hP_v_pos :
        0 < (quarticSubQuadraticPolynomial a b d d u v μ).eval v := by
      rw [eval_quarticSubQuadratic_at_v]
      have hva_pos : 0 < v - a := sub_pos.mpr hav_lt
      have hvb_pos : 0 < v - b := sub_pos.mpr hbv_lt
      have hvd_neg : v - d < 0 := sub_neg.mpr hvd_lt
      have hsq_pos : 0 < (v - d) * (v - d) :=
        mul_pos_of_neg_of_neg hvd_neg hvd_neg
      have hhead_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
      nlinarith [mul_pos hhead_pos hsq_pos]
    exact splits_of_two_sign_change_intervals_and_both_tails_of_le
      (quarticSubQuadratic_ne_zero a b d d u v μ)
      (by rw [natDegree_quarticSubQuadratic])
      (le_of_lt hab) hbu_lt hvd_lt huv le_rfl
      (le_of_lt hP_a_neg)
      (mul_neg_of_neg_of_pos hP_b_neg hP_u_pos)
      (mul_neg_of_pos_of_neg hP_v_pos hP_d_neg)
      (le_of_lt hP_d_neg)
      (tendsto_eval_quarticSubQuadratic_atBot_atTop a b d d u v μ)
      (tendsto_eval_quarticSubQuadratic_atTop_atTop a b d d u v μ)

/-- Double-pair repeated-left-root boundary `a = b < c = d` for the normalized
quartic-minus-quadratic factor. -/
lemma quarticSubQuadraticSplits_of_double_left_pair
    {a c u v μ : ℝ} (hac : a < c) (huv : u ≤ v)
    (hau : a ≤ u) (huc : u ≤ c) (hvc : v ≤ c) (hμ : 0 < μ) :
    (quarticSubQuadraticPolynomial a a c c u v μ).Splits := by
  by_cases hua_eq : u = a
  · subst u
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := a) (a := a) (b := c) (c := c) (u := v)
      (le_of_lt hac) le_rfl huv hvc hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  by_cases hvc_eq : v = c
  · subst v
    have hsplits := quarticSubQuadratic_splits_of_common_root
      (r := c) (a := a) (b := a) (c := c) (u := u)
      le_rfl (le_of_lt hac) hau huc hμ
    simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
      using hsplits
  have hau_lt : a < u := lt_of_le_of_ne hau (by intro h; exact hua_eq h.symm)
  have hvc_lt : v < c := lt_of_le_of_ne hvc hvc_eq
  have huc_lt : u < c := lt_of_le_of_lt huv hvc_lt
  have hav_lt : a < v := lt_of_lt_of_le hau_lt huv
  have hP_a_neg :
      (quarticSubQuadraticPolynomial a a c c u v μ).eval a < 0 := by
    rw [eval_quarticSubQuadratic_at_a]
    have hG_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hau_lt) (sub_neg.mpr hav_lt)
    nlinarith [mul_pos hμ hG_pos]
  have hP_u_pos :
      0 < (quarticSubQuadraticPolynomial a a c c u v μ).eval u := by
    rw [eval_quarticSubQuadratic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau_lt
    have huc_neg : u - c < 0 := sub_neg.mpr huc_lt
    have hsq_left : 0 < (u - a) * (u - a) := mul_pos hua_pos hua_pos
    have hsq_right : 0 < (u - c) * (u - c) :=
      mul_pos_of_neg_of_neg huc_neg huc_neg
    nlinarith [mul_pos hsq_left hsq_right]
  have hP_v_pos :
      0 < (quarticSubQuadraticPolynomial a a c c u v μ).eval v := by
    rw [eval_quarticSubQuadratic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav_lt
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc_lt
    have hsq_left : 0 < (v - a) * (v - a) := mul_pos hva_pos hva_pos
    have hsq_right : 0 < (v - c) * (v - c) :=
      mul_pos_of_neg_of_neg hvc_neg hvc_neg
    nlinarith [mul_pos hsq_left hsq_right]
  have hP_c_neg :
      (quarticSubQuadraticPolynomial a a c c u v μ).eval c < 0 := by
    rw [eval_quarticSubQuadratic_at_c]
    have hG_pos : 0 < (c - u) * (c - v) :=
      mul_pos (sub_pos.mpr huc_lt) (sub_pos.mpr hvc_lt)
    nlinarith [mul_pos hμ hG_pos]
  exact splits_of_two_sign_change_intervals_and_both_tails_of_le
    (quarticSubQuadratic_ne_zero a a c c u v μ)
    (by rw [natDegree_quarticSubQuadratic])
    le_rfl hau_lt hvc_lt huv le_rfl
    (le_of_lt hP_a_neg)
    (mul_neg_of_neg_of_pos hP_a_neg hP_u_pos)
    (mul_neg_of_pos_of_neg hP_v_pos hP_c_neg)
    (le_of_lt hP_c_neg)
    (tendsto_eval_quarticSubQuadratic_atBot_atTop a a c c u v μ)
    (tendsto_eval_quarticSubQuadratic_atTop_atTop a a c c u v μ)

/-- The normalized quartic-minus-quadratic endpoint factor splits under the
closed interlacing inequalities. -/
theorem quarticSubQuadraticSplits :
    quarticSubQuadraticSplitsStatement := by
  intro a b c d u v μ hab hbc hcd huv hau hbv huc hvd _hd0 _hv0 hμ
  by_cases hab_eq : a = b
  · subst b
    by_cases hac_eq : a = c
    · subst c
      have hua : u = a := le_antisymm huc hau
      subst u
      have hsplits := quarticSubQuadratic_splits_of_common_root
        (r := a) (a := a) (b := a) (c := d) (u := v)
        le_rfl hcd huv hvd hμ
      simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
        using hsplits
    · have hac : a < c := lt_of_le_of_ne hbc hac_eq
      by_cases hcd_eq : c = d
      · subst d
        exact quarticSubQuadraticSplits_of_double_left_pair
          hac huv hau huc hvd hμ
      · have hcd_lt : c < d := lt_of_le_of_ne hcd hcd_eq
        exact quarticSubQuadraticSplits_of_lower_left_repeated
          hac hcd_lt huv hau huc hvd hμ
  · have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
    by_cases hbc_eq : b = c
    · subst c
      by_cases hbd_eq : b = d
      · subst d
        have hvb : v = b := le_antisymm hvd hbv
        subst v
        have hsplits := quarticSubQuadratic_splits_of_common_root
          (r := b) (a := a) (b := b) (c := b) (u := u)
          (le_of_lt hab_lt) le_rfl hau huc hμ
        simpa [quarticSubQuadraticPolynomial, mul_comm, mul_left_comm, mul_assoc]
          using hsplits
      · have hbd_lt : b < d := lt_of_le_of_ne hcd hbd_eq
        exact quarticSubQuadraticSplits_of_middle_left_repeated
          hab_lt hbd_lt huv hau huc hbv hvd hμ
    · have hbc_lt : b < c := lt_of_le_of_ne hbc hbc_eq
      by_cases hcd_eq : c = d
      · subst d
        exact quarticSubQuadraticSplits_of_upper_left_repeated
          hab_lt hbc_lt huv hau hbv huc hvd hμ
      · have hcd_lt : c < d := lt_of_le_of_ne hcd hcd_eq
        exact quarticSubQuadraticSplits_of_strict_left_roots
          hab_lt hbc_lt hcd_lt huv hau hbv huc hvd hμ

/-- Double endpoint-zero corner of the normalized quartic/cubic boundary.
Factoring out `X` leaves the proved cubic/quadratic leaf. -/
lemma xSubQuarticCubicSplits_of_endpoint_roots_zero {a b c u v μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v)
    (hau : a ≤ u) (hbv : b ≤ v) (huc : u ≤ c)
    (hc0 : c ≤ 0) (hv0 : v ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c 0 u v 0 μ).Splits := by
  let Q : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hQ : Q.Splits := by
    dsimp [Q]
    exact xSubCubicQuadraticSplits hab hbc huv hau hbv huc hc0 hv0 hμ
  have hfactor :
      xSubQuarticCubicPolynomial a b c 0 u v 0 μ = X * Q := by
    simp [Q, xSubQuarticCubicPolynomial]
    ring
  rw [hfactor]
  exact Polynomial.Splits.X.mul hQ

/-- The right-only endpoint-zero quartic/cubic boundary follows from the
quartic-minus-quadratic factor obtained after removing the common `X`. -/
theorem xSubQuarticCubicRightOnlyEndpointZeroBoundaryCases_of_quarticSubQuadratic
    (hquad : quarticSubQuadraticSplitsStatement) :
    xSubQuarticCubicRightOnlyEndpointZeroBoundaryCasesStatement := by
  intro a b c d u v w μ hab hbc hcd huv _hvw hau hbv _hcw huc hvd hd0 _hw0 hμ
    hw_eq _hd_ne
  subst w
  let Q : ℝ[X] := quarticSubQuadraticPolynomial a b c d u v μ
  have hv0 : v ≤ 0 := hvd.trans hd0
  have hQ : Q.Splits := by
    dsimp [Q]
    exact hquad hab hbc hcd huv hau hbv huc hvd hd0 hv0 hμ
  have hfactor :
      xSubQuarticCubicPolynomial a b c d u v 0 μ = X * Q := by
    simp [Q, quarticSubQuadraticPolynomial, xSubQuarticCubicPolynomial]
    ring
  rw [hfactor]
  exact Polynomial.Splits.X.mul hQ

/-- The right-only endpoint-zero quartic/cubic boundary. -/
theorem xSubQuarticCubicRightOnlyEndpointZeroBoundaryCases :
    xSubQuarticCubicRightOnlyEndpointZeroBoundaryCasesStatement :=
  xSubQuarticCubicRightOnlyEndpointZeroBoundaryCases_of_quarticSubQuadratic
    quarticSubQuadraticSplits

/-- Lower repeated-left-root boundary `a = b` for the normalized quartic/cubic
terminal. -/
lemma xSubQuarticCubicSplits_of_lower_left_repeated
    {a c d u v w μ : ℝ} (hac : a < c) (hcd : c < d)
    (huv : u ≤ v) (hvw : v ≤ w) (hau : a ≤ u) (hcw : c ≤ w)
    (huc : u ≤ c) (hvd : v ≤ d) (hd0 : d ≤ 0) (hw0 : w ≤ 0)
    (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a a c d u v w μ).Splits := by
  by_cases hw_eq : w = 0
  · by_cases hd_eq : d = 0
    · subst d
      subst w
      exact xSubQuarticCubicSplits_of_endpoint_roots_zero
        le_rfl (le_of_lt hac) huv hau (hau.trans huv) huc
        (le_of_lt hcd) hvd hμ
    · exact xSubQuarticCubicRightOnlyEndpointZeroBoundaryCases
        le_rfl (le_of_lt hac) (le_of_lt hcd) huv hvw hau
        (hau.trans huv) hcw huc hvd hd0 hw0 hμ hw_eq hd_eq
  have hcommon_dispatch :
      (u = a ∨ u = a ∨ u = c ∨ v = a ∨ v = c ∨ v = d ∨
          w = c ∨ w = d) →
        (xSubQuarticCubicPolynomial a a c d u v w μ).Splits := by
    intro hcommon
    exact xSubQuarticCubicSplits_of_common_root_cases
      le_rfl (le_of_lt hac) (le_of_lt hcd) huv hvw hau
      (hau.trans huv) hcw huc hvd hd0 hw0 hμ hcommon
  by_cases hua_eq : u = a
  · exact hcommon_dispatch (by simp [hua_eq])
  by_cases huc_eq : u = c
  · exact hcommon_dispatch (by simp [huc_eq])
  by_cases hvc_eq : v = c
  · exact hcommon_dispatch (by simp [hvc_eq])
  by_cases hvd_eq : v = d
  · exact hcommon_dispatch (by simp [hvd_eq])
  by_cases hwc_eq : w = c
  · exact hcommon_dispatch (by simp [hwc_eq])
  by_cases hwd_eq : w = d
  · exact hcommon_dispatch (by simp [hwd_eq])
  have hau_lt : a < u := lt_of_le_of_ne hau (by intro h; exact hua_eq h.symm)
  have huc_lt : u < c := lt_of_le_of_ne huc huc_eq
  have hud_lt : u < d := lt_trans huc_lt hcd
  have hu0_lt : u < 0 := lt_of_lt_of_le hud_lt hd0
  have hav_lt : a < v := lt_of_lt_of_le hau_lt huv
  have haw_lt : a < w := lt_trans hac (lt_of_le_of_ne hcw (by intro h; exact hwc_eq h.symm))
  have hvd_lt : v < d := lt_of_le_of_ne hvd hvd_eq
  have hw0_lt : w < 0 := lt_of_le_of_ne hw0 hw_eq
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a a c d u v w μ).eval a := by
    rw [eval_xSubQuarticCubic_at_a]
    have hau_neg : a - u < 0 := sub_neg.mpr hau_lt
    have hav_neg : a - v < 0 := sub_neg.mpr hav_lt
    have haw_neg : a - w < 0 := sub_neg.mpr haw_lt
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg :
      (xSubQuarticCubicPolynomial a a c d u v w μ).eval u < 0 := by
    rw [eval_xSubQuarticCubic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau_lt
    have huc_neg : u - c < 0 := sub_neg.mpr huc_lt
    have hud_neg : u - d < 0 := sub_neg.mpr hud_lt
    have hsq_pos : 0 < (u - a) * (u - a) := mul_pos hua_pos hua_pos
    have h123_neg : (u - a) * (u - a) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg hsq_pos huc_neg
    have hquartic_pos : 0 < (u - a) * (u - a) * (u - c) * (u - d) :=
      mul_pos_of_neg_of_neg h123_neg hud_neg
    exact mul_neg_of_neg_of_pos hu0_lt hquartic_pos
  by_cases hvc_lt : v < c
  · have hv0_lt : v < 0 := lt_of_lt_of_le (lt_trans hvc_lt hcd) hd0
    have hP_v_neg :
        (xSubQuarticCubicPolynomial a a c d u v w μ).eval v < 0 := by
      rw [eval_xSubQuarticCubic_at_v]
      have hva_pos : 0 < v - a := sub_pos.mpr hav_lt
      have hvc_neg : v - c < 0 := sub_neg.mpr hvc_lt
      have hvd_neg : v - d < 0 := sub_neg.mpr (lt_trans hvc_lt hcd)
      have hsq_pos : 0 < (v - a) * (v - a) := mul_pos hva_pos hva_pos
      have h123_neg : (v - a) * (v - a) * (v - c) < 0 :=
        mul_neg_of_pos_of_neg hsq_pos hvc_neg
      have hquartic_pos : 0 < (v - a) * (v - a) * (v - c) * (v - d) :=
        mul_pos_of_neg_of_neg h123_neg hvd_neg
      exact mul_neg_of_neg_of_pos hv0_lt hquartic_pos
    have hP_c_pos :
        0 < (xSubQuarticCubicPolynomial a a c d u v w μ).eval c := by
      rw [eval_xSubQuarticCubic_at_c]
      have hcu_pos : 0 < c - u := sub_pos.mpr huc_lt
      have hcv_pos : 0 < c - v := sub_pos.mpr hvc_lt
      have hcw_neg : c - w < 0 :=
        sub_neg.mpr (lt_of_le_of_ne hcw (by intro h; exact hwc_eq h.symm))
      have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
      have hG_neg : (c - u) * (c - v) * (c - w) < 0 :=
        mul_neg_of_pos_of_neg h12_pos hcw_neg
      nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
    by_cases hwd_lt : w < d
    · have hP_w_pos :
          0 < (xSubQuarticCubicPolynomial a a c d u v w μ).eval w := by
        rw [eval_xSubQuarticCubic_at_w]
        have hwa_pos : 0 < w - a := sub_pos.mpr haw_lt
        have hwc_pos : 0 < w - c :=
          sub_pos.mpr (lt_of_le_of_ne hcw (by intro h; exact hwc_eq h.symm))
        have hwd_neg : w - d < 0 := sub_neg.mpr hwd_lt
        have hsq_pos : 0 < (w - a) * (w - a) := mul_pos hwa_pos hwa_pos
        have h123_pos : 0 < (w - a) * (w - a) * (w - c) :=
          mul_pos hsq_pos hwc_pos
        have hquartic_neg : (w - a) * (w - a) * (w - c) * (w - d) < 0 :=
          mul_neg_of_pos_of_neg h123_pos hwd_neg
        exact mul_pos_of_neg_of_neg hw0_lt hquartic_neg
      have hP_d_neg :
          (xSubQuarticCubicPolynomial a a c d u v w μ).eval d < 0 := by
        rw [eval_xSubQuarticCubic_at_d]
        have hdu_pos : 0 < d - u := sub_pos.mpr hud_lt
        have hdv_pos : 0 < d - v := sub_pos.mpr (lt_trans hvc_lt hcd)
        have hdw_pos : 0 < d - w := sub_pos.mpr hwd_lt
        have h12_pos : 0 < (d - u) * (d - v) := mul_pos hdu_pos hdv_pos
        have hG_pos : 0 < (d - u) * (d - v) * (d - w) :=
          mul_pos h12_pos hdw_pos
        nlinarith [mul_pos hμ hG_pos]
      exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
        huv hvw hw0 hμ le_rfl hau_lt hvc_lt hwd_lt huv hcw hd0
        (le_of_lt hP_a_pos)
        (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
        (mul_neg_of_neg_of_pos hP_v_neg hP_c_pos)
        (mul_neg_of_pos_of_neg hP_w_pos hP_d_neg)
    · have hdw_lt : d < w :=
        lt_of_le_of_ne (le_of_not_gt hwd_lt) (by intro h; exact hwd_eq h.symm)
      have hP_d_pos :
          0 < (xSubQuarticCubicPolynomial a a c d u v w μ).eval d := by
        rw [eval_xSubQuarticCubic_at_d]
        have hdu_pos : 0 < d - u := sub_pos.mpr hud_lt
        have hdv_pos : 0 < d - v := sub_pos.mpr (lt_trans hvc_lt hcd)
        have hdw_neg : d - w < 0 := sub_neg.mpr hdw_lt
        have h12_pos : 0 < (d - u) * (d - v) := mul_pos hdu_pos hdv_pos
        have hG_neg : (d - u) * (d - v) * (d - w) < 0 :=
          mul_neg_of_pos_of_neg h12_pos hdw_neg
        nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
      have hP_w_neg :
          (xSubQuarticCubicPolynomial a a c d u v w μ).eval w < 0 := by
        rw [eval_xSubQuarticCubic_at_w]
        have hwa_pos : 0 < w - a := sub_pos.mpr haw_lt
        have hwc_pos : 0 < w - c :=
          sub_pos.mpr (lt_of_le_of_ne hcw (by intro h; exact hwc_eq h.symm))
        have hwd_pos : 0 < w - d := sub_pos.mpr hdw_lt
        have hsq_pos : 0 < (w - a) * (w - a) := mul_pos hwa_pos hwa_pos
        have h123_pos : 0 < (w - a) * (w - a) * (w - c) :=
          mul_pos hsq_pos hwc_pos
        have hquartic_pos : 0 < (w - a) * (w - a) * (w - c) * (w - d) :=
          mul_pos h123_pos hwd_pos
        exact mul_neg_of_neg_of_pos hw0_lt hquartic_pos
      exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
        huv hvw hw0 hμ le_rfl hau_lt hvc_lt hdw_lt huv (le_of_lt hcd) hw0
        (le_of_lt hP_a_pos)
        (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
        (mul_neg_of_neg_of_pos hP_v_neg hP_c_pos)
        (mul_neg_of_pos_of_neg hP_d_pos hP_w_neg)
  · have hcv_lt : c < v :=
      lt_of_le_of_ne (le_of_not_gt hvc_lt) (by intro h; exact hvc_eq h.symm)
    have hv0_lt : v < 0 := lt_of_lt_of_le hvd_lt hd0
    have hP_c_neg :
        (xSubQuarticCubicPolynomial a a c d u v w μ).eval c < 0 := by
      rw [eval_xSubQuarticCubic_at_c]
      have hcu_pos : 0 < c - u := sub_pos.mpr huc_lt
      have hcv_neg : c - v < 0 := sub_neg.mpr hcv_lt
      have hcw_neg : c - w < 0 :=
        sub_neg.mpr (lt_of_le_of_ne hcw (by intro h; exact hwc_eq h.symm))
      have h12_neg : (c - u) * (c - v) < 0 :=
        mul_neg_of_pos_of_neg hcu_pos hcv_neg
      have hG_pos : 0 < (c - u) * (c - v) * (c - w) :=
        mul_pos_of_neg_of_neg h12_neg hcw_neg
      nlinarith [mul_pos hμ hG_pos]
    have hP_v_pos :
        0 < (xSubQuarticCubicPolynomial a a c d u v w μ).eval v := by
      rw [eval_xSubQuarticCubic_at_v]
      have hva_pos : 0 < v - a := sub_pos.mpr hav_lt
      have hvc_pos : 0 < v - c := sub_pos.mpr hcv_lt
      have hvd_neg : v - d < 0 := sub_neg.mpr hvd_lt
      have hsq_pos : 0 < (v - a) * (v - a) := mul_pos hva_pos hva_pos
      have h123_pos : 0 < (v - a) * (v - a) * (v - c) :=
        mul_pos hsq_pos hvc_pos
      have hquartic_neg : (v - a) * (v - a) * (v - c) * (v - d) < 0 :=
        mul_neg_of_pos_of_neg h123_pos hvd_neg
      exact mul_pos_of_neg_of_neg hv0_lt hquartic_neg
    by_cases hwd_lt : w < d
    · have hP_w_pos :
          0 < (xSubQuarticCubicPolynomial a a c d u v w μ).eval w := by
        rw [eval_xSubQuarticCubic_at_w]
        have hwa_pos : 0 < w - a := sub_pos.mpr haw_lt
        have hwc_pos : 0 < w - c :=
          sub_pos.mpr (lt_of_le_of_ne hcw (by intro h; exact hwc_eq h.symm))
        have hwd_neg : w - d < 0 := sub_neg.mpr hwd_lt
        have hsq_pos : 0 < (w - a) * (w - a) := mul_pos hwa_pos hwa_pos
        have h123_pos : 0 < (w - a) * (w - a) * (w - c) :=
          mul_pos hsq_pos hwc_pos
        have hquartic_neg : (w - a) * (w - a) * (w - c) * (w - d) < 0 :=
          mul_neg_of_pos_of_neg h123_pos hwd_neg
        exact mul_pos_of_neg_of_neg hw0_lt hquartic_neg
      have hP_d_neg :
          (xSubQuarticCubicPolynomial a a c d u v w μ).eval d < 0 := by
        rw [eval_xSubQuarticCubic_at_d]
        have hdu_pos : 0 < d - u := sub_pos.mpr hud_lt
        have hdv_pos : 0 < d - v := sub_pos.mpr hvd_lt
        have hdw_pos : 0 < d - w := sub_pos.mpr hwd_lt
        have h12_pos : 0 < (d - u) * (d - v) := mul_pos hdu_pos hdv_pos
        have hG_pos : 0 < (d - u) * (d - v) * (d - w) :=
          mul_pos h12_pos hdw_pos
        nlinarith [mul_pos hμ hG_pos]
      exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
        huv hvw hw0 hμ le_rfl hau_lt hcv_lt hwd_lt huc hvw hd0
        (le_of_lt hP_a_pos)
        (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
        (mul_neg_of_neg_of_pos hP_c_neg hP_v_pos)
        (mul_neg_of_pos_of_neg hP_w_pos hP_d_neg)
    · have hdw_lt : d < w :=
        lt_of_le_of_ne (le_of_not_gt hwd_lt) (by intro h; exact hwd_eq h.symm)
      have hP_d_pos :
          0 < (xSubQuarticCubicPolynomial a a c d u v w μ).eval d := by
        rw [eval_xSubQuarticCubic_at_d]
        have hdu_pos : 0 < d - u := sub_pos.mpr hud_lt
        have hdv_pos : 0 < d - v := sub_pos.mpr hvd_lt
        have hdw_neg : d - w < 0 := sub_neg.mpr hdw_lt
        have h12_pos : 0 < (d - u) * (d - v) := mul_pos hdu_pos hdv_pos
        have hG_neg : (d - u) * (d - v) * (d - w) < 0 :=
          mul_neg_of_pos_of_neg h12_pos hdw_neg
        nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
      have hP_w_neg :
          (xSubQuarticCubicPolynomial a a c d u v w μ).eval w < 0 := by
        rw [eval_xSubQuarticCubic_at_w]
        have hwa_pos : 0 < w - a := sub_pos.mpr haw_lt
        have hwc_pos : 0 < w - c :=
          sub_pos.mpr (lt_of_le_of_ne hcw (by intro h; exact hwc_eq h.symm))
        have hwd_pos : 0 < w - d := sub_pos.mpr hdw_lt
        have hsq_pos : 0 < (w - a) * (w - a) := mul_pos hwa_pos hwa_pos
        have h123_pos : 0 < (w - a) * (w - a) * (w - c) :=
          mul_pos hsq_pos hwc_pos
        have hquartic_pos : 0 < (w - a) * (w - a) * (w - c) * (w - d) :=
          mul_pos h123_pos hwd_pos
        exact mul_neg_of_neg_of_pos hw0_lt hquartic_pos
      exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
        huv hvw hw0 hμ le_rfl hau_lt hcv_lt hdw_lt huc hvd hw0
        (le_of_lt hP_a_pos)
        (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
        (mul_neg_of_neg_of_pos hP_c_neg hP_v_pos)
        (mul_neg_of_pos_of_neg hP_d_pos hP_w_neg)

/-- Middle repeated-left-root boundary `b = c` for the normalized quartic/cubic
terminal. -/
lemma xSubQuarticCubicSplits_of_middle_left_repeated
    {a b d u v w μ : ℝ} (hab : a < b) (hbd : b < d)
    (huv : u ≤ v) (hvw : v ≤ w) (hau : a ≤ u) (hub : u ≤ b)
    (hbv : b ≤ v) (hbw : b ≤ w) (hvd : v ≤ d)
    (hd0 : d ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b b d u v w μ).Splits := by
  have hcommon_dispatch :
      (u = a ∨ u = b ∨ u = b ∨ v = b ∨ v = b ∨ v = d ∨
          w = b ∨ w = d) →
        (xSubQuarticCubicPolynomial a b b d u v w μ).Splits := by
    intro hcommon
    exact xSubQuarticCubicSplits_of_common_root_cases
      (le_of_lt hab) le_rfl (le_of_lt hbd) huv hvw hau hbv hbw hub hvd
      hd0 hw0 hμ hcommon
  by_cases hua_eq : u = a
  · exact hcommon_dispatch (by simp [hua_eq])
  by_cases hub_eq : u = b
  · exact hcommon_dispatch (by simp [hub_eq])
  by_cases hvb_eq : v = b
  · exact hcommon_dispatch (by simp [hvb_eq])
  by_cases hvd_eq : v = d
  · exact hcommon_dispatch (by simp [hvd_eq])
  by_cases hwb_eq : w = b
  · exact hcommon_dispatch (by simp [hwb_eq])
  by_cases hwd_eq : w = d
  · exact hcommon_dispatch (by simp [hwd_eq])
  by_cases hw_eq : w = 0
  · have hd_ne : d ≠ 0 := by
      intro hd_eq
      exact hwd_eq (by rw [hw_eq, hd_eq])
    exact xSubQuarticCubicRightOnlyEndpointZeroBoundaryCases
      (le_of_lt hab) le_rfl (le_of_lt hbd) huv hvw hau hbv hbw hub hvd
      hd0 hw0 hμ hw_eq hd_ne
  have hau_lt : a < u := lt_of_le_of_ne hau (by intro h; exact hua_eq h.symm)
  have hub_lt : u < b := lt_of_le_of_ne hub hub_eq
  have hbv_lt : b < v := lt_of_le_of_ne hbv (by intro h; exact hvb_eq h.symm)
  have hbw_lt : b < w := lt_of_le_of_ne hbw (by intro h; exact hwb_eq h.symm)
  have hvd_lt : v < d := lt_of_le_of_ne hvd hvd_eq
  have hud_lt : u < d := lt_trans hub_lt hbd
  have hu0_lt : u < 0 := lt_of_lt_of_le hud_lt hd0
  have hav_lt : a < v := lt_trans hab hbv_lt
  have haw_lt : a < w := lt_trans hab hbw_lt
  have hv0_lt : v < 0 := lt_of_lt_of_le hvd_lt hd0
  have hw0_lt : w < 0 := lt_of_le_of_ne hw0 hw_eq
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a b b d u v w μ).eval a := by
    rw [eval_xSubQuarticCubic_at_a]
    have hau_neg : a - u < 0 := sub_neg.mpr hau_lt
    have hav_neg : a - v < 0 := sub_neg.mpr hav_lt
    have haw_neg : a - w < 0 := sub_neg.mpr haw_lt
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_pos :
      0 < (xSubQuarticCubicPolynomial a b b d u v w μ).eval u := by
    rw [eval_xSubQuarticCubic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau_lt
    have hub_neg : u - b < 0 := sub_neg.mpr hub_lt
    have hud_neg : u - d < 0 := sub_neg.mpr hud_lt
    have hsq_pos : 0 < (u - b) * (u - b) :=
      mul_pos_of_neg_of_neg hub_neg hub_neg
    have htail_neg : (u - a) * ((u - b) * (u - b)) * (u - d) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hua_pos hsq_pos) hud_neg
    nlinarith [mul_pos_of_neg_of_neg hu0_lt htail_neg]
  have hP_b_neg :
      (xSubQuarticCubicPolynomial a b b d u v w μ).eval b < 0 := by
    rw [eval_xSubQuarticCubic_at_b]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub_lt
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv_lt
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw_lt
    have h12_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg hbu_pos hbv_neg
    have hG_pos : 0 < (b - u) * (b - v) * (b - w) :=
      mul_pos_of_neg_of_neg h12_neg hbw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos :
      0 < (xSubQuarticCubicPolynomial a b b d u v w μ).eval v := by
    rw [eval_xSubQuarticCubic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav_lt
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv_lt
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd_lt
    have hsq_pos : 0 < (v - b) * (v - b) := mul_pos hvb_pos hvb_pos
    have htail_neg : (v - a) * ((v - b) * (v - b)) * (v - d) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hva_pos hsq_pos) hvd_neg
    nlinarith [mul_pos_of_neg_of_neg hv0_lt htail_neg]
  by_cases hwd_lt : w < d
  · have hP_w_pos :
        0 < (xSubQuarticCubicPolynomial a b b d u v w μ).eval w := by
      rw [eval_xSubQuarticCubic_at_w]
      have hwa_pos : 0 < w - a := sub_pos.mpr haw_lt
      have hwb_pos : 0 < w - b := sub_pos.mpr hbw_lt
      have hwd_neg : w - d < 0 := sub_neg.mpr hwd_lt
      have hsq_pos : 0 < (w - b) * (w - b) := mul_pos hwb_pos hwb_pos
      have htail_neg : (w - a) * ((w - b) * (w - b)) * (w - d) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hwa_pos hsq_pos) hwd_neg
      nlinarith [mul_pos_of_neg_of_neg hw0_lt htail_neg]
    have hP_d_neg :
        (xSubQuarticCubicPolynomial a b b d u v w μ).eval d < 0 := by
      rw [eval_xSubQuarticCubic_at_d]
      have hdu_pos : 0 < d - u := sub_pos.mpr hud_lt
      have hdv_pos : 0 < d - v := sub_pos.mpr hvd_lt
      have hdw_pos : 0 < d - w := sub_pos.mpr hwd_lt
      have h12_pos : 0 < (d - u) * (d - v) := mul_pos hdu_pos hdv_pos
      have hG_pos : 0 < (d - u) * (d - v) * (d - w) :=
        mul_pos h12_pos hdw_pos
      nlinarith [mul_pos hμ hG_pos]
    exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
      huv hvw hw0 hμ (le_of_lt hau_lt) hub_lt hbv_lt hwd_lt
      le_rfl hvw hd0 (le_of_lt hP_a_pos)
      (mul_neg_of_pos_of_neg hP_u_pos hP_b_neg)
      (mul_neg_of_neg_of_pos hP_b_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_w_pos hP_d_neg)
  · have hdw_lt : d < w :=
      lt_of_le_of_ne (le_of_not_gt hwd_lt) (by intro h; exact hwd_eq h.symm)
    have hP_d_pos :
        0 < (xSubQuarticCubicPolynomial a b b d u v w μ).eval d := by
      rw [eval_xSubQuarticCubic_at_d]
      have hdu_pos : 0 < d - u := sub_pos.mpr hud_lt
      have hdv_pos : 0 < d - v := sub_pos.mpr hvd_lt
      have hdw_neg : d - w < 0 := sub_neg.mpr hdw_lt
      have h12_pos : 0 < (d - u) * (d - v) := mul_pos hdu_pos hdv_pos
      have hG_neg : (d - u) * (d - v) * (d - w) < 0 :=
        mul_neg_of_pos_of_neg h12_pos hdw_neg
      nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
    have hP_w_neg :
        (xSubQuarticCubicPolynomial a b b d u v w μ).eval w < 0 := by
      rw [eval_xSubQuarticCubic_at_w]
      have hwa_pos : 0 < w - a := sub_pos.mpr haw_lt
      have hwb_pos : 0 < w - b := sub_pos.mpr hbw_lt
      have hwd_pos : 0 < w - d := sub_pos.mpr hdw_lt
      have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
      have h123_pos : 0 < (w - a) * (w - b) * (w - b) :=
        mul_pos h12_pos hwb_pos
      have htail_pos : 0 < (w - a) * (w - b) * (w - b) * (w - d) :=
        mul_pos h123_pos hwd_pos
      exact mul_neg_of_neg_of_pos hw0_lt htail_pos
    exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
      huv hvw hw0 hμ (le_of_lt hau_lt) hub_lt hbv_lt hdw_lt
      le_rfl hvd hw0 (le_of_lt hP_a_pos)
      (mul_neg_of_pos_of_neg hP_u_pos hP_b_neg)
      (mul_neg_of_neg_of_pos hP_b_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_d_pos hP_w_neg)

/-- Upper repeated-left-root boundary `c = d` for the normalized quartic/cubic
terminal. -/
lemma xSubQuarticCubicSplits_of_upper_left_repeated
    {a b d u v w μ : ℝ} (hab : a < b) (hbd : b < d)
    (huv : u ≤ v) (hvw : v ≤ w) (hau : a ≤ u) (hbv : b ≤ v)
    (hdw : d ≤ w) (hud : u ≤ d) (hvd : v ≤ d)
    (hd0 : d ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b d d u v w μ).Splits := by
  have hcommon_dispatch :
      (u = a ∨ u = b ∨ u = d ∨ v = b ∨ v = d ∨ v = d ∨
          w = d ∨ w = d) →
        (xSubQuarticCubicPolynomial a b d d u v w μ).Splits := by
    intro hcommon
    exact xSubQuarticCubicSplits_of_common_root_cases
      (le_of_lt hab) (le_of_lt hbd) le_rfl huv hvw hau hbv hdw
      hud hvd hd0 hw0 hμ hcommon
  by_cases hua_eq : u = a
  · exact hcommon_dispatch (by simp [hua_eq])
  by_cases hub_eq : u = b
  · exact hcommon_dispatch (by simp [hub_eq])
  by_cases hud_eq : u = d
  · exact hcommon_dispatch (by simp [hud_eq])
  by_cases hvb_eq : v = b
  · exact hcommon_dispatch (by simp [hvb_eq])
  by_cases hvd_eq : v = d
  · exact hcommon_dispatch (by simp [hvd_eq])
  by_cases hwd_eq : w = d
  · exact hcommon_dispatch (by simp [hwd_eq])
  by_cases hw_eq : w = 0
  · have hd_ne : d ≠ 0 := by
      intro hd_eq
      exact hwd_eq (by rw [hw_eq, hd_eq])
    exact xSubQuarticCubicRightOnlyEndpointZeroBoundaryCases
      (le_of_lt hab) (le_of_lt hbd) le_rfl huv hvw hau hbv hdw
      hud hvd hd0 hw0 hμ hw_eq hd_ne
  have hau_lt : a < u := lt_of_le_of_ne hau (by intro h; exact hua_eq h.symm)
  have hud_lt : u < d := lt_of_le_of_ne hud hud_eq
  have hbv_lt : b < v := lt_of_le_of_ne hbv (by intro h; exact hvb_eq h.symm)
  have hvd_lt : v < d := lt_of_le_of_ne hvd hvd_eq
  have hdw_lt : d < w :=
    lt_of_le_of_ne hdw (by intro h; exact hwd_eq h.symm)
  have hw0_lt : w < 0 := lt_of_le_of_ne hw0 hw_eq
  have hav_lt : a < v := lt_trans hab hbv_lt
  have haw_lt : a < w := lt_trans (lt_trans hab hbd) hdw_lt
  have hbw_lt : b < w := lt_trans hbd hdw_lt
  have hu0_lt : u < 0 := lt_of_lt_of_le hud_lt hd0
  have hv0_lt : v < 0 := lt_of_lt_of_le hvd_lt hd0
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a b d d u v w μ).eval a := by
    rw [eval_xSubQuarticCubic_at_a]
    have hau_neg : a - u < 0 := sub_neg.mpr hau_lt
    have hav_neg : a - v < 0 := sub_neg.mpr hav_lt
    have haw_neg : a - w < 0 := sub_neg.mpr haw_lt
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_v_neg :
      (xSubQuarticCubicPolynomial a b d d u v w μ).eval v < 0 := by
    rw [eval_xSubQuarticCubic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav_lt
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv_lt
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd_lt
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_neg : (v - a) * (v - b) * (v - d) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvd_neg
    have hquartic_pos : 0 < (v - a) * (v - b) * (v - d) * (v - d) :=
      mul_pos_of_neg_of_neg h123_neg hvd_neg
    exact mul_neg_of_neg_of_pos hv0_lt hquartic_pos
  have hP_d_pos :
      0 < (xSubQuarticCubicPolynomial a b d d u v w μ).eval d := by
    rw [eval_xSubQuarticCubic_at_d]
    have hdu_pos : 0 < d - u := sub_pos.mpr hud_lt
    have hdv_pos : 0 < d - v := sub_pos.mpr hvd_lt
    have hdw_neg : d - w < 0 := sub_neg.mpr hdw_lt
    have h12_pos : 0 < (d - u) * (d - v) := mul_pos hdu_pos hdv_pos
    have hG_neg : (d - u) * (d - v) * (d - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hdw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg :
      (xSubQuarticCubicPolynomial a b d d u v w μ).eval w < 0 := by
    rw [eval_xSubQuarticCubic_at_w]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw_lt
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw_lt
    have hwd_pos : 0 < w - d := sub_pos.mpr hdw_lt
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have h123_pos : 0 < (w - a) * (w - b) * (w - d) :=
      mul_pos h12_pos hwd_pos
    have hquartic_pos : 0 < (w - a) * (w - b) * (w - d) * (w - d) :=
      mul_pos h123_pos hwd_pos
    exact mul_neg_of_neg_of_pos hw0_lt hquartic_pos
  by_cases hub_lt : u < b
  · have hP_u_pos :
        0 < (xSubQuarticCubicPolynomial a b d d u v w μ).eval u := by
      rw [eval_xSubQuarticCubic_at_u]
      have hua_pos : 0 < u - a := sub_pos.mpr hau_lt
      have hub_neg : u - b < 0 := sub_neg.mpr hub_lt
      have hud_neg : u - d < 0 := sub_neg.mpr hud_lt
      have h12_neg : (u - a) * (u - b) < 0 :=
        mul_neg_of_pos_of_neg hua_pos hub_neg
      have h123_pos : 0 < (u - a) * (u - b) * (u - d) :=
        mul_pos_of_neg_of_neg h12_neg hud_neg
      have hquartic_neg : (u - a) * (u - b) * (u - d) * (u - d) < 0 :=
        mul_neg_of_pos_of_neg h123_pos hud_neg
      exact mul_pos_of_neg_of_neg hu0_lt hquartic_neg
    have hP_b_neg :
        (xSubQuarticCubicPolynomial a b d d u v w μ).eval b < 0 := by
      rw [eval_xSubQuarticCubic_at_b]
      have hbu_pos : 0 < b - u := sub_pos.mpr hub_lt
      have hbv_neg : b - v < 0 := sub_neg.mpr hbv_lt
      have hbw_neg : b - w < 0 := sub_neg.mpr hbw_lt
      have h12_neg : (b - u) * (b - v) < 0 :=
        mul_neg_of_pos_of_neg hbu_pos hbv_neg
      have hG_pos : 0 < (b - u) * (b - v) * (b - w) :=
        mul_pos_of_neg_of_neg h12_neg hbw_neg
      nlinarith [mul_pos hμ hG_pos]
    exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
      huv hvw hw0 hμ (le_of_lt hau_lt) hub_lt hvd_lt hdw_lt
      hbv le_rfl hw0 (le_of_lt hP_a_pos)
      (mul_neg_of_pos_of_neg hP_u_pos hP_b_neg)
      (mul_neg_of_neg_of_pos hP_v_neg hP_d_pos)
      (mul_neg_of_pos_of_neg hP_d_pos hP_w_neg)
  · have hbu_lt : b < u :=
      lt_of_le_of_ne (le_of_not_gt hub_lt) (by intro h; exact hub_eq h.symm)
    have hP_b_pos :
        0 < (xSubQuarticCubicPolynomial a b d d u v w μ).eval b := by
      rw [eval_xSubQuarticCubic_at_b]
      have hbu_neg : b - u < 0 := sub_neg.mpr hbu_lt
      have hbv_neg : b - v < 0 := sub_neg.mpr hbv_lt
      have hbw_neg : b - w < 0 := sub_neg.mpr hbw_lt
      have h12_pos : 0 < (b - u) * (b - v) :=
        mul_pos_of_neg_of_neg hbu_neg hbv_neg
      have hG_neg : (b - u) * (b - v) * (b - w) < 0 :=
        mul_neg_of_pos_of_neg h12_pos hbw_neg
      nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
    have hP_u_neg :
        (xSubQuarticCubicPolynomial a b d d u v w μ).eval u < 0 := by
      rw [eval_xSubQuarticCubic_at_u]
      have hua_pos : 0 < u - a := sub_pos.mpr hau_lt
      have hub_pos : 0 < u - b := sub_pos.mpr hbu_lt
      have hud_neg : u - d < 0 := sub_neg.mpr hud_lt
      have h12_pos : 0 < (u - a) * (u - b) := mul_pos hua_pos hub_pos
      have h123_neg : (u - a) * (u - b) * (u - d) < 0 :=
        mul_neg_of_pos_of_neg h12_pos hud_neg
      have hquartic_pos : 0 < (u - a) * (u - b) * (u - d) * (u - d) :=
        mul_pos_of_neg_of_neg h123_neg hud_neg
      exact mul_neg_of_neg_of_pos hu0_lt hquartic_pos
    exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
      huv hvw hw0 hμ (le_of_lt hab) hbu_lt hvd_lt hdw_lt
      huv le_rfl hw0 (le_of_lt hP_a_pos)
      (mul_neg_of_pos_of_neg hP_b_pos hP_u_neg)
      (mul_neg_of_neg_of_pos hP_v_neg hP_d_pos)
      (mul_neg_of_pos_of_neg hP_d_pos hP_w_neg)

/-- Double-pair repeated-left-root boundary `a = b < c = d` for the normalized
quartic/cubic terminal. -/
lemma xSubQuarticCubicSplits_of_double_left_pair
    {a c u v w μ : ℝ} (hac : a < c)
    (huv : u ≤ v) (hvw : v ≤ w) (hau : a ≤ u) (huc : u ≤ c)
    (hvc : v ≤ c) (hcw : c ≤ w) (hc0 : c ≤ 0) (hw0 : w ≤ 0)
    (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a a c c u v w μ).Splits := by
  have hcommon_dispatch :
      (u = a ∨ u = a ∨ u = c ∨ v = a ∨ v = c ∨ v = c ∨
          w = c ∨ w = c) →
        (xSubQuarticCubicPolynomial a a c c u v w μ).Splits := by
    intro hcommon
    exact xSubQuarticCubicSplits_of_common_root_cases
      le_rfl (le_of_lt hac) le_rfl huv hvw hau (hau.trans huv) hcw
      huc hvc hc0 hw0 hμ hcommon
  by_cases hua_eq : u = a
  · exact hcommon_dispatch (by simp [hua_eq])
  by_cases huc_eq : u = c
  · exact hcommon_dispatch (by simp [huc_eq])
  by_cases hvc_eq : v = c
  · exact hcommon_dispatch (by simp [hvc_eq])
  by_cases hwc_eq : w = c
  · exact hcommon_dispatch (by simp [hwc_eq])
  by_cases hw_eq : w = 0
  · have hc_ne : c ≠ 0 := by
      intro hc_eq
      exact hwc_eq (by rw [hw_eq, hc_eq])
    exact xSubQuarticCubicRightOnlyEndpointZeroBoundaryCases
      le_rfl (le_of_lt hac) le_rfl huv hvw hau (hau.trans huv) hcw
      huc hvc hc0 hw0 hμ hw_eq hc_ne
  have hau_lt : a < u := lt_of_le_of_ne hau (by intro h; exact hua_eq h.symm)
  have hvc_lt : v < c := lt_of_le_of_ne hvc hvc_eq
  have huc_lt : u < c := lt_of_le_of_lt huv hvc_lt
  have hcw_lt : c < w :=
    lt_of_le_of_ne hcw (by intro h; exact hwc_eq h.symm)
  have hw0_lt : w < 0 := lt_of_le_of_ne hw0 hw_eq
  have hav_lt : a < v := lt_of_lt_of_le hau_lt huv
  have haw_lt : a < w := lt_trans hac hcw_lt
  have hu0_lt : u < 0 := lt_of_lt_of_le huc_lt hc0
  have hv0_lt : v < 0 := lt_of_lt_of_le hvc_lt hc0
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a a c c u v w μ).eval a := by
    rw [eval_xSubQuarticCubic_at_a]
    have hau_neg : a - u < 0 := sub_neg.mpr hau_lt
    have hav_neg : a - v < 0 := sub_neg.mpr hav_lt
    have haw_neg : a - w < 0 := sub_neg.mpr haw_lt
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_neg :
      (xSubQuarticCubicPolynomial a a c c u v w μ).eval u < 0 := by
    rw [eval_xSubQuarticCubic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau_lt
    have huc_neg : u - c < 0 := sub_neg.mpr huc_lt
    have hsq_left : 0 < (u - a) * (u - a) := mul_pos hua_pos hua_pos
    have hsq_right : 0 < (u - c) * (u - c) :=
      mul_pos_of_neg_of_neg huc_neg huc_neg
    have hquartic_pos : 0 < (u - a) * (u - a) * ((u - c) * (u - c)) :=
      mul_pos hsq_left hsq_right
    nlinarith [mul_neg_of_neg_of_pos hu0_lt hquartic_pos]
  have hP_v_neg :
      (xSubQuarticCubicPolynomial a a c c u v w μ).eval v < 0 := by
    rw [eval_xSubQuarticCubic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav_lt
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc_lt
    have hsq_left : 0 < (v - a) * (v - a) := mul_pos hva_pos hva_pos
    have hsq_right : 0 < (v - c) * (v - c) :=
      mul_pos_of_neg_of_neg hvc_neg hvc_neg
    have hquartic_pos : 0 < (v - a) * (v - a) * ((v - c) * (v - c)) :=
      mul_pos hsq_left hsq_right
    nlinarith [mul_neg_of_neg_of_pos hv0_lt hquartic_pos]
  have hP_c_pos :
      0 < (xSubQuarticCubicPolynomial a a c c u v w μ).eval c := by
    rw [eval_xSubQuarticCubic_at_c]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc_lt
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc_lt
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw_lt
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_neg : (c - u) * (c - v) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg :
      (xSubQuarticCubicPolynomial a a c c u v w μ).eval w < 0 := by
    rw [eval_xSubQuarticCubic_at_w]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw_lt
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw_lt
    have hsq_left : 0 < (w - a) * (w - a) := mul_pos hwa_pos hwa_pos
    have hsq_right : 0 < (w - c) * (w - c) := mul_pos hwc_pos hwc_pos
    have hquartic_pos : 0 < (w - a) * (w - a) * ((w - c) * (w - c)) :=
      mul_pos hsq_left hsq_right
    nlinarith [mul_neg_of_neg_of_pos hw0_lt hquartic_pos]
  exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
    huv hvw hw0 hμ le_rfl hau_lt hvc_lt hcw_lt huv le_rfl hw0
    (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
    (mul_neg_of_neg_of_pos hP_v_neg hP_c_pos)
    (mul_neg_of_pos_of_neg hP_c_pos hP_w_neg)

/-- The repeated-left-root quartic/cubic boundary package. -/
theorem xSubQuarticCubicRepeatedLeftBoundaryCases :
    xSubQuarticCubicRepeatedLeftBoundaryCasesStatement := by
  intro a b c d u v w μ hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ hrep
  by_cases hab_eq : a = b
  · subst b
    by_cases hac_eq : a = c
    · subst c
      have hua : u = a := le_antisymm huc hau
      subst u
      exact xSubQuarticCubicSplits_of_common_root_cases
        le_rfl le_rfl hcd huv hvw le_rfl hbv hcw le_rfl hvd hd0 hw0 hμ
        (by simp)
    · have hac : a < c := lt_of_le_of_ne hbc hac_eq
      by_cases hcd_eq : c = d
      · subst d
        exact xSubQuarticCubicSplits_of_double_left_pair
          hac huv hvw hau huc hvd hcw hd0 hw0 hμ
      · have hcd_lt : c < d := lt_of_le_of_ne hcd hcd_eq
        exact xSubQuarticCubicSplits_of_lower_left_repeated
          hac hcd_lt huv hvw hau hcw huc hvd hd0 hw0 hμ
  · have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
    by_cases hbc_eq : b = c
    · subst c
      by_cases hbd_eq : b = d
      · subst d
        have hvb : v = b := le_antisymm hvd hbv
        subst v
        exact xSubQuarticCubicSplits_of_common_root_cases
          (le_of_lt hab_lt) le_rfl le_rfl huv hvw hau le_rfl hcw huc le_rfl
          hd0 hw0 hμ (by simp)
      · have hbd_lt : b < d := lt_of_le_of_ne hcd hbd_eq
        exact xSubQuarticCubicSplits_of_middle_left_repeated
          hab_lt hbd_lt huv hvw hau huc hbv hcw hvd hd0 hw0 hμ
    · have hbc_lt : b < c := lt_of_le_of_ne hbc hbc_eq
      by_cases hcd_eq : c = d
      · subst d
        exact xSubQuarticCubicSplits_of_upper_left_repeated
          hab_lt hbc_lt huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      · rcases hrep with h | h | h
        · exact (hab_eq h).elim
        · exact (hbc_eq h).elim
        · exact (hcd_eq h).elim

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

/-- The repeated-right quartic/cubic boundary follows from the repeated-left
and endpoint-zero packages, because the remaining branch has strict left roots
and a strictly negative right endpoint. -/
theorem xSubQuarticCubicRepeatedRightBoundaryCases_of_left_endpoint_packages
    (hleft : xSubQuarticCubicRepeatedLeftBoundaryCasesStatement)
    (hend : xSubQuarticCubicEndpointZeroBoundaryCasesStatement) :
    xSubQuarticCubicRepeatedRightBoundaryCasesStatement := by
  intro a b c d u v w μ hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ h
  by_cases hab_eq : a = b
  · exact hleft hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inl hab_eq)
  by_cases hbc_eq : b = c
  · exact hleft hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inr (Or.inl hbc_eq))
  by_cases hcd_eq : c = d
  · exact hleft hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inr (Or.inr hcd_eq))
  by_cases hw_eq : w = 0
  · exact hend hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inr hw_eq)
  have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
  have hbc_lt : b < c := lt_of_le_of_ne hbc hbc_eq
  have hcd_lt : c < d := lt_of_le_of_ne hcd hcd_eq
  have hw0_lt : w < 0 := lt_of_le_of_ne hw0 hw_eq
  exact xSubQuarticCubicStrictLeftRepeatedRightBoundaryCases
    hab_lt hbc_lt hcd_lt huv hvw hau hbv hcw huc hvd hd0 hw0_lt hμ h

/-- The combined quartic/cubic side-boundary package follows from the three
independent repeated-left, repeated-right, and endpoint-zero subpackages. -/
theorem xSubQuarticCubicSideBoundaryCases_of_packages
    (hleft : xSubQuarticCubicRepeatedLeftBoundaryCasesStatement)
    (hright : xSubQuarticCubicRepeatedRightBoundaryCasesStatement)
    (hend : xSubQuarticCubicEndpointZeroBoundaryCasesStatement) :
    xSubQuarticCubicSideBoundaryCasesStatement := by
  intro a b c d u v w μ hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ h
  rcases h with hab_eq | hbc_eq | hcd_eq | huv_eq | hvw_eq | hd_eq | hw_eq
  · exact hleft hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inl hab_eq)
  · exact hleft hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inr (Or.inl hbc_eq))
  · exact hleft hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inr (Or.inr hcd_eq))
  · exact hright hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inl huv_eq)
  · exact hright hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inr hvw_eq)
  · exact hend hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inl hd_eq)
  · exact hend hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (Or.inr hw_eq)

/-- The full normalized quartic/cubic terminal follows once the same-side
repeated-root and endpoint-zero boundary package is proved.  Shared-root cases
are handled by `xSubQuarticCubicSplits_of_common_root_cases`; the remaining
strict case is `xSubQuarticCubicSplits_of_strict_side_roots`. -/
theorem xSubQuarticCubicSplits_of_side_boundary_cases
    (hboundary : xSubQuarticCubicSideBoundaryCasesStatement) :
    xSubQuarticCubicSplitsStatement := by
  intro a b c d u v w μ hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
  by_cases hua : u = a
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [hua])
  by_cases hub : u = b
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [hub])
  by_cases huc_eq : u = c
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [huc_eq])
  by_cases hvb : v = b
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [hvb])
  by_cases hvc : v = c
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [hvc])
  by_cases hvd_eq : v = d
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [hvd_eq])
  by_cases hwc : w = c
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [hwc])
  by_cases hwd : w = d
  · exact xSubQuarticCubicSplits_of_common_root_cases
      hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ (by simp [hwd])
  by_cases hab_eq : a = b
  · exact hboundary hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hab_eq])
  by_cases hbc_eq : b = c
  · exact hboundary hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hbc_eq])
  by_cases hcd_eq : c = d
  · exact hboundary hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hcd_eq])
  by_cases huv_eq : u = v
  · exact hboundary hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [huv_eq])
  by_cases hvw_eq : v = w
  · exact hboundary hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hvw_eq])
  by_cases hd_eq : d = 0
  · exact hboundary hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hd_eq])
  by_cases hw_eq : w = 0
  · exact hboundary hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ
      (by simp [hw_eq])
  have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
  have hbc_lt : b < c := lt_of_le_of_ne hbc hbc_eq
  have hcd_lt : c < d := lt_of_le_of_ne hcd hcd_eq
  have huv_lt : u < v := lt_of_le_of_ne huv huv_eq
  have hvw_lt : v < w := lt_of_le_of_ne hvw hvw_eq
  have hau_lt : a < u := lt_of_le_of_ne hau (by intro h; exact hua h.symm)
  have hbv_lt : b < v := lt_of_le_of_ne hbv (by intro h; exact hvb h.symm)
  have hcw_lt : c < w := lt_of_le_of_ne hcw (by intro h; exact hwc h.symm)
  have huc_lt : u < c := lt_of_le_of_ne huc huc_eq
  have hvd_lt : v < d := lt_of_le_of_ne hvd hvd_eq
  have hd0_lt : d < 0 := lt_of_le_of_ne hd0 hd_eq
  have hw0_lt : w < 0 := lt_of_le_of_ne hw0 hw_eq
  exact xSubQuarticCubicSplits_of_strict_side_roots
    hab_lt hbc_lt hcd_lt huv_lt hvw_lt hau_lt hbv_lt hcw_lt huc_lt hvd_lt
    hd0_lt hw0_lt hμ

/-- The full normalized quartic/cubic terminal follows from the three focused
boundary subpackages. -/
theorem xSubQuarticCubicSplits_of_boundary_packages
    (hleft : xSubQuarticCubicRepeatedLeftBoundaryCasesStatement)
    (hright : xSubQuarticCubicRepeatedRightBoundaryCasesStatement)
    (hend : xSubQuarticCubicEndpointZeroBoundaryCasesStatement) :
    xSubQuarticCubicSplitsStatement :=
  xSubQuarticCubicSplits_of_side_boundary_cases
    (xSubQuarticCubicSideBoundaryCases_of_packages hleft hright hend)

/-- The full normalized quartic/cubic terminal follows once the repeated-left
and endpoint-zero boundary packages are proved.  The repeated-right package is
derived from them using the strict-left repeated-right core. -/
theorem xSubQuarticCubicSplits_of_left_endpoint_boundary_packages
    (hleft : xSubQuarticCubicRepeatedLeftBoundaryCasesStatement)
    (hend : xSubQuarticCubicEndpointZeroBoundaryCasesStatement) :
    xSubQuarticCubicSplitsStatement :=
  xSubQuarticCubicSplits_of_boundary_packages hleft
    (xSubQuarticCubicRepeatedRightBoundaryCases_of_left_endpoint_packages
      hleft hend)
    hend

/-- The full normalized quartic/cubic terminal follows from the repeated-left
boundary package and the two disjoint single-endpoint zero packages. -/
theorem xSubQuarticCubicSplits_of_left_single_endpoint_boundary_packages
    (hleft : xSubQuarticCubicRepeatedLeftBoundaryCasesStatement)
    (hleftZero :
      xSubQuarticCubicLeftOnlyEndpointZeroBoundaryCasesStatement)
    (hrightZero :
      xSubQuarticCubicRightOnlyEndpointZeroBoundaryCasesStatement) :
    xSubQuarticCubicSplitsStatement :=
  xSubQuarticCubicSplits_of_left_endpoint_boundary_packages hleft
    (xSubQuarticCubicEndpointZeroBoundaryCases_of_single_endpoint_packages
      hleftZero hrightZero)

/-- The full normalized quartic/cubic terminal follows from repeated-left and
left-only endpoint packages, plus the quartic-minus-quadratic right endpoint
factor. -/
theorem xSubQuarticCubicSplits_of_left_endpoint_quarticSubQuadratic_packages
    (hleft : xSubQuarticCubicRepeatedLeftBoundaryCasesStatement)
    (hleftZero :
      xSubQuarticCubicLeftOnlyEndpointZeroBoundaryCasesStatement)
    (hquad : quarticSubQuadraticSplitsStatement) :
    xSubQuarticCubicSplitsStatement :=
  xSubQuarticCubicSplits_of_left_endpoint_boundary_packages hleft
    (xSubQuarticCubicEndpointZeroBoundaryCases_of_left_endpoint_quarticSubQuadratic
      hleftZero hquad)

/-- The full normalized quartic/cubic terminal now follows from the two
remaining left-boundary packages. -/
theorem xSubQuarticCubicSplits_of_remaining_left_boundary_packages
    (hleft : xSubQuarticCubicRepeatedLeftBoundaryCasesStatement)
    (hleftZero :
      xSubQuarticCubicLeftOnlyEndpointZeroBoundaryCasesStatement) :
    xSubQuarticCubicSplitsStatement :=
  xSubQuarticCubicSplits_of_left_endpoint_quarticSubQuadratic_packages hleft
    hleftZero quarticSubQuadraticSplits

/-- The normalized monic quartic/cubic x-subtraction leaf. -/
theorem xSubQuarticCubicSplits : xSubQuarticCubicSplitsStatement :=
  xSubQuarticCubicSplits_of_remaining_left_boundary_packages
    xSubQuarticCubicRepeatedLeftBoundaryCases
    xSubQuarticCubicLeftOnlyEndpointZeroBoundaryCases


end LiuOppositeSigns
end RealRooted
