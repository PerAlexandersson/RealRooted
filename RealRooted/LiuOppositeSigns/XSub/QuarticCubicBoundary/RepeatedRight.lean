import RealRooted.LiuOppositeSigns.XSub.QuarticCubicBoundary.Statements

/-!
# Repeated-right quartic/cubic boundary

Strict-left proofs for the repeated-right normalized quartic/cubic boundary.
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

/-- The strict-left repeated-right quartic/cubic boundary package. -/
theorem xSubQuarticCubicStrictLeftRepeatedRightBoundaryCases :
    xSubQuarticCubicStrictLeftRepeatedRightBoundaryCasesStatement := by
  intro a b c d u v w μ hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ h
  exact xSubQuarticCubicSplits_of_strict_left_repeated_right_boundary
    hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hμ h


end LiuOppositeSigns
end RealRooted
