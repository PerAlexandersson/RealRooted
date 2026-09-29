import RealRooted.LiuOppositeSigns.XSub.QuarticCubicBoundary.QuarticSubQuadratic

/-!
# Repeated-left quartic/cubic boundary

The repeated-left normalized quartic/cubic boundary package.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

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


end LiuOppositeSigns
end RealRooted
