import RealRooted.LiuOppositeSigns.XSub.CubicCubic.MiddleCases

/-!
# Cubic/cubic x-subtraction repeated right-endpoint cases.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`u < a < b < v = w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_u_a_b_v_v_c {a b c u v μ : ℝ}
    (hua : u < a) (hab : a < b) (hbv : b < v) (hvc : v < c)
    (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C v))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C v))
  have hac : a < c := lt_trans hab (lt_trans hbv hvc)
  have hav : a < v := lt_trans hab hbv
  have huc : u < c := lt_trans hua hac
  have ha0 : a < 0 := lt_of_lt_of_le hac hc0
  have hu0 : u < 0 := lt_trans hua ha0
  have hv0 : v < 0 := lt_of_lt_of_le hvc hc0
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr (lt_trans hua hab)
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
    have hsq_pos : 0 < (a - v) * (a - v) :=
      mul_pos_of_neg_of_neg hav_neg hav_neg
    have hG_pos : 0 < (a - u) * ((a - v) * (a - v)) :=
      mul_pos hau_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr (lt_trans hua hab)
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hsq_pos : 0 < (b - v) * (b - v) :=
      mul_pos_of_neg_of_neg hbv_neg hbv_neg
    have hG_pos : 0 < (b - u) * ((b - v) * (b - v)) :=
      mul_pos hbu_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    have hleft_pos : 0 < v * ((v - a) * (v - b) * (v - c)) :=
      mul_pos_of_neg_of_neg hv0 hprod_neg
    nlinarith
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hsq_pos : 0 < (c - v) * (c - v) := mul_pos hcv_pos hcv_pos
    have hG_pos : 0 < (c - u) * ((c - v) * (c - v)) :=
      mul_pos hcu_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have hsq_pos : 0 < (0 - v) * (0 - v) := mul_pos h0v_pos h0v_pos
    have hG_pos : 0 < (0 - u) * ((0 - v) * (0 - v)) :=
      mul_pos h0u_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u v v μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u v v μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hua hbv hvc (le_of_lt hab) (le_refl v) hc0
      (mul_neg_of_pos_of_neg hP_u_pos hP_a_neg)
      (mul_neg_of_neg_of_pos hP_b_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_v_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict boundary subcase of the normalized cubic/cubic leaf with order
`a < u < b < v = w < c < 0`. -/
lemma xSubCubicCubicSplits_of_order_a_u_b_v_v_c {a b c u v μ : ℝ}
    (hau : a < u) (hub : u < b) (hbv : b < v) (hvc : v < c)
    (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C v))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C v))
  have hab : a < b := lt_trans hau hub
  have hav : a < v := lt_trans hab hbv
  have huc : u < c := lt_trans hub (lt_trans hbv hvc)
  have hbc : b < c := lt_trans hbv hvc
  have hb0 : b < 0 := lt_of_lt_of_le hbc hc0
  have hu0 : u < 0 := lt_trans hub hb0
  have hv0 : v < 0 := lt_of_lt_of_le hvc hc0
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have hsq_pos : 0 < (a - v) * (a - v) :=
      mul_pos_of_neg_of_neg hav_neg hav_neg
    have hG_neg : (a - u) * ((a - v) * (a - v)) < 0 :=
      mul_neg_of_neg_of_pos hau_neg hsq_pos
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
    have hsq_pos : 0 < (b - v) * (b - v) :=
      mul_pos_of_neg_of_neg hbv_neg hbv_neg
    have hG_pos : 0 < (b - u) * ((b - v) * (b - v)) :=
      mul_pos hbu_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    have hleft_pos : 0 < v * ((v - a) * (v - b) * (v - c)) :=
      mul_pos_of_neg_of_neg hv0 hprod_neg
    nlinarith
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hsq_pos : 0 < (c - v) * (c - v) := mul_pos hcv_pos hcv_pos
    have hG_pos : 0 < (c - u) * ((c - v) * (c - v)) :=
      mul_pos hcu_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicCubic]
    have h0u_pos : 0 < 0 - u := sub_pos.mpr hu0
    have h0v_pos : 0 < 0 - v := sub_pos.mpr hv0
    have hsq_pos : 0 < (0 - v) * (0 - v) := mul_pos h0v_pos h0v_pos
    have hG_pos : 0 < (0 - u) * ((0 - v) * (0 - v)) :=
      mul_pos h0u_pos hsq_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicCubic_ne_zero a b c u v v μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicCubic_atTop_atTop a b c u v v μ
  have hsplits :=
    splits_of_three_sign_change_intervals_and_right_tail_of_le
      hP_ne hdeg_le hau hbv hvc (le_of_lt hub) (le_refl v) hc0
      (mul_neg_of_pos_of_neg hP_a_pos hP_u_neg)
      (mul_neg_of_neg_of_pos hP_b_neg hP_v_pos)
      (mul_neg_of_pos_of_neg hP_v_pos hP_c_neg)
      hP_zero_neg ht_top
  simpa [P] using hsplits

/-- Strict-left-root boundary package for the repeated upper right root
`v = w`.  Endpoint coincidences reduce to common-root quadratic/quadratic
endpoints; the remaining two orders use adjacent sign-change intervals. -/
lemma xSubCubicCubicSplits_of_upper_right_double_root {a b c u v μ : ℝ}
    (hab : a < b) (hbc : b < c) (huv : u < v) (hub : u ≤ b)
    (hvc : v ≤ c) (hav : a ≤ v) (hbv : b ≤ v)
    (hc0 : c ≤ 0) (hv0 : v < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C v))).Splits := by
  by_cases hvb_eq : v = b
  · subst v
    exact xSubCubicCubicSplits_of_middle_common_root
      (le_of_lt hab) (le_of_lt hbc) hub (le_refl b)
      hc0 (le_of_lt hv0) hμ
  by_cases hvc_eq : v = c
  · subst v
    have hac : a ≤ c := (le_of_lt hab).trans (le_of_lt hbc)
    exact xSubCubicCubicSplits_of_upper_common_root
      (le_of_lt hab) (le_of_lt hbc) (le_of_lt huv) hub hac (le_refl c) hc0 hμ
  have hbv_lt : b < v :=
    lt_of_le_of_ne hbv (by intro h; exact hvb_eq h.symm)
  have hvc_lt : v < c := lt_of_le_of_ne hvc hvc_eq
  by_cases hua : u < a
  · exact xSubCubicCubicSplits_of_order_u_a_b_v_v_c
      hua hab hbv_lt hvc_lt hc0 hμ
  by_cases hua_eq : u = a
  · subst u
    exact xSubCubicCubicSplits_of_lower_common_root
      (le_of_lt hbc) (le_refl v) hvc hbv hc0 (le_of_lt hv0) hμ
  by_cases hub_eq : u = b
  · subst u
    have hac : a ≤ c := (le_of_lt hab).trans (le_of_lt hbc)
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := b) (a := a) (b := c) (c := v) (d := v)
      hac (le_refl v) hav hvc hc0 (le_of_lt hv0) hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  have hau : a < u :=
    lt_of_le_of_ne (le_of_not_gt hua) (by intro h; exact hua_eq h.symm)
  have hub_lt : u < b := lt_of_le_of_ne hub hub_eq
  exact xSubCubicCubicSplits_of_order_a_u_b_v_v_c
    hau hub_lt hbv_lt hvc_lt hc0 hμ

/-- Dispatcher for the strict cubic/cubic subcases where the lower right root
lies strictly between the lower and middle left roots.  The ordinary branch is
closed by Ma--Wang interlacing; the other three branches are the strict
nonordinary sign-change lemmas. -/
lemma xSubCubicCubicSplits_of_left_root_right_strict_distinct {a b c u v w μ : ℝ}
    (hab : a < b) (hbc : b < c) (hau : a < u) (hub : u < b)
    (huv : u < v) (hvw : v < w) (hvc : v < c) (hbw : b < w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hvb_ne : v ≠ b) (hwc_ne : w ≠ c)
    (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  rcases lt_or_gt_of_ne hvb_ne with hvb | hbv
  · rcases lt_or_gt_of_ne hwc_ne with hwc | hcw
    · exact xSubCubicCubicSplits_of_order_a_u_v_b_w_c
        hau huv hvb hbw hwc hc0 hμ
    · exact xSubCubicCubicSplits_of_order_a_u_v_b_c_w
        hau huv hvb hbc hcw hw0 hμ
  · rcases lt_or_gt_of_ne hwc_ne with hwc | hcw
    · exact xSubCubicCubicSplits_of_order_a_u_b_v_w_c
        hau hub hbv hvw hwc hc0 hμ
    · exact xSubCubicCubicSplits_of_interlacing_roots
        (le_of_lt hab) (le_of_lt hbc) hc0
        (le_of_lt huv) (le_of_lt hvw) (le_of_lt hau) (le_of_lt hub)
        (le_of_lt hbv) (le_of_lt hvc) (le_of_lt hcw) (le_of_lt hw0) hμ

/-- Dispatcher for the strict cubic/cubic subcases where the lower right root
lies weakly between the lower and middle left roots.  Boundary equalities reduce
to common-root quadratic/quadratic endpoints; the remaining case is the strict
dispatcher. -/
lemma xSubCubicCubicSplits_of_left_root_right_strict_roots {a b c u v w μ : ℝ}
    (hab : a < b) (hbc : b < c) (hau : a < u) (hub : u ≤ b)
    (huv : u < v) (hvw : v < w) (hvc : v ≤ c) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases hub_eq : u = b
  · subst u
    have hac : a ≤ c := (le_of_lt hab).trans (le_of_lt hbc)
    have haw : a ≤ w := (le_of_lt hab).trans hbw
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := b) (a := a) (b := c) (c := v) (d := w)
      hac (le_of_lt hvw) haw hvc hc0 (le_of_lt hw0) hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hvb : v = b
  · subst v
    exact xSubCubicCubicSplits_of_middle_common_root
      (le_of_lt hab) (le_of_lt hbc) hub hbw hc0 (le_of_lt hw0) hμ
  by_cases hvc_eq : v = c
  · subst v
    have huw : u ≤ w := (le_of_lt huv).trans (le_of_lt hvw)
    have haw : a ≤ w := (le_of_lt hab).trans hbw
    have hb0 : b ≤ 0 := (le_of_lt hbc).trans hc0
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := c) (a := a) (b := b) (c := u) (d := w)
      (le_of_lt hab) huw haw hub hb0 (le_of_lt hw0) hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hwb : w = b
  · subst w
    have hac : a ≤ c := (le_of_lt hab).trans (le_of_lt hbc)
    have hav : a ≤ v := (le_of_lt hau).trans (le_of_lt huv)
    have huc : u ≤ c := hub.trans (le_of_lt hbc)
    have hv0 : v ≤ 0 := hvc.trans hc0
    have hcommon := xSubCubicCubicSplits_of_common_root
      (r := b) (a := a) (b := c) (c := u) (d := v)
      hac (le_of_lt huv) hav huc hc0 hv0 hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon
  by_cases hwc : w = c
  · subst w
    have hav : a ≤ v := (le_of_lt hau).trans (le_of_lt huv)
    exact xSubCubicCubicSplits_of_upper_common_root
      (le_of_lt hab) (le_of_lt hbc) (le_of_lt huv) hub hav hvc
      hc0 hμ
  have hub_lt : u < b := lt_of_le_of_ne hub hub_eq
  have hvc_lt : v < c := lt_of_le_of_ne hvc hvc_eq
  have hbw_lt : b < w := by exact lt_of_le_of_ne hbw (by intro h; exact hwb h.symm)
  exact xSubCubicCubicSplits_of_left_root_right_strict_distinct
    hab hbc hau hub_lt huv hvw hvc_lt hbw_lt hc0 hw0 hvb hwc hμ

/-- Strict-root dispatcher for the normalized cubic/cubic leaf with negative
upper endpoints.  It splits on the lower right root relative to the lower left
root and reuses the two strict packages plus the common-root boundary. -/
lemma xSubCubicCubicSplits_of_strict_roots {a b c u v w μ : ℝ}
    (hab : a < b) (hbc : b < c) (huv : u < v) (hvw : v < w)
    (hub : u ≤ b) (hvc : v ≤ c) (hav : a ≤ v) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases hua : u < a
  · exact xSubCubicCubicSplits_of_left_root_left_strict_roots
      hua hab hbc hav hvc hvw hbw hc0 hw0 hμ
  by_cases hua_eq : u = a
  · subst u
    exact xSubCubicCubicSplits_of_lower_common_root
      (le_of_lt hbc) (le_of_lt hvw) hvc hbw hc0 (le_of_lt hw0) hμ
  have hau : a < u := by exact lt_of_le_of_ne (le_of_not_gt hua) (by intro h; exact hua_eq h.symm)
  exact xSubCubicCubicSplits_of_left_root_right_strict_roots
    hab hbc hau hub huv hvw hvc hbw hc0 hw0 hμ

/-- Strict-left-root dispatcher for the normalized cubic/cubic leaf with a weak
lower-right-root inequality.  The boundary `u = v` is the repeated lower
right-root package; the strict case reuses `xSubCubicCubicSplits_of_strict_roots`.
-/
lemma xSubCubicCubicSplits_of_strict_left_roots_right_upper_strict
    {a b c u v w μ : ℝ}
    (hab : a < b) (hbc : b < c) (huv : u ≤ v) (hvw : v < w)
    (hub : u ≤ b) (hvc : v ≤ c) (hav : a ≤ v) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases huv_eq : u = v
  · subst v
    by_cases hua : u = a
    · subst u
      exact xSubCubicCubicSplits_of_lower_common_root
        (le_of_lt hbc) (le_of_lt hvw) hvc hbw hc0 (le_of_lt hw0) hμ
    by_cases hub_eq : u = b
    · subst u
      exact xSubCubicCubicSplits_of_middle_common_root
        (le_of_lt hab) (le_of_lt hbc) (le_refl b) hbw
        hc0 (le_of_lt hw0) hμ
    have hau : a < u := lt_of_le_of_ne hav (by intro h; exact hua h.symm)
    have hub_lt : u < b := lt_of_le_of_ne hub hub_eq
    exact xSubCubicCubicSplits_of_lower_right_double_root
      hab hbc hau hub_lt hbw hc0 hw0 hμ
  · have huv_lt : u < v := lt_of_le_of_ne huv huv_eq
    exact xSubCubicCubicSplits_of_strict_roots
      hab hbc huv_lt hvw hub hvc hav hbw hc0 hw0 hμ

/-- Normalized cubic/cubic leaf with strict left roots, weak right-root order,
and strictly negative upper endpoints.  The `v = w` boundary is the repeated
upper right-root package; the strict `v < w` case reuses the previous wrapper.
-/
lemma xSubCubicCubicSplits_of_strict_left_roots {a b c u v w μ : ℝ}
    (hab : a < b) (hbc : b < c) (huv : u ≤ v) (hvw : v ≤ w)
    (hub : u ≤ b) (hvc : v ≤ c) (hav : a ≤ v) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  by_cases hvw_eq : v = w
  · subst w
    by_cases huv_eq : u = v
    · subst v
      have hub_eq : u = b := le_antisymm hub hbw
      subst u
      exact xSubCubicCubicSplits_of_middle_common_root
        (le_of_lt hab) (le_of_lt hbc) (le_refl b) (le_refl b)
        hc0 (le_of_lt hw0) hμ
    · have huv_lt : u < v := lt_of_le_of_ne huv huv_eq
      exact xSubCubicCubicSplits_of_upper_right_double_root
        hab hbc huv_lt hub hvc hav hbw hc0 hw0 hμ
  · have hvw_lt : v < w := lt_of_le_of_ne hvw hvw_eq
    exact xSubCubicCubicSplits_of_strict_left_roots_right_upper_strict
      hab hbc huv hvw_lt hub hvc hav hbw hc0 hw0 hμ
end LiuOppositeSigns
end RealRooted
