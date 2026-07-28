import RealRooted.LiuOppositeSigns.XSub.SplittingTools

/-!
# Liu quartic/cubic x-subtraction strict core

This module contains the normalized quartic/cubic x-subtraction polynomial and
strict-root splitting cases used by the left-successor right-degree-three leaf.
Boundary and positive-split wrapper packages live downstream.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- The normalized quartic/cubic x-subtraction polynomial. -/
noncomputable def xSubQuarticCubicPolynomial (a b c d u v w μ : ℝ) : ℝ[X] :=
  X * ((X - C a) * (X - C b) * (X - C c) * (X - C d)) -
    C μ * ((X - C u) * (X - C v) * (X - C w))

/-- Normalized monic arithmetic leaf for the degree-four/degree-three
left-successor positive-split x-subtraction endpoint.  This is the remaining
terminal needed for the two-degree Liu factor-return branch through endpoint
degree three. -/
def xSubQuarticCubicSplitsStatement : Prop :=
  ∀ {a b c d u v w μ : ℝ},
    a ≤ b → b ≤ c → c ≤ d → u ≤ v → v ≤ w →
      a ≤ u → b ≤ v → c ≤ w → u ≤ c → v ≤ d →
        d ≤ 0 → w ≤ 0 → 0 < μ →
          (xSubQuarticCubicPolynomial a b c d u v w μ).Splits

/-- The normalized quartic/cubic x-subtraction polynomial is a genuine
quintic. -/
lemma natDegree_xSubQuarticCubic (a b c d u v w μ : ℝ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).natDegree = 5 := by
  unfold xSubQuarticCubicPolynomial
  compute_degree <;> norm_num

/-- The normalized quartic/cubic x-subtraction polynomial is nonzero. -/
lemma xSubQuarticCubic_ne_zero (a b c d u v w μ : ℝ) :
    xSubQuarticCubicPolynomial a b c d u v w μ ≠ 0 := by
  intro hzero
  have hdeg := natDegree_xSubQuarticCubic a b c d u v w μ
  rw [hzero] at hdeg
  norm_num at hdeg

/-- The normalized quartic/cubic x-subtraction polynomial has positive leading
coefficient. -/
lemma hasPosLeadingCoeff_xSubQuarticCubic (a b c d u v w μ : ℝ) :
    HasPosLeadingCoeff
      (xSubQuarticCubicPolynomial a b c d u v w μ) := by
  unfold xSubQuarticCubicPolynomial
  have hquartic_pos :
      HasPosLeadingCoeff ((X - C a) * (X - C b) * (X - C c) * (X - C d)) := by
    exact (((hasPosLeadingCoeff_X_sub_C a).mul
      (hasPosLeadingCoeff_X_sub_C b)).mul
      (hasPosLeadingCoeff_X_sub_C c)).mul
      (hasPosLeadingCoeff_X_sub_C d)
  have hleft_pos :
      HasPosLeadingCoeff
        (X * ((X - C a) * (X - C b) * (X - C c) * (X - C d))) :=
    hquartic_pos.X_mul
  have hleft_deg :
      (X * ((X - C a) * (X - C b) * (X - C c) * (X - C d))).natDegree = 5 := by
    compute_degree <;> norm_num
  have hdeg_lt : (C μ * ((X - C u) * (X - C v) * (X - C w))).natDegree <
      (X * ((X - C a) * (X - C b) * (X - C c) * (X - C d))).natDegree := by
    rw [hleft_deg]
    compute_degree
    norm_num
  unfold HasPosLeadingCoeff at hleft_pos ⊢
  have hdegree_lt : degree (C μ * ((X - C u) * (X - C v) * (X - C w))) <
      degree (X * ((X - C a) * (X - C b) * (X - C c) * (X - C d))) :=
    degree_lt_degree hdeg_lt
  rw [leadingCoeff_sub_of_degree_lt hdegree_lt]
  exact hleft_pos

/-- Evaluation form of the normalized quartic/cubic x-subtraction leaf. -/
lemma eval_xSubQuarticCubic (a b c d u v w μ x : ℝ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).eval x =
      x * ((x - a) * (x - b) * (x - c) * (x - d)) -
        μ * ((x - u) * (x - v) * (x - w)) := by
  unfold xSubQuarticCubicPolynomial
  simp only [eval_sub, eval_mul, eval_X, eval_C]

/-- Evaluation at the first left root of the normalized quartic/cubic
x-subtraction polynomial. -/
lemma eval_xSubQuarticCubic_at_a (a b c d u v w μ : ℝ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).eval a =
      -μ * ((a - u) * (a - v) * (a - w)) := by
  rw [eval_xSubQuarticCubic]
  ring

/-- Evaluation at the second left root of the normalized quartic/cubic
x-subtraction polynomial. -/
lemma eval_xSubQuarticCubic_at_b (a b c d u v w μ : ℝ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).eval b =
      -μ * ((b - u) * (b - v) * (b - w)) := by
  rw [eval_xSubQuarticCubic]
  ring

/-- Evaluation at the third left root of the normalized quartic/cubic
x-subtraction polynomial. -/
lemma eval_xSubQuarticCubic_at_c (a b c d u v w μ : ℝ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).eval c =
      -μ * ((c - u) * (c - v) * (c - w)) := by
  rw [eval_xSubQuarticCubic]
  ring

/-- Evaluation at the fourth left root of the normalized quartic/cubic
x-subtraction polynomial. -/
lemma eval_xSubQuarticCubic_at_d (a b c d u v w μ : ℝ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).eval d =
      -μ * ((d - u) * (d - v) * (d - w)) := by
  rw [eval_xSubQuarticCubic]
  ring

/-- Evaluation at the first right root of the normalized quartic/cubic
x-subtraction polynomial. -/
lemma eval_xSubQuarticCubic_at_u (a b c d u v w μ : ℝ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).eval u =
      u * ((u - a) * (u - b) * (u - c) * (u - d)) := by
  rw [eval_xSubQuarticCubic]
  ring

/-- Evaluation at the second right root of the normalized quartic/cubic
x-subtraction polynomial. -/
lemma eval_xSubQuarticCubic_at_v (a b c d u v w μ : ℝ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).eval v =
      v * ((v - a) * (v - b) * (v - c) * (v - d)) := by
  rw [eval_xSubQuarticCubic]
  ring

/-- Evaluation at the third right root of the normalized quartic/cubic
x-subtraction polynomial. -/
lemma eval_xSubQuarticCubic_at_w (a b c d u v w μ : ℝ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).eval w =
      w * ((w - a) * (w - b) * (w - c) * (w - d)) := by
  rw [eval_xSubQuarticCubic]
  ring

/-- The origin gives a nonpositive value for the normalized quartic/cubic
x-subtraction pencil. -/
lemma eval_xSubQuarticCubic_at_zero_nonpos {a b c d u v w μ : ℝ}
    (huv : u ≤ v) (hvw : v ≤ w) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).eval 0 ≤ 0 := by
  rw [eval_xSubQuarticCubic]
  have hu0 : u ≤ 0 := huv.trans (hvw.trans hw0)
  have hv0 : v ≤ 0 := hvw.trans hw0
  have h0u : 0 ≤ 0 - u := sub_nonneg.mpr hu0
  have h0v : 0 ≤ 0 - v := sub_nonneg.mpr hv0
  have h0w : 0 ≤ 0 - w := sub_nonneg.mpr hw0
  have hG_nonneg : 0 ≤ (0 - u) * (0 - v) * (0 - w) :=
    mul_nonneg (mul_nonneg h0u h0v) h0w
  nlinarith [mul_nonneg (le_of_lt hμ) hG_nonneg]

/-- The normalized quartic/cubic x-subtraction polynomial tends to `-∞` at
`-∞`. -/
lemma tendsto_eval_xSubQuarticCubic_atBot_atBot (a b c d u v w μ : ℝ) :
    Tendsto
      (fun x => (xSubQuarticCubicPolynomial a b c d u v w μ).eval x)
      atBot atBot := by
  let P : ℝ[X] := xSubQuarticCubicPolynomial a b c d u v w μ
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubQuarticCubic a b c d u v w μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      dsimp [P]
      rw [natDegree_xSubQuarticCubic]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  have hP_odd : Odd P.natDegree := by
    dsimp [P]
    rw [natDegree_xSubQuarticCubic]
    norm_num
  exact tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hP_pos hP_deg_pos hP_odd

/-- The normalized quartic/cubic x-subtraction polynomial tends to `+∞` at
`+∞`. -/
lemma tendsto_eval_xSubQuarticCubic_atTop_atTop (a b c d u v w μ : ℝ) :
    Tendsto
      (fun x => (xSubQuarticCubicPolynomial a b c d u v w μ).eval x)
      atTop atTop := by
  let P : ℝ[X] := xSubQuarticCubicPolynomial a b c d u v w μ
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubQuarticCubic a b c d u v w μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      dsimp [P]
      rw [natDegree_xSubQuarticCubic]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  exact P.tendsto_atTop_of_leadingCoeff_nonneg hP_deg_pos hP_pos.le

/-- A quartic/cubic normalized x-subtraction polynomial splits once four
sign-changing intervals are ordered before `0`. -/
lemma xSubQuarticCubicSplits_of_four_sign_change_intervals_and_zero_tail
    {a b c d u v w μ x₁ x₂ y₁ y₂ z₁ z₂ t₁ t₂ : ℝ}
    (huv : u ≤ v) (hvw : v ≤ w) (hw0 : w ≤ 0) (hμ : 0 < μ)
    (hx : x₁ < x₂) (hy : y₁ < y₂) (hz : z₁ < z₂) (ht : t₁ < t₂)
    (hxy : x₂ ≤ y₁) (hyz : y₂ ≤ z₁) (hzt : z₂ ≤ t₁) (ht0 : t₂ ≤ 0)
    (hsx :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval x₁ *
        (xSubQuarticCubicPolynomial a b c d u v w μ).eval x₂ < 0)
    (hsy :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval y₁ *
        (xSubQuarticCubicPolynomial a b c d u v w μ).eval y₂ < 0)
    (hsz :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval z₁ *
        (xSubQuarticCubicPolynomial a b c d u v w μ).eval z₂ < 0)
    (hst :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval t₁ *
        (xSubQuarticCubicPolynomial a b c d u v w μ).eval t₂ < 0) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  let P : ℝ[X] := xSubQuarticCubicPolynomial a b c d u v w μ
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubQuarticCubic_ne_zero a b c d u v w μ
  have hdeg_le : P.natDegree ≤ 5 := by
    dsimp [P]
    rw [natDegree_xSubQuarticCubic]
  have hzero : P.eval 0 ≤ 0 := by
    dsimp [P]
    exact eval_xSubQuarticCubic_at_zero_nonpos huv hvw hw0 hμ
  have htop : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubQuarticCubic_atTop_atTop a b c d u v w μ
  have hsplits := splits_of_four_sign_change_intervals_and_right_tail_of_le
    hP_ne hdeg_le hx hy hz ht hxy hyz hzt ht0 hsx hsy hsz hst hzero htop
  simpa [P] using hsplits

/-- A quartic/cubic normalized x-subtraction polynomial splits once three
sign-changing intervals sit between a left-tail value and the zero tail. -/
lemma xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
    {a b c d u v w μ l x₁ x₂ y₁ y₂ z₁ z₂ : ℝ}
    (huv : u ≤ v) (hvw : v ≤ w) (hw0 : w ≤ 0) (hμ : 0 < μ)
    (hlx : l ≤ x₁) (hx : x₁ < x₂) (hy : y₁ < y₂) (hz : z₁ < z₂)
    (hxy : x₂ ≤ y₁) (hyz : y₂ ≤ z₁) (hz0 : z₂ ≤ 0)
    (hl_eval : 0 ≤ (xSubQuarticCubicPolynomial a b c d u v w μ).eval l)
    (hsx :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval x₁ *
        (xSubQuarticCubicPolynomial a b c d u v w μ).eval x₂ < 0)
    (hsy :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval y₁ *
        (xSubQuarticCubicPolynomial a b c d u v w μ).eval y₂ < 0)
    (hsz :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval z₁ *
        (xSubQuarticCubicPolynomial a b c d u v w μ).eval z₂ < 0) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  have hdeg_le : (xSubQuarticCubicPolynomial a b c d u v w μ).natDegree ≤ 5 := by
    rw [natDegree_xSubQuarticCubic]
  have hzero : (xSubQuarticCubicPolynomial a b c d u v w μ).eval 0 ≤ 0 :=
    eval_xSubQuarticCubic_at_zero_nonpos huv hvw hw0 hμ
  exact splits_of_three_sign_change_intervals_and_both_tails_of_le
    (xSubQuarticCubic_ne_zero a b c d u v w μ) hdeg_le hlx hx hy hz hxy hyz hz0
    hl_eval hsx hsy hsz hzero
    (tendsto_eval_xSubQuarticCubic_atBot_atBot a b c d u v w μ)
    (tendsto_eval_xSubQuarticCubic_atTop_atTop a b c d u v w μ)

/-- Strict ordinary interleaving order `a < u < b < v < c < w < d < 0` for
the normalized quartic/cubic terminal. -/
lemma xSubQuarticCubicSplits_of_order_a_u_b_v_c_w_d
    {a b c d u v w μ : ℝ} (hau : a < u) (hub : u < b)
    (hbv : b < v) (hvc : v < c) (hcw : c < w) (hwd : w < d)
    (hd0 : d < 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  let P : ℝ[X] := xSubQuarticCubicPolynomial a b c d u v w μ
  have hav : a < v := lt_trans hau (lt_trans hub hbv)
  have hac : a < c := lt_trans hav hvc
  have haw : a < w := lt_trans hac hcw
  have hbw : b < w := lt_trans hbv (lt_trans hvc hcw)
  have hbd : b < d := lt_trans hbw hwd
  have hud : u < d := lt_trans hub hbd
  have huv : u < v := lt_trans hub hbv
  have huc : u < c := lt_trans huv hvc
  have hvw : v < w := lt_trans hvc hcw
  have hvd : v < d := lt_trans hvw hwd
  have hu0 : u < 0 := lt_trans hud hd0
  have hv0 : v < 0 := lt_trans hvd hd0
  have hw0 : w < 0 := lt_trans hwd hd0
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hud_neg : u - d < 0 := sub_neg.mpr hud
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have h123_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) * (u - d) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hud_neg
    have hF_pos :
        0 < u * ((u - a) * (u - b) * (u - c) * (u - d)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg hbu_pos hbv_neg
    have hG_pos : 0 < (b - u) * (b - v) * (b - w) :=
      mul_pos_of_neg_of_neg h12_neg hbw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) * (v - d) :=
      mul_pos_of_neg_of_neg h123_neg hvd_neg
    have hF_neg :
        v * ((v - a) * (v - b) * (v - c) * (v - d)) < 0 :=
      mul_neg_of_neg_of_pos hv0 hprod_pos
    nlinarith
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_neg : (c - u) * (c - v) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_pos : 0 < P.eval w := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hwd_neg : w - d < 0 := sub_neg.mpr hwd
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have h123_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos h12_pos hwc_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) * (w - d) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hwd_neg
    have hF_pos :
        0 < w * ((w - a) * (w - b) * (w - c) * (w - d)) :=
      mul_pos_of_neg_of_neg hw0 hprod_neg
    nlinarith
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hdu_pos : 0 < d - u := sub_pos.mpr hud
    have hdv_pos : 0 < d - v := sub_pos.mpr hvd
    have hdw_pos : 0 < d - w := sub_pos.mpr hwd
    have h12_pos : 0 < (d - u) * (d - v) := mul_pos hdu_pos hdv_pos
    have hG_pos : 0 < (d - u) * (d - v) * (d - w) :=
      mul_pos h12_pos hdw_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubQuarticCubic_ne_zero a b c d u v w μ
  have hdeg_le : P.natDegree ≤ 5 := by
    dsimp [P]
    rw [natDegree_xSubQuarticCubic]
  have ht_bot : Tendsto (fun x => P.eval x) atBot atBot := by
    dsimp [P]
    exact tendsto_eval_xSubQuarticCubic_atBot_atBot a b c d u v w μ
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubQuarticCubic_atTop_atTop a b c d u v w μ
  have hP_zero_nonpos : P.eval 0 ≤ 0 := by
    dsimp [P]
    exact eval_xSubQuarticCubic_at_zero_nonpos (le_of_lt huv)
      (le_of_lt hvw) (le_of_lt hw0) hμ
  have hsplits := splits_of_three_sign_change_intervals_and_both_tails_of_le
    hP_ne hdeg_le (le_of_lt hau) hub hvc hwd (le_of_lt hbv)
    (le_of_lt hcw) (le_of_lt hd0) (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_u_pos hP_b_neg)
    (mul_neg_of_neg_of_pos hP_v_neg hP_c_pos)
    (mul_neg_of_pos_of_neg hP_w_pos hP_d_neg)
    hP_zero_nonpos ht_bot ht_top
  simpa [P] using hsplits

/-- Strict ordinary order `a < u < b < v < c < d < w < 0` for the normalized
quartic/cubic terminal. -/
lemma xSubQuarticCubicSplits_of_order_a_u_b_v_c_d_w
    {a b c d u v w μ : ℝ} (hau : a < u) (hub : u < b)
    (hbv : b < v) (hvc : v < c) (hcd : c < d) (hdw : d < w)
    (hw0 : w < 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  let P : ℝ[X] := xSubQuarticCubicPolynomial a b c d u v w μ
  have hav : a < v := lt_trans hau (lt_trans hub hbv)
  have hac : a < c := lt_trans hav hvc
  have had : a < d := lt_trans hac hcd
  have haw : a < w := lt_trans had hdw
  have hbd : b < d := lt_trans hbv (lt_trans hvc hcd)
  have hbw : b < w := lt_trans hbd hdw
  have hcw : c < w := lt_trans hcd hdw
  have hud : u < d := lt_trans hub hbd
  have huv : u < v := lt_trans hub hbv
  have huc : u < c := lt_trans huv hvc
  have hvd : v < d := lt_trans hvc hcd
  have hvw : v < w := lt_trans hvd hdw
  have hd0 : d < 0 := lt_trans hdw hw0
  have hu0 : u < 0 := lt_trans hud hd0
  have hv0 : v < 0 := lt_trans hvd hd0
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hud_neg : u - d < 0 := sub_neg.mpr hud
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have h123_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) * (u - d) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hud_neg
    have hF_pos :
        0 < u * ((u - a) * (u - b) * (u - c) * (u - d)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg hbu_pos hbv_neg
    have hG_pos : 0 < (b - u) * (b - v) * (b - w) :=
      mul_pos_of_neg_of_neg h12_neg hbw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) * (v - d) :=
      mul_pos_of_neg_of_neg h123_neg hvd_neg
    have hF_neg :
        v * ((v - a) * (v - b) * (v - c) * (v - d)) < 0 :=
      mul_neg_of_neg_of_pos hv0 hprod_pos
    nlinarith
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_neg : (c - u) * (c - v) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_d_pos : 0 < P.eval d := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hdu_pos : 0 < d - u := sub_pos.mpr hud
    have hdv_pos : 0 < d - v := sub_pos.mpr hvd
    have hdw_neg : d - w < 0 := sub_neg.mpr hdw
    have h12_pos : 0 < (d - u) * (d - v) := mul_pos hdu_pos hdv_pos
    have hG_neg : (d - u) * (d - v) * (d - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hdw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg : P.eval w < 0 := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hwd_pos : 0 < w - d := sub_pos.mpr hdw
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have h123_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos h12_pos hwc_pos
    have hprod_pos : 0 < (w - a) * (w - b) * (w - c) * (w - d) :=
      mul_pos h123_pos hwd_pos
    have hF_neg :
        w * ((w - a) * (w - b) * (w - c) * (w - d)) < 0 :=
      mul_neg_of_neg_of_pos hw0 hprod_pos
    nlinarith
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubQuarticCubic_ne_zero a b c d u v w μ
  have hdeg_le : P.natDegree ≤ 5 := by
    dsimp [P]
    rw [natDegree_xSubQuarticCubic]
  have ht_bot : Tendsto (fun x => P.eval x) atBot atBot := by
    dsimp [P]
    exact tendsto_eval_xSubQuarticCubic_atBot_atBot a b c d u v w μ
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubQuarticCubic_atTop_atTop a b c d u v w μ
  have hP_zero_nonpos : P.eval 0 ≤ 0 := by
    dsimp [P]
    exact eval_xSubQuarticCubic_at_zero_nonpos (le_of_lt huv)
      (le_of_lt hvw) (le_of_lt hw0) hμ
  have hsplits := splits_of_three_sign_change_intervals_and_both_tails_of_le
    hP_ne hdeg_le (le_of_lt hau) hub hvc hdw (le_of_lt hbv)
    (le_of_lt hcd) (le_of_lt hw0) (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_u_pos hP_b_neg)
    (mul_neg_of_neg_of_pos hP_v_neg hP_c_pos)
    (mul_neg_of_pos_of_neg hP_d_pos hP_w_neg)
    hP_zero_nonpos ht_bot ht_top
  simpa [P] using hsplits

/-- Strict order `a < u < b < c < v < w < d < 0` for the normalized
quartic/cubic terminal. -/
lemma xSubQuarticCubicSplits_of_order_a_u_b_c_v_w_d
    {a b c d u v w μ : ℝ} (hau : a < u) (hub : u < b)
    (hbc : b < c) (hcv : c < v) (hvw : v < w) (hwd : w < d)
    (hd0 : d < 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  let P : ℝ[X] := xSubQuarticCubicPolynomial a b c d u v w μ
  have hav : a < v := lt_trans hau (lt_trans hub (lt_trans hbc hcv))
  have haw : a < w := lt_trans hav hvw
  have hbd : b < d := lt_trans hbc (lt_trans hcv (lt_trans hvw hwd))
  have hbw : b < w := lt_trans hbc (lt_trans hcv hvw)
  have hcw : c < w := lt_trans hcv hvw
  have hcd : c < d := lt_trans hcw hwd
  have hud : u < d := lt_trans hub hbd
  have huv : u < v := lt_trans hub (lt_trans hbc hcv)
  have huc : u < c := lt_trans hub hbc
  have hvd : v < d := lt_trans hvw hwd
  have hu0 : u < 0 := lt_trans hud hd0
  have hv0 : v < 0 := lt_trans hvd hd0
  have hw0 : w < 0 := lt_trans hwd hd0
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have haw_neg : a - w < 0 := sub_neg.mpr haw
    have h12_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    have hG_neg : (a - u) * (a - v) * (a - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos haw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hud_neg : u - d < 0 := sub_neg.mpr hud
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have h123_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) * (u - d) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hud_neg
    have hF_pos :
        0 < u * ((u - a) * (u - b) * (u - c) * (u - d)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr (lt_trans hbc hcv)
    have hbw_neg : b - w < 0 := sub_neg.mpr hbw
    have h12_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg hbu_pos hbv_neg
    have hG_pos : 0 < (b - u) * (b - v) * (b - w) :=
      mul_pos_of_neg_of_neg h12_neg hbw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_neg : c - v < 0 := sub_neg.mpr hcv
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have h12_neg : (c - u) * (c - v) < 0 :=
      mul_neg_of_pos_of_neg hcu_pos hcv_neg
    have hG_pos : 0 < (c - u) * (c - v) * (c - w) :=
      mul_pos_of_neg_of_neg h12_neg hcw_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr (lt_trans hbc hcv)
    have hvc_pos : 0 < v - c := sub_pos.mpr hcv
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos h12_pos hvc_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) * (v - d) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hvd_neg
    have hF_pos :
        0 < v * ((v - a) * (v - b) * (v - c) * (v - d)) :=
      mul_pos_of_neg_of_neg hv0 hprod_neg
    nlinarith
  have hP_w_pos : 0 < P.eval w := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hwd_neg : w - d < 0 := sub_neg.mpr hwd
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have h123_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos h12_pos hwc_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) * (w - d) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hwd_neg
    have hF_pos :
        0 < w * ((w - a) * (w - b) * (w - c) * (w - d)) :=
      mul_pos_of_neg_of_neg hw0 hprod_neg
    nlinarith
  have hP_d_neg : P.eval d < 0 := by
    dsimp [P]
    rw [eval_xSubQuarticCubic]
    have hdu_pos : 0 < d - u := sub_pos.mpr hud
    have hdv_pos : 0 < d - v := sub_pos.mpr hvd
    have hdw_pos : 0 < d - w := sub_pos.mpr hwd
    have h12_pos : 0 < (d - u) * (d - v) := mul_pos hdu_pos hdv_pos
    have hG_pos : 0 < (d - u) * (d - v) * (d - w) :=
      mul_pos h12_pos hdw_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubQuarticCubic_ne_zero a b c d u v w μ
  have hdeg_le : P.natDegree ≤ 5 := by
    dsimp [P]
    rw [natDegree_xSubQuarticCubic]
  have ht_bot : Tendsto (fun x => P.eval x) atBot atBot := by
    dsimp [P]
    exact tendsto_eval_xSubQuarticCubic_atBot_atBot a b c d u v w μ
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubQuarticCubic_atTop_atTop a b c d u v w μ
  have hP_zero_nonpos : P.eval 0 ≤ 0 := by
    dsimp [P]
    exact eval_xSubQuarticCubic_at_zero_nonpos (le_of_lt huv)
      (le_of_lt hvw) (le_of_lt hw0) hμ
  have hsplits := splits_of_three_sign_change_intervals_and_both_tails_of_le
    hP_ne hdeg_le (le_of_lt hau) hub hcv hwd (le_of_lt hbc)
    (le_of_lt hvw) (le_of_lt hd0) (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_u_pos hP_b_neg)
    (mul_neg_of_neg_of_pos hP_c_neg hP_v_pos)
    (mul_neg_of_pos_of_neg hP_w_pos hP_d_neg)
    hP_zero_nonpos ht_bot ht_top
  simpa [P] using hsplits

/-- Strict order `a < u < b < c < v < d < w < 0` for the normalized
quartic/cubic terminal. -/
lemma xSubQuarticCubicSplits_of_order_a_u_b_c_v_d_w
    {a b c d u v w μ : ℝ} (hau : a < u) (hub : u < b)
    (hbc : b < c) (hcv : c < v) (hvd : v < d) (hdw : d < w)
    (hw0 : w < 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  have hav : a < v := lt_trans hau (lt_trans hub (lt_trans hbc hcv))
  have haw : a < w := lt_trans hav (lt_trans hvd hdw)
  have hbd : b < d := lt_trans hbc (lt_trans hcv hvd)
  have hbw : b < w := lt_trans hbd hdw
  have hcw : c < w := lt_trans hcv (lt_trans hvd hdw)
  have hud : u < d := lt_trans hub hbd
  have huv : u < v := lt_trans hub (lt_trans hbc hcv)
  have huc : u < c := lt_trans hub hbc
  have hvw : v < w := lt_trans hvd hdw
  have hd0 : d < 0 := lt_trans hdw hw0
  have hu0 : u < 0 := lt_trans hud hd0
  have hv0 : v < 0 := lt_trans hvd hd0
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval a := by
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
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval u := by
    rw [eval_xSubQuarticCubic_at_u]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hud_neg : u - d < 0 := sub_neg.mpr hud
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have h123_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) * (u - d) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hud_neg
    exact mul_pos_of_neg_of_neg hu0 hprod_neg
  have hP_b_neg :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval b < 0 := by
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
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval c < 0 := by
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
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval v := by
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
  have hP_d_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval d := by
    rw [eval_xSubQuarticCubic_at_d]
    have hdu_pos : 0 < d - u := sub_pos.mpr hud
    have hdv_pos : 0 < d - v := sub_pos.mpr hvd
    have hdw_neg : d - w < 0 := sub_neg.mpr hdw
    have h12_pos : 0 < (d - u) * (d - v) := mul_pos hdu_pos hdv_pos
    have hG_neg : (d - u) * (d - v) * (d - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hdw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval w < 0 := by
    rw [eval_xSubQuarticCubic_at_w]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hwd_pos : 0 < w - d := sub_pos.mpr hdw
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have h123_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos h12_pos hwc_pos
    have hprod_pos : 0 < (w - a) * (w - b) * (w - c) * (w - d) :=
      mul_pos h123_pos hwd_pos
    exact mul_neg_of_neg_of_pos hw0 hprod_pos
  have hdeg_le : (xSubQuarticCubicPolynomial a b c d u v w μ).natDegree ≤ 5 := by
    rw [natDegree_xSubQuarticCubic]
  have hP_zero_nonpos :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval 0 ≤ 0 :=
    eval_xSubQuarticCubic_at_zero_nonpos (le_of_lt huv)
      (le_of_lt hvw) (le_of_lt hw0) hμ
  exact splits_of_three_sign_change_intervals_and_both_tails_of_le
    (xSubQuarticCubic_ne_zero a b c d u v w μ) hdeg_le (le_of_lt hau)
    hub hcv hdw (le_of_lt hbc) (le_of_lt hvd) (le_of_lt hw0)
    (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_u_pos hP_b_neg)
    (mul_neg_of_neg_of_pos hP_c_neg hP_v_pos)
    (mul_neg_of_pos_of_neg hP_d_pos hP_w_neg)
    hP_zero_nonpos
    (tendsto_eval_xSubQuarticCubic_atBot_atBot a b c d u v w μ)
    (tendsto_eval_xSubQuarticCubic_atTop_atTop a b c d u v w μ)

/-- Strict order `a < b < u < v < c < w < d < 0` for the normalized
quartic/cubic terminal. -/
lemma xSubQuarticCubicSplits_of_order_a_b_u_v_c_w_d
    {a b c d u v w μ : ℝ} (hab : a < b) (hbu : b < u)
    (huv : u < v) (hvc : v < c) (hcw : c < w) (hwd : w < d)
    (hd0 : d < 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  have hau : a < u := lt_trans hab hbu
  have hav : a < v := lt_trans hau huv
  have haw : a < w := lt_trans hav (lt_trans hvc hcw)
  have hbv : b < v := lt_trans hbu huv
  have hbw : b < w := lt_trans hbv (lt_trans hvc hcw)
  have hbd : b < d := lt_trans hbw hwd
  have huc : u < c := lt_trans huv hvc
  have hud : u < d := lt_trans huc (lt_trans hcw hwd)
  have hvw : v < w := lt_trans hvc hcw
  have hvd : v < d := lt_trans hvw hwd
  have hu0 : u < 0 := lt_trans hud hd0
  have hv0 : v < 0 := lt_trans hvd hd0
  have hw0 : w < 0 := lt_trans hwd hd0
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval a := by
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
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval b := by
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
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval u < 0 := by
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
  have hP_v_neg :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval v < 0 := by
    rw [eval_xSubQuarticCubic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) * (v - d) :=
      mul_pos_of_neg_of_neg h123_neg hvd_neg
    exact mul_neg_of_neg_of_pos hv0 hprod_pos
  have hP_c_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval c := by
    rw [eval_xSubQuarticCubic_at_c]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_neg : c - w < 0 := sub_neg.mpr hcw
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_neg : (c - u) * (c - v) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval w := by
    rw [eval_xSubQuarticCubic_at_w]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hwd_neg : w - d < 0 := sub_neg.mpr hwd
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have h123_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos h12_pos hwc_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) * (w - d) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hwd_neg
    exact mul_pos_of_neg_of_neg hw0 hprod_neg
  have hP_d_neg :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval d < 0 := by
    rw [eval_xSubQuarticCubic_at_d]
    have hdu_pos : 0 < d - u := sub_pos.mpr hud
    have hdv_pos : 0 < d - v := sub_pos.mpr hvd
    have hdw_pos : 0 < d - w := sub_pos.mpr hwd
    have h12_pos : 0 < (d - u) * (d - v) := mul_pos hdu_pos hdv_pos
    have hG_pos : 0 < (d - u) * (d - v) * (d - w) :=
      mul_pos h12_pos hdw_pos
    nlinarith [mul_pos hμ hG_pos]
  exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
    (le_of_lt huv) (le_of_lt hvw) (le_of_lt hw0) hμ (le_of_lt hab)
    hbu hvc hwd (le_of_lt huv) (le_of_lt hcw) (le_of_lt hd0)
    (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_b_pos hP_u_neg)
    (mul_neg_of_neg_of_pos hP_v_neg hP_c_pos)
    (mul_neg_of_pos_of_neg hP_w_pos hP_d_neg)

/-- Strict order `a < b < u < v < c < d < w < 0` for the normalized
quartic/cubic terminal. -/
lemma xSubQuarticCubicSplits_of_order_a_b_u_v_c_d_w
    {a b c d u v w μ : ℝ} (hab : a < b) (hbu : b < u)
    (huv : u < v) (hvc : v < c) (hcd : c < d) (hdw : d < w)
    (hw0 : w < 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  have hau : a < u := lt_trans hab hbu
  have hav : a < v := lt_trans hau huv
  have haw : a < w := lt_trans hav (lt_trans hvc (lt_trans hcd hdw))
  have hbv : b < v := lt_trans hbu huv
  have hbw : b < w := lt_trans hbv (lt_trans hvc (lt_trans hcd hdw))
  have huc : u < c := lt_trans huv hvc
  have hud : u < d := lt_trans huc hcd
  have hvd : v < d := lt_trans hvc hcd
  have hvw : v < w := lt_trans hvd hdw
  have hd0 : d < 0 := lt_trans hdw hw0
  have hu0 : u < 0 := lt_trans hud hd0
  have hv0 : v < 0 := lt_trans hvd hd0
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval a := by
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
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval b := by
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
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval u < 0 := by
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
  have hP_v_neg :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval v < 0 := by
    rw [eval_xSubQuarticCubic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) * (v - d) :=
      mul_pos_of_neg_of_neg h123_neg hvd_neg
    exact mul_neg_of_neg_of_pos hv0 hprod_pos
  have hP_c_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval c := by
    rw [eval_xSubQuarticCubic_at_c]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hcw_neg : c - w < 0 := sub_neg.mpr (lt_trans hcd hdw)
    have h12_pos : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    have hG_neg : (c - u) * (c - v) * (c - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hcw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_d_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval d := by
    rw [eval_xSubQuarticCubic_at_d]
    have hdu_pos : 0 < d - u := sub_pos.mpr hud
    have hdv_pos : 0 < d - v := sub_pos.mpr hvd
    have hdw_neg : d - w < 0 := sub_neg.mpr hdw
    have h12_pos : 0 < (d - u) * (d - v) := mul_pos hdu_pos hdv_pos
    have hG_neg : (d - u) * (d - v) * (d - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hdw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval w < 0 := by
    rw [eval_xSubQuarticCubic_at_w]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr (lt_trans hcd hdw)
    have hwd_pos : 0 < w - d := sub_pos.mpr hdw
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have h123_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos h12_pos hwc_pos
    have hprod_pos : 0 < (w - a) * (w - b) * (w - c) * (w - d) :=
      mul_pos h123_pos hwd_pos
    exact mul_neg_of_neg_of_pos hw0 hprod_pos
  exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
    (le_of_lt huv) (le_of_lt hvw) (le_of_lt hw0) hμ (le_of_lt hab)
    hbu hvc hdw (le_of_lt huv) (le_of_lt hcd) (le_of_lt hw0)
    (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_b_pos hP_u_neg)
    (mul_neg_of_neg_of_pos hP_v_neg hP_c_pos)
    (mul_neg_of_pos_of_neg hP_d_pos hP_w_neg)

/-- Strict order `a < b < u < c < v < w < d < 0` for the normalized
quartic/cubic terminal. -/
lemma xSubQuarticCubicSplits_of_order_a_b_u_c_v_w_d
    {a b c d u v w μ : ℝ} (hab : a < b) (hbu : b < u)
    (huc : u < c) (hcv : c < v) (hvw : v < w) (hwd : w < d)
    (hd0 : d < 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  have hau : a < u := lt_trans hab hbu
  have hav : a < v := lt_trans hau (lt_trans huc hcv)
  have haw : a < w := lt_trans hav hvw
  have hbv : b < v := lt_trans hbu (lt_trans huc hcv)
  have hbw : b < w := lt_trans hbv hvw
  have hud : u < d := lt_trans huc (lt_trans hcv (lt_trans hvw hwd))
  have huv : u < v := lt_trans huc hcv
  have hvd : v < d := lt_trans hvw hwd
  have hcw : c < w := lt_trans hcv hvw
  have hu0 : u < 0 := lt_trans hud hd0
  have hv0 : v < 0 := lt_trans hvd hd0
  have hw0 : w < 0 := lt_trans hwd hd0
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval a := by
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
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval b := by
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
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval u < 0 := by
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
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval c < 0 := by
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
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval v := by
    rw [eval_xSubQuarticCubic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_pos : 0 < v - c := sub_pos.mpr hcv
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos h12_pos hvc_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) * (v - d) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hvd_neg
    exact mul_pos_of_neg_of_neg hv0 hprod_neg
  have hP_w_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval w := by
    rw [eval_xSubQuarticCubic_at_w]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hwd_neg : w - d < 0 := sub_neg.mpr hwd
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have h123_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos h12_pos hwc_pos
    have hprod_neg : (w - a) * (w - b) * (w - c) * (w - d) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hwd_neg
    exact mul_pos_of_neg_of_neg hw0 hprod_neg
  have hP_d_neg :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval d < 0 := by
    rw [eval_xSubQuarticCubic_at_d]
    have hdu_pos : 0 < d - u := sub_pos.mpr hud
    have hdv_pos : 0 < d - v := sub_pos.mpr hvd
    have hdw_pos : 0 < d - w := sub_pos.mpr hwd
    have h12_pos : 0 < (d - u) * (d - v) := mul_pos hdu_pos hdv_pos
    have hG_pos : 0 < (d - u) * (d - v) * (d - w) :=
      mul_pos h12_pos hdw_pos
    nlinarith [mul_pos hμ hG_pos]
  exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
    (le_of_lt huv) (le_of_lt hvw) (le_of_lt hw0) hμ (le_of_lt hab)
    hbu hcv hwd (le_of_lt huc) (le_of_lt hvw) (le_of_lt hd0)
    (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_b_pos hP_u_neg)
    (mul_neg_of_neg_of_pos hP_c_neg hP_v_pos)
    (mul_neg_of_pos_of_neg hP_w_pos hP_d_neg)

/-- Strict order `a < b < u < c < v < d < w < 0` for the normalized
quartic/cubic terminal. -/
lemma xSubQuarticCubicSplits_of_order_a_b_u_c_v_d_w
    {a b c d u v w μ : ℝ} (hab : a < b) (hbu : b < u)
    (huc : u < c) (hcv : c < v) (hvd : v < d) (hdw : d < w)
    (hw0 : w < 0) (hμ : 0 < μ) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  have hau : a < u := lt_trans hab hbu
  have hav : a < v := lt_trans hau (lt_trans huc hcv)
  have haw : a < w := lt_trans hav (lt_trans hvd hdw)
  have hbv : b < v := lt_trans hbu (lt_trans huc hcv)
  have hbw : b < w := lt_trans hbv (lt_trans hvd hdw)
  have hud : u < d := lt_trans huc (lt_trans hcv hvd)
  have huv : u < v := lt_trans huc hcv
  have hvw : v < w := lt_trans hvd hdw
  have hcw : c < w := lt_trans hcv hvw
  have hd0 : d < 0 := lt_trans hdw hw0
  have hu0 : u < 0 := lt_trans hud hd0
  have hv0 : v < 0 := lt_trans hvd hd0
  have hP_a_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval a := by
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
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval b := by
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
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval u < 0 := by
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
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval c < 0 := by
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
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval v := by
    rw [eval_xSubQuarticCubic_at_v]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_pos : 0 < v - c := sub_pos.mpr hcv
    have hvd_neg : v - d < 0 := sub_neg.mpr hvd
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have h123_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos h12_pos hvc_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) * (v - d) < 0 :=
      mul_neg_of_pos_of_neg h123_pos hvd_neg
    exact mul_pos_of_neg_of_neg hv0 hprod_neg
  have hP_d_pos :
      0 < (xSubQuarticCubicPolynomial a b c d u v w μ).eval d := by
    rw [eval_xSubQuarticCubic_at_d]
    have hdu_pos : 0 < d - u := sub_pos.mpr hud
    have hdv_pos : 0 < d - v := sub_pos.mpr hvd
    have hdw_neg : d - w < 0 := sub_neg.mpr hdw
    have h12_pos : 0 < (d - u) * (d - v) := mul_pos hdu_pos hdv_pos
    have hG_neg : (d - u) * (d - v) * (d - w) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hdw_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_w_neg :
      (xSubQuarticCubicPolynomial a b c d u v w μ).eval w < 0 := by
    rw [eval_xSubQuarticCubic_at_w]
    have hwa_pos : 0 < w - a := sub_pos.mpr haw
    have hwb_pos : 0 < w - b := sub_pos.mpr hbw
    have hwc_pos : 0 < w - c := sub_pos.mpr hcw
    have hwd_pos : 0 < w - d := sub_pos.mpr hdw
    have h12_pos : 0 < (w - a) * (w - b) := mul_pos hwa_pos hwb_pos
    have h123_pos : 0 < (w - a) * (w - b) * (w - c) :=
      mul_pos h12_pos hwc_pos
    have hprod_pos : 0 < (w - a) * (w - b) * (w - c) * (w - d) :=
      mul_pos h123_pos hwd_pos
    exact mul_neg_of_neg_of_pos hw0 hprod_pos
  exact xSubQuarticCubicSplits_of_three_sign_change_intervals_and_zero_tail
    (le_of_lt huv) (le_of_lt hvw) (le_of_lt hw0) hμ (le_of_lt hab)
    hbu hcv hdw (le_of_lt huc) (le_of_lt hvd) (le_of_lt hw0)
    (le_of_lt hP_a_pos)
    (mul_neg_of_pos_of_neg hP_b_pos hP_u_neg)
    (mul_neg_of_neg_of_pos hP_c_neg hP_v_pos)
    (mul_neg_of_pos_of_neg hP_d_pos hP_w_neg)

/-- Dispatcher for the strict quartic/cubic terminal.  Once all finite root
inequalities and the two endpoint signs are strict, the only remaining choices
are whether `u` lies below or above `b`, whether `v` lies below or above `c`,
and whether `w` lies below or above `d`. -/
lemma xSubQuarticCubicSplits_of_strict_roots
    {a b c d u v w μ : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (huv : u < v) (hvw : v < w) (hau : a < u) (hbv : b < v)
    (hcw : c < w) (huc : u < c) (hvd : v < d)
    (hd0 : d < 0) (hw0 : w < 0) (hμ : 0 < μ)
    (hub_ne : u ≠ b) (hvc_ne : v ≠ c) (hwd_ne : w ≠ d) :
    (xSubQuarticCubicPolynomial a b c d u v w μ).Splits := by
  rcases lt_or_gt_of_ne hub_ne with hub | hbu
  · rcases lt_or_gt_of_ne hvc_ne with hvc | hcv
    · rcases lt_or_gt_of_ne hwd_ne with hwd | hdw
      · exact xSubQuarticCubicSplits_of_order_a_u_b_v_c_w_d
          hau hub hbv hvc hcw hwd hd0 hμ
      · exact xSubQuarticCubicSplits_of_order_a_u_b_v_c_d_w
          hau hub hbv hvc hcd hdw hw0 hμ
    · rcases lt_or_gt_of_ne hwd_ne with hwd | hdw
      · exact xSubQuarticCubicSplits_of_order_a_u_b_c_v_w_d
          hau hub hbc hcv hvw hwd hd0 hμ
      · exact xSubQuarticCubicSplits_of_order_a_u_b_c_v_d_w
          hau hub hbc hcv hvd hdw hw0 hμ
  · rcases lt_or_gt_of_ne hvc_ne with hvc | hcv
    · rcases lt_or_gt_of_ne hwd_ne with hwd | hdw
      · exact xSubQuarticCubicSplits_of_order_a_b_u_v_c_w_d
          hab hbu huv hvc hcw hwd hd0 hμ
      · exact xSubQuarticCubicSplits_of_order_a_b_u_v_c_d_w
          hab hbu huv hvc hcd hdw hw0 hμ
    · rcases lt_or_gt_of_ne hwd_ne with hwd | hdw
      · exact xSubQuarticCubicSplits_of_order_a_b_u_c_v_w_d
          hab hbu huc hcv hvw hwd hd0 hμ
      · exact xSubQuarticCubicSplits_of_order_a_b_u_c_v_d_w
          hab hbu huc hcv hvd hdw hw0 hμ


end LiuOppositeSigns
end RealRooted
