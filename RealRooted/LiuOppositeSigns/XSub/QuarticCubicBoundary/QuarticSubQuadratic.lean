import RealRooted.LiuOppositeSigns.XSub.QuarticCubicBoundary.Statements

/-!
# Quartic-minus-quadratic boundary leaf

The quartic-minus-quadratic endpoint factor and the right endpoint-zero package.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

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

/-- The quartic-minus-quadratic factor is monic. -/
lemma monic_quarticSubQuadratic (a b c d u v μ : ℝ) :
    (quarticSubQuadraticPolynomial a b c d u v μ).Monic := by
  unfold quarticSubQuadraticPolynomial
  monicity!

/-- The normalized quartic-minus-quadratic factor has positive leading
coefficient. -/
lemma hasPosLeadingCoeff_quarticSubQuadratic (a b c d u v μ : ℝ) :
    HasPosLeadingCoeff (quarticSubQuadraticPolynomial a b c d u v μ) := by
  unfold HasPosLeadingCoeff
  simp [(monic_quarticSubQuadratic a b c d u v μ).leadingCoeff]

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


end LiuOppositeSigns
end RealRooted
