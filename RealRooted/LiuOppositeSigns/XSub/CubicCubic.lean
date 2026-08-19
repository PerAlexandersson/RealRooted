import RealRooted.LiuOppositeSigns.XSub.QuadraticQuadratic
import RealRooted.LiuOppositeSigns.XSub.SplittingTools
import RealRooted.MaWang

/-!
# Liu cubic/cubic x-subtraction leaf

This module contains the normalized cubic/cubic positive-split x-subtraction
leaf used by the same-degree right-degree-three endpoint.  It also contains
the cubic-minus-quadratic boundary helper used when the upper right root is
zero.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- A monic cubic minus a positive multiple of a monic quadratic is still a
genuine cubic. -/
lemma natDegree_cubicSubQuadratic (a b c u v μ : ℝ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).natDegree = 3 := by
  compute_degree <;> norm_num

/-- A monic cubic minus a positive multiple of a monic quadratic is nonzero. -/
lemma cubicSubQuadratic_ne_zero (a b c u v μ : ℝ) :
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v)) ≠ 0 := by
  intro hzero
  have hdeg := natDegree_cubicSubQuadratic a b c u v μ
  rw [hzero] at hdeg
  norm_num at hdeg

/-- Evaluation form of a monic cubic minus a positive multiple of a monic
quadratic. -/
lemma eval_cubicSubQuadratic (a b c u v μ x : ℝ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).eval x =
      (x - a) * (x - b) * (x - c) - μ * ((x - u) * (x - v)) := by
  simp only [eval_sub, eval_mul, eval_X, eval_C]

/-- The upper left root gives a nonpositive value for the cubic-minus-quadratic
pencil under the root-count inequalities. -/
lemma eval_cubicSubQuadratic_at_upper_nonpos {a b c u v μ : ℝ}
    (hbc : b ≤ c) (hub : u ≤ b) (hvc : v ≤ c) (hμ : 0 < μ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).eval c ≤ 0 := by
  rw [eval_cubicSubQuadratic]
  have hcu_nonneg : 0 ≤ c - u := sub_nonneg.mpr (hub.trans hbc)
  have hcv_nonneg : 0 ≤ c - v := sub_nonneg.mpr hvc
  have hG_nonneg : 0 ≤ (c - u) * (c - v) :=
    mul_nonneg hcu_nonneg hcv_nonneg
  nlinarith [mul_nonneg (le_of_lt hμ) hG_nonneg]

/-- A monic cubic minus a lower-degree quadratic has positive leading
coefficient. -/
lemma hasPosLeadingCoeff_cubicSubQuadratic (a b c u v μ : ℝ) :
    HasPosLeadingCoeff
      (((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))) := by
  have hcubic_pos : HasPosLeadingCoeff ((X - C a) * (X - C b) * (X - C c)) := by
    exact ((hasPosLeadingCoeff_X_sub_C a).mul (hasPosLeadingCoeff_X_sub_C b)).mul
      (hasPosLeadingCoeff_X_sub_C c)
  have hcubic_deg : ((X - C a) * (X - C b) * (X - C c)).natDegree = 3 := by
    compute_degree <;> norm_num
  have hdeg_lt : (C μ * ((X - C u) * (X - C v))).natDegree <
      ((X - C a) * (X - C b) * (X - C c)).natDegree := by
    rw [hcubic_deg]
    compute_degree
    norm_num
  unfold HasPosLeadingCoeff at hcubic_pos ⊢
  have hdegree_lt : degree (C μ * ((X - C u) * (X - C v))) <
      degree ((X - C a) * (X - C b) * (X - C c)) :=
    degree_lt_degree hdeg_lt
  rw [leadingCoeff_sub_of_degree_lt hdegree_lt]
  exact hcubic_pos

/-- The monic cubic-minus-quadratic pencil tends to `+∞` at `+∞`. -/
lemma tendsto_eval_cubicSubQuadratic_atTop_atTop (a b c u v μ : ℝ) :
    Tendsto
      (fun x =>
        (((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v))).eval x)
      atTop atTop := by
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_cubicSubQuadratic a b c u v μ
  have hP_deg : P.natDegree = 3 := by
    dsimp [P]
    exact natDegree_cubicSubQuadratic a b c u v μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      rw [hP_deg]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  exact P.tendsto_atTop_of_leadingCoeff_nonneg hP_deg_pos hP_pos.le

/-- Common-root boundary for a monic cubic-minus-quadratic pencil.  Factoring
out the shared linear term leaves the proved quadratic-minus-linear lemma. -/
lemma cubicSubQuadratic_splits_of_common_root {r a b c μ : ℝ}
    (hab : a ≤ b) (hcb : c ≤ b) (hμ : 0 < μ) :
    (((X - C r) * ((X - C a) * (X - C b))) -
      C μ * ((X - C r) * (X - C c))).Splits := by
  let Q : ℝ[X] := ((X - C a) * (X - C b)) - C μ * (X - C c)
  have hQ : Q.Splits := by
    dsimp [Q]
    exact quadraticSubLinear_splits_of_right_root_le_upper hab hcb hμ
  have hfactor :
      ((X - C r) * ((X - C a) * (X - C b))) -
        C μ * ((X - C r) * (X - C c)) = (X - C r) * Q := by
    dsimp [Q]
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C r).mul hQ

/-- Strict order case `u < a < v < b ≤ c` for a monic
cubic-minus-quadratic pencil. -/
lemma cubicSubQuadratic_splits_of_order_u_a_v_b
    {a b c u v μ : ℝ} (hua : u < a) (hav : a < v) (hvb : v < b)
    (hbc : b ≤ c) (hμ : 0 < μ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hub : u < b := lt_trans hua (lt_trans hav hvb)
  have huc : u < c := lt_of_lt_of_le hub hbc
  have hvc : v < c := lt_of_lt_of_le hvb hbc
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_pos : 0 < (u - a) * (u - b) :=
      mul_pos_of_neg_of_neg hua_neg hub_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have hG_neg : (a - u) * (a - v) < 0 :=
      mul_neg_of_pos_of_neg hau_pos hav_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_neg : v - b < 0 := sub_neg.mpr hvb
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_neg : (v - a) * (v - b) < 0 :=
      mul_neg_of_pos_of_neg hva_pos hvb_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos_of_neg_of_neg h12_neg hvc_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_pos : 0 < b - v := sub_pos.mpr hvb
    have hG_pos : 0 < (b - u) * (b - v) := mul_pos hbu_pos hbv_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_c_nonpos : P.eval c ≤ 0 := by
    dsimp [P]
    exact eval_cubicSubQuadratic_at_upper_nonpos hbc (le_of_lt hub)
      (le_of_lt hvc) hμ
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact cubicSubQuadratic_ne_zero a b c u v μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_cubicSubQuadratic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_cubicSubQuadratic_atTop_atTop a b c u v μ
  have hsplits :=
    splits_of_two_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hua hvb (le_of_lt hav) hbc
      (mul_neg_of_neg_of_pos hP_u_neg hP_a_pos)
      (mul_neg_of_pos_of_neg hP_v_pos hP_b_neg)
      hP_c_nonpos ht_top
  simpa [P] using hsplits

/-- Strict order case `u < a ≤ b < v < c` for a monic
cubic-minus-quadratic pencil. -/
lemma cubicSubQuadratic_splits_of_order_u_a_b_v
    {a b c u v μ : ℝ} (hua : u < a) (hab : a ≤ b) (hbv : b < v)
    (hvc : v < c) (hμ : 0 < μ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hav : a < v := lt_of_le_of_lt hab hbv
  have hub : u < b := lt_of_lt_of_le hua hab
  have huc : u < c := lt_trans hub (lt_trans hbv hvc)
  have hbc : b ≤ c := le_of_lt (lt_trans hbv hvc)
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hua_neg : u - a < 0 := sub_neg.mpr hua
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_pos : 0 < (u - a) * (u - b) :=
      mul_pos_of_neg_of_neg hua_neg hub_neg
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos huc_neg
    nlinarith
  have hP_a_pos : 0 < P.eval a := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hau_pos : 0 < a - u := sub_pos.mpr hua
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have hG_neg : (a - u) * (a - v) < 0 :=
      mul_neg_of_pos_of_neg hau_pos hav_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hG_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg hbu_pos hbv_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    nlinarith
  have hP_c_nonpos : P.eval c ≤ 0 := by
    dsimp [P]
    exact eval_cubicSubQuadratic_at_upper_nonpos hbc (le_of_lt hub)
      (le_of_lt hvc) hμ
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact cubicSubQuadratic_ne_zero a b c u v μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_cubicSubQuadratic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_cubicSubQuadratic_atTop_atTop a b c u v μ
  have hsplits :=
    splits_of_two_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hua hbv hab (le_of_lt hvc)
      (mul_neg_of_neg_of_pos hP_u_neg hP_a_pos)
      (mul_neg_of_pos_of_neg hP_b_pos hP_v_neg)
      hP_c_nonpos ht_top
  simpa [P] using hsplits

/-- Strict order case `a < u ≤ v < b ≤ c` for a monic
cubic-minus-quadratic pencil. -/
lemma cubicSubQuadratic_splits_of_order_a_u_v_b
    {a b c u v μ : ℝ} (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hbc : b ≤ c) (hμ : 0 < μ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hub : u < b := lt_of_le_of_lt huv hvb
  have hav : a < v := lt_of_lt_of_le hau huv
  have huc : u < c := lt_of_lt_of_le hub hbc
  have hvc : v < c := lt_of_lt_of_le hvb hbc
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have hG_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    nlinarith
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_neg : v - b < 0 := sub_neg.mpr hvb
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_neg : (v - a) * (v - b) < 0 :=
      mul_neg_of_pos_of_neg hva_pos hvb_neg
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) :=
      mul_pos_of_neg_of_neg h12_neg hvc_neg
    nlinarith
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_pos : 0 < b - v := sub_pos.mpr hvb
    have hG_pos : 0 < (b - u) * (b - v) := mul_pos hbu_pos hbv_pos
    nlinarith [mul_pos hμ hG_pos]
  have hP_c_nonpos : P.eval c ≤ 0 := by
    dsimp [P]
    exact eval_cubicSubQuadratic_at_upper_nonpos hbc (le_of_lt hub)
      (le_of_lt hvc) hμ
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact cubicSubQuadratic_ne_zero a b c u v μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_cubicSubQuadratic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_cubicSubQuadratic_atTop_atTop a b c u v μ
  have hsplits :=
    splits_of_two_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hau hvb huv hbc
      (mul_neg_of_neg_of_pos hP_a_neg hP_u_pos)
      (mul_neg_of_pos_of_neg hP_v_pos hP_b_neg)
      hP_c_nonpos ht_top
  simpa [P] using hsplits

/-- Strict order case `a < u < b < v < c` for a monic
cubic-minus-quadratic pencil. -/
lemma cubicSubQuadratic_splits_of_order_a_u_b_v
    {a b c u v μ : ℝ} (hau : a < u) (hub : u < b) (hbv : b < v)
    (hvc : v < c) (hμ : 0 < μ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  let P : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hav : a < v := lt_trans hau (lt_trans hub hbv)
  have huc : u < c := lt_trans hub (lt_trans hbv hvc)
  have hbc : b ≤ c := le_of_lt (lt_trans hbv hvc)
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hau_neg : a - u < 0 := sub_neg.mpr hau
    have hav_neg : a - v < 0 := sub_neg.mpr hav
    have hG_pos : 0 < (a - u) * (a - v) :=
      mul_pos_of_neg_of_neg hau_neg hav_neg
    nlinarith [mul_pos hμ hG_pos]
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have h12_neg : (u - a) * (u - b) < 0 :=
      mul_neg_of_pos_of_neg hua_pos hub_neg
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) :=
      mul_pos_of_neg_of_neg h12_neg huc_neg
    nlinarith
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hbu_pos : 0 < b - u := sub_pos.mpr hub
    have hbv_neg : b - v < 0 := sub_neg.mpr hbv
    have hG_neg : (b - u) * (b - v) < 0 :=
      mul_neg_of_pos_of_neg hbu_pos hbv_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_cubicSubQuadratic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have h12_pos : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
    have hprod_neg : (v - a) * (v - b) * (v - c) < 0 :=
      mul_neg_of_pos_of_neg h12_pos hvc_neg
    nlinarith
  have hP_c_nonpos : P.eval c ≤ 0 := by
    dsimp [P]
    exact eval_cubicSubQuadratic_at_upper_nonpos hbc (le_of_lt hub)
      (le_of_lt hvc) hμ
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact cubicSubQuadratic_ne_zero a b c u v μ
  have hdeg_le : P.natDegree ≤ 3 := by
    dsimp [P]
    rw [natDegree_cubicSubQuadratic]
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_cubicSubQuadratic_atTop_atTop a b c u v μ
  have hsplits :=
    splits_of_two_sign_change_intervals_and_right_tail
      hP_ne hdeg_le hau hbv (le_of_lt hub) (le_of_lt hvc)
      (mul_neg_of_neg_of_pos hP_a_neg hP_u_pos)
      (mul_neg_of_pos_of_neg hP_b_pos hP_v_neg)
      hP_c_nonpos ht_top
  simpa [P] using hsplits

/-- A monic cubic minus a positive multiple of a monic quadratic splits under the
weak root-count inequalities produced by the cubic/cubic `w = 0` boundary. -/
lemma cubicSubQuadratic_splits_of_roots_le {a b c u v μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v)
    (hub : u ≤ b) (hvc : v ≤ c) (hav : a ≤ v) (hμ : 0 < μ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  by_cases hua_eq : u = a
  · subst u
    have hsplits := cubicSubQuadratic_splits_of_common_root
      (r := a) (a := b) (b := c) (c := v) hbc hvc hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  by_cases hva_eq : v = a
  · subst v
    have huc : u ≤ c := hub.trans hbc
    have hsplits := cubicSubQuadratic_splits_of_common_root
      (r := a) (a := b) (b := c) (c := u) hbc huc hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  by_cases hub_eq : u = b
  · subst u
    have hac : a ≤ c := hab.trans hbc
    have hsplits := cubicSubQuadratic_splits_of_common_root
      (r := b) (a := a) (b := c) (c := v) hac hvc hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  by_cases hvb_eq : v = b
  · subst v
    have hac : a ≤ c := hab.trans hbc
    have huc : u ≤ c := hub.trans hbc
    have hsplits := cubicSubQuadratic_splits_of_common_root
      (r := b) (a := a) (b := c) (c := u) hac huc hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  by_cases hvc_eq : v = c
  · subst v
    have hsplits := cubicSubQuadratic_splits_of_common_root
      (r := c) (a := a) (b := b) (c := u) hab hub hμ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsplits
  have hav_lt : a < v := lt_of_le_of_ne hav (by intro h; exact hva_eq h.symm)
  by_cases hua : u < a
  · by_cases hvb : v < b
    · exact cubicSubQuadratic_splits_of_order_u_a_v_b
        hua hav_lt hvb hbc hμ
    · have hbv : b < v :=
        lt_of_le_of_ne (le_of_not_gt hvb) (by intro h; exact hvb_eq h.symm)
      have hvc_lt : v < c := lt_of_le_of_ne hvc hvc_eq
      exact cubicSubQuadratic_splits_of_order_u_a_b_v
        hua hab hbv hvc_lt hμ
  · have hau : a < u :=
      lt_of_le_of_ne (le_of_not_gt hua) (by intro h; exact hua_eq h.symm)
    by_cases hvb : v < b
    · exact cubicSubQuadratic_splits_of_order_a_u_v_b
        hau huv hvb hbc hμ
    · have hub_lt : u < b := lt_of_le_of_ne hub hub_eq
      have hbv : b < v :=
        lt_of_le_of_ne (le_of_not_gt hvb) (by intro h; exact hvb_eq h.symm)
      have hvc_lt : v < c := lt_of_le_of_ne hvc hvc_eq
      exact cubicSubQuadratic_splits_of_order_a_u_b_v
        hau hub_lt hbv hvc_lt hμ

/-- In the `(3, 3)` positive split root-count case, neither ordered root list
can contain two roots strictly beyond the next root of the other list.  These
four finite inequalities are the cubic/cubic analogue of the overlap data used
in the quadratic/quadratic endpoint. -/
lemma roots_order_of_positiveSplitRootCountPair_three_three
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    {a b c u v w : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (huv : u ≤ v) (hvw : v ≤ w)
    (hfroots : f.roots = {a, b, c}) (hgroots : g.roots = {u, v, w}) :
    u ≤ b ∧ v ≤ c ∧ a ≤ v ∧ b ≤ w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hub
    have hbu : b < u := lt_of_not_ge hub
    let x : ℝ := (b + u) / 2
    have hbx : b < x := by
      dsimp [x]
      linarith
    have hxu : x ≤ u := by
      dsimp [x]
      linarith
    have hax : a < x := lt_of_le_of_lt hab hbx
    have hxv : x ≤ v := hxu.trans huv
    have hxw : x ≤ w := hxv.trans hvw
    have hf_count_le : rootCountAtOrAbove f x ≤ 1 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xa : ¬ x ≤ a := not_le.mpr hax
      have hnot_xb : ¬ x ≤ b := not_le.mpr hbx
      by_cases hxc : x ≤ c <;> simp [hnot_xa, hnot_xb, hxc]
    have hg_count : rootCountAtOrAbove g x = 3 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      simp [hxu, hxv, hxw]
    have hcount := h.count.right_sub_le_one x
    rw [hg_count] at hcount
    norm_num at hcount
    have hf_count_int : ((rootCountAtOrAbove f x : ℤ) ≤ 1) := by exact_mod_cast hf_count_le
    linarith
  · by_contra hvc
    have hcv : c < v := lt_of_not_ge hvc
    let x : ℝ := (c + v) / 2
    have hcx : c < x := by
      dsimp [x]
      linarith
    have hxv : x ≤ v := by
      dsimp [x]
      linarith
    have hax : a < x := lt_of_le_of_lt (hab.trans hbc) hcx
    have hbx : b < x := lt_of_le_of_lt hbc hcx
    have hxw : x ≤ w := hxv.trans hvw
    have hf_count : rootCountAtOrAbove f x = 0 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xa : ¬ x ≤ a := not_le.mpr hax
      have hnot_xb : ¬ x ≤ b := not_le.mpr hbx
      have hnot_xc : ¬ x ≤ c := not_le.mpr hcx
      simp [hnot_xa, hnot_xb, hnot_xc]
    have hg_count_ge : 2 ≤ rootCountAtOrAbove g x := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      by_cases hxu : x ≤ u <;> simp [hxu, hxv, hxw]
    have hcount := h.count.right_sub_le_one x
    rw [hf_count] at hcount
    norm_num at hcount
    have hg_count_int : (2 : ℤ) ≤ rootCountAtOrAbove g x := by exact_mod_cast hg_count_ge
    linarith
  · by_contra hav
    have hva : v < a := lt_of_not_ge hav
    let x : ℝ := (a + v) / 2
    have hxa : x ≤ a := by
      dsimp [x]
      linarith
    have hvx : v < x := by
      dsimp [x]
      linarith
    have hxb : x ≤ b := hxa.trans hab
    have hxc : x ≤ c := hxb.trans hbc
    have hux : u < x := lt_of_le_of_lt huv hvx
    have hf_count : rootCountAtOrAbove f x = 3 := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      simp [hxa, hxb, hxc]
    have hg_count_le : rootCountAtOrAbove g x ≤ 1 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xu : ¬ x ≤ u := not_le.mpr hux
      have hnot_xv : ¬ x ≤ v := not_le.mpr hvx
      by_cases hxw : x ≤ w <;> simp [hnot_xu, hnot_xv, hxw]
    have hcount := h.count.left_sub_le_one x
    rw [hf_count] at hcount
    norm_num at hcount
    have hg_count_int : ((rootCountAtOrAbove g x : ℤ) ≤ 1) := by exact_mod_cast hg_count_le
    linarith
  · by_contra hbw
    have hwb : w < b := lt_of_not_ge hbw
    let x : ℝ := (b + w) / 2
    have hxb : x ≤ b := by
      dsimp [x]
      linarith
    have hwx : w < x := by
      dsimp [x]
      linarith
    have hxc : x ≤ c := hxb.trans hbc
    have hux : u < x := lt_of_le_of_lt (huv.trans hvw) hwx
    have hvx : v < x := lt_of_le_of_lt hvw hwx
    have hf_count_ge : 2 ≤ rootCountAtOrAbove f x := by
      rw [rootCountAtOrAbove, hfroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      by_cases hxa : x ≤ a <;> simp [hxa, hxb, hxc]
    have hg_count : rootCountAtOrAbove g x = 0 := by
      rw [rootCountAtOrAbove, hgroots]
      simp only [Multiset.insert_eq_cons, Multiset.filter_cons,
        Multiset.filter_singleton]
      have hnot_xu : ¬ x ≤ u := not_le.mpr hux
      have hnot_xv : ¬ x ≤ v := not_le.mpr hvx
      have hnot_xw : ¬ x ≤ w := not_le.mpr hwx
      simp [hnot_xu, hnot_xv, hnot_xw]
    have hcount := h.count.left_sub_le_one x
    rw [hg_count] at hcount
    norm_num at hcount
    have hf_count_int : (2 : ℤ) ≤ rootCountAtOrAbove f x := by exact_mod_cast hf_count_ge
    linarith

/-- A `(3, 3)` positive split root-count pair admits ordered root data with
the four finite inequalities needed by the cubic/cubic x-subtraction endpoint.
-/
lemma exists_roots_order_of_positiveSplitRootCountPair_three_three
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    (hfdeg : f.natDegree = 3) (hgdeg : g.natDegree = 3) :
    ∃ a b c u v w : ℝ,
      a ≤ b ∧ b ≤ c ∧ u ≤ v ∧ v ≤ w ∧
        f.roots = {a, b, c} ∧ g.roots = {u, v, w} ∧
          f = C f.leadingCoeff * ((X - C a) * (X - C b) * (X - C c)) ∧
            g = C g.leadingCoeff * ((X - C u) * (X - C v) * (X - C w)) ∧
              u ≤ b ∧ v ≤ c ∧ a ≤ v ∧ b ≤ w := by
  obtain ⟨a, b, c, hab, hbc, hfroots, hffac⟩ :=
    exists_roots_triple_of_splits_natDegree_three h.left_splits hfdeg
  obtain ⟨u, v, w, huv, hvw, hgroots, hgfac⟩ :=
    exists_roots_triple_of_splits_natDegree_three h.right_splits hgdeg
  obtain ⟨hub, hvc, hav, hbw⟩ :=
    roots_order_of_positiveSplitRootCountPair_three_three
      h hab hbc huv hvw hfroots hgroots
  exact
    ⟨a, b, c, u, v, w, hab, hbc, huv, hvw, hfroots, hgroots,
      hffac, hgfac, hub, hvc, hav, hbw⟩

/-- Normalized monic arithmetic leaf for the degree-three/degree-three
same-degree positive-split x-subtraction endpoint.  The finite root-order
inequalities are exactly those supplied by a `(3, 3)`
`PositiveSplitRootCountPair`. -/
def xSubCubicCubicSplitsStatement : Prop :=
  ∀ {a b c u v w μ : ℝ},
    a ≤ b → b ≤ c → u ≤ v → v ≤ w →
      u ≤ b → v ≤ c → a ≤ v → b ≤ w →
        c ≤ 0 → w ≤ 0 → 0 < μ →
          (X * ((X - C a) * (X - C b) * (X - C c)) -
              C μ * ((X - C u) * (X - C v) * (X - C w))).Splits

/-- The normalized cubic/cubic x-subtraction polynomial is a genuine quartic. -/
lemma natDegree_xSubCubicCubic (a b c u v w μ : ℝ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).natDegree = 4 := by
  compute_degree <;> norm_num

/-- The normalized cubic/cubic x-subtraction polynomial is nonzero. -/
lemma xSubCubicCubic_ne_zero (a b c u v w μ : ℝ) :
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w)) ≠ 0 := by
  intro hzero
  have hdeg := natDegree_xSubCubicCubic a b c u v w μ
  rw [hzero] at hdeg
  norm_num at hdeg

/-- The normalized cubic/cubic x-subtraction polynomial has positive leading
coefficient. -/
lemma hasPosLeadingCoeff_xSubCubicCubic (a b c u v w μ : ℝ) :
    HasPosLeadingCoeff
      (X * ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v) * (X - C w))) := by
  have hcubic_pos : HasPosLeadingCoeff ((X - C a) * (X - C b) * (X - C c)) := by
    exact ((hasPosLeadingCoeff_X_sub_C a).mul (hasPosLeadingCoeff_X_sub_C b)).mul
      (hasPosLeadingCoeff_X_sub_C c)
  have hleft_pos : HasPosLeadingCoeff (X * ((X - C a) * (X - C b) * (X - C c))) :=
    hcubic_pos.X_mul
  have hleft_deg :
      (X * ((X - C a) * (X - C b) * (X - C c))).natDegree = 4 := by
    compute_degree <;> norm_num
  have hdeg_lt : (C μ * ((X - C u) * (X - C v) * (X - C w))).natDegree <
      (X * ((X - C a) * (X - C b) * (X - C c))).natDegree := by
    rw [hleft_deg]
    compute_degree
    norm_num
  unfold HasPosLeadingCoeff at hleft_pos ⊢
  have hdegree_lt :
      degree (C μ * ((X - C u) * (X - C v) * (X - C w))) <
        degree (X * ((X - C a) * (X - C b) * (X - C c))) :=
    degree_lt_degree hdeg_lt
  rw [leadingCoeff_sub_of_degree_lt hdegree_lt]
  exact hleft_pos

/-- Evaluation form of the normalized cubic/cubic x-subtraction leaf. -/
lemma eval_xSubCubicCubic (a b c u v w μ x : ℝ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).eval x =
      x * ((x - a) * (x - b) * (x - c)) -
        μ * ((x - u) * (x - v) * (x - w)) := by
  simp only [eval_sub, eval_mul, eval_X, eval_C]

/-- The normalized cubic/cubic x-subtraction polynomial tends to `+∞` at
`-∞`. -/
lemma tendsto_eval_xSubCubicCubic_atBot_atTop (a b c u v w μ : ℝ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v) * (X - C w))).eval x)
      atBot atTop := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubCubicCubic a b c u v w μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      dsimp [P]
      rw [natDegree_xSubCubicCubic]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  have hP_even : Even P.natDegree := by
    dsimp [P]
    rw [natDegree_xSubCubicCubic]
    norm_num
  exact tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hP_pos hP_deg_pos hP_even

/-- The normalized cubic/cubic x-subtraction polynomial tends to `+∞` at
`+∞`. -/
lemma tendsto_eval_xSubCubicCubic_atTop_atTop (a b c u v w μ : ℝ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v) * (X - C w))).eval x)
      atTop atTop := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubCubicCubic a b c u v w μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      dsimp [P]
      rw [natDegree_xSubCubicCubic]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  exact P.tendsto_atTop_of_leadingCoeff_nonneg hP_deg_pos hP_pos.le

/-- A cubic whose roots lie between consecutive roots of the quartic
`X * (X - a) * (X - b) * (X - c)` interlaces that quartic. -/
lemma interlaces_cubic_quartic_of_roots_between {a b c u v w : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hc0 : c ≤ 0)
    (huv : u ≤ v) (hvw : v ≤ w)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvc : v ≤ c) (hcw : c ≤ w) (hw0 : w ≤ 0) :
    Interlaces ((X - C u) * (X - C v) * (X - C w))
      (X * ((X - C a) * (X - C b) * (X - C c))) := by
  let f : ℝ[X] := X * ((X - C a) * (X - C b) * (X - C c))
  let g : ℝ[X] := (X - C u) * (X - C v) * (X - C w)
  have hf_ne : f ≠ 0 := by
    dsimp [f]
    exact mul_ne_zero X_ne_zero
      (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b))
        (X_sub_C_ne_zero c))
  have hg_ne : g ≠ 0 := by
    dsimp [g]
    exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero u) (X_sub_C_ne_zero v))
      (X_sub_C_ne_zero w)
  have hf_split : f.Splits := by
    dsimp [f]
    exact Polynomial.Splits.X.mul
      (((Polynomial.Splits.X_sub_C a).mul (Polynomial.Splits.X_sub_C b)).mul
        (Polynomial.Splits.X_sub_C c))
  have hg_split : g.Splits := by
    dsimp [g]
    exact ((Polynomial.Splits.X_sub_C u).mul (Polynomial.Splits.X_sub_C v)).mul
      (Polynomial.Splits.X_sub_C w)
  have hf_deg : f.natDegree = 4 := by
    dsimp [f]
    compute_degree <;> norm_num
  have hg_deg : g.natDegree = 3 := by
    dsimp [g]
    compute_degree <;> norm_num
  have hf_roots : (↑[a, b, c, 0] : Multiset ℝ) = f.roots := by
    dsimp [f] at hf_ne ⊢
    rw [roots_mul hf_ne, roots_X,
      roots_mul (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero a)
        (X_sub_C_ne_zero b)) (X_sub_C_ne_zero c)),
      roots_mul (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)),
      roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
    change ({a} : Multiset ℝ) + {b} + {c} + {0} =
      ({0} : Multiset ℝ) + ({a} + {b} + {c})
    ac_rfl
  have hg_roots : (↑[u, v, w] : Multiset ℝ) = g.roots := by
    dsimp [g] at hg_ne ⊢
    rw [roots_mul hg_ne, roots_mul (mul_ne_zero (X_sub_C_ne_zero u)
        (X_sub_C_ne_zero v)),
      roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
    rfl
  change Interlaces g f
  exact Interlaces.of_cubic_quartic_root_lists
    hf_ne hf_split hg_ne hg_split hf_deg hg_deg hf_roots.symm hg_roots.symm
    hab hbc hc0 huv hvw hau hub hbv hvc hcw hw0

/-- In the ordinary interlacing subcase of the normalized cubic/cubic leaf, the
desired splitting follows from the Ma--Wang weak-sign theorem. -/
lemma xSubCubicCubicSplits_of_interlacing_roots {a b c u v w μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hc0 : c ≤ 0)
    (huv : u ≤ v) (hvw : v ≤ w)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v)
    (hvc : v ≤ c) (hcw : c ≤ w) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C w))).Splits := by
  let f : ℝ[X] := X * ((X - C a) * (X - C b) * (X - C c))
  let g : ℝ[X] := (X - C u) * (X - C v) * (X - C w)
  have hgf : Interlaces g f := by
    dsimp [f, g]
    exact interlaces_cubic_quartic_of_roots_between
      hab hbc hc0 huv hvw hau hub hbv hvc hcw hw0
  have hf_deg : f.natDegree = 4 := by
    dsimp [f]
    compute_degree <;> norm_num
  have hF_deg : ((1 : ℝ[X]) * f + (-C μ) * g).natDegree = 4 := by
    dsimp [f, g]
    simpa [sub_eq_add_neg] using natDegree_xSubCubicCubic a b c u v w μ
  have hg_pos : HasPosLeadingCoeff g := by
    dsimp [g]
    exact ((hasPosLeadingCoeff_X_sub_C u).mul (hasPosLeadingCoeff_X_sub_C v)).mul
      (hasPosLeadingCoeff_X_sub_C w)
  have hF_pos : HasPosLeadingCoeff ((1 : ℝ[X]) * f + (-C μ) * g) := by
    dsimp [f, g]
    simpa [sub_eq_add_neg] using hasPosLeadingCoeff_xSubCubicCubic a b c u v w μ
  have hdeg_lo : f.natDegree ≤ ((1 : ℝ[X]) * f + (-C μ) * g).natDegree := by rw [hf_deg, hF_deg]
  have hdeg_hi : ((1 : ℝ[X]) * f + (-C μ) * g).natDegree ≤ f.natDegree + 1 := by
    rw [hf_deg, hF_deg]
    norm_num
  have hb_nonpos : ∀ r, f.IsRoot r → (-C μ).eval r ≤ 0 := by
    intro r _
    simpa only [eval_neg, eval_C, Left.neg_nonpos_iff] using le_of_lt hμ
  have hprec : Prec f ((1 : ℝ[X]) * f + (-C μ) * g) :=
    prec_of_interlaces_evalCoeff_nonpos
      hgf hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
  have hsplits : ((1 : ℝ[X]) * f + (-C μ) * g).Splits := hprec.2.1.2
  dsimp [f, g] at hsplits ⊢
  simpa [sub_eq_add_neg] using hsplits

/-- If the normalized cubic/cubic x-subtraction endpoints share a linear
factor, the splitting problem reduces to the already proved
quadratic/quadratic leaf. -/
lemma xSubCubicCubicSplits_of_common_root {r a b c d μ : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (had : a ≤ d) (hcb : c ≤ b)
    (hb0 : b ≤ 0) (hd0 : d ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C r) * ((X - C a) * (X - C b))) -
      C μ * ((X - C r) * ((X - C c) * (X - C d)))).Splits := by
  let Q : ℝ[X] := X * ((X - C a) * (X - C b)) -
    C μ * ((X - C c) * (X - C d))
  have hQ : Q.Splits := by
    dsimp [Q]
    exact xSubQuadraticQuadraticSplits hab hcd had hcb hb0 hd0 hμ
  have hfactor :
      X * ((X - C r) * ((X - C a) * (X - C b))) -
        C μ * ((X - C r) * ((X - C c) * (X - C d))) =
        (X - C r) * Q := by
    dsimp [Q]
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C r).mul hQ

/-- Boundary case of the normalized cubic/cubic leaf where the lower
right-endpoint root equals the lower left-endpoint root. -/
lemma xSubCubicCubicSplits_of_lower_common_root {a b c v w μ : ℝ}
    (hbc : b ≤ c) (hvw : v ≤ w) (hvc : v ≤ c) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C a) * (X - C v) * (X - C w))).Splits := by
  have hcommon := xSubCubicCubicSplits_of_common_root
    (r := a) (a := b) (b := c) (c := v) (d := w)
    hbc hvw hbw hvc hc0 hw0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon

/-- Boundary case of the normalized cubic/cubic leaf where the middle
right-endpoint root equals the middle left-endpoint root. -/
lemma xSubCubicCubicSplits_of_middle_common_root {a b c u w μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hub : u ≤ b) (hbw : b ≤ w)
    (hc0 : c ≤ 0) (hw0 : w ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C b) * (X - C w))).Splits := by
  have hac : a ≤ c := hab.trans hbc
  have huw : u ≤ w := hub.trans hbw
  have haw : a ≤ w := hab.trans hbw
  have huc : u ≤ c := hub.trans hbc
  have hcommon := xSubCubicCubicSplits_of_common_root
    (r := b) (a := a) (b := c) (c := u) (d := w)
    hac huw haw huc hc0 hw0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon

/-- Boundary case of the normalized cubic/cubic leaf where the upper
right-endpoint root equals the upper left-endpoint root. -/
lemma xSubCubicCubicSplits_of_upper_common_root {a b c u v μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v) (hub : u ≤ b)
    (hav : a ≤ v) (hvc : v ≤ c) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v) * (X - C c))).Splits := by
  have hb0 : b ≤ 0 := hbc.trans hc0
  have hv0 : v ≤ 0 := hvc.trans hc0
  have hcommon := xSubCubicCubicSplits_of_common_root
    (r := c) (a := a) (b := b) (c := u) (d := v)
    hab huv hav hub hb0 hv0 hμ
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcommon

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

/-- The normalized monic cubic/cubic x-subtraction leaf. -/
theorem xSubCubicCubicSplits :
    xSubCubicCubicSplitsStatement := by
  intro a b c u v w μ hab hbc huv hvw hub hvc hav hbw hc0 hw0 hμ
  by_cases hw_eq : w = 0
  · subst w
    by_cases hc_eq : c = 0
    · subst c
      simpa using xSubCubicCubicSplits_of_upper_roots_zero
        hab huv hav hub hbw hvc hμ
    · simpa using xSubCubicCubicSplits_of_right_upper_root_zero
        hab hbc huv hub hvc hav hμ
  · have hw_lt : w < 0 := lt_of_le_of_ne hw0 hw_eq
    exact xSubCubicCubicSplits_of_negative_endpoints
      hab hbc huv hvw hub hvc hav hbw hc0 hw_lt hμ

/-- The normalized monic cubic/cubic x-subtraction leaf implies the
degree-three/degree-three positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement)
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 3) (hqdeg : q.natDegree = 3)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  obtain ⟨a, b, c, u, v, w, hab, hbc, huv, hvw, hproots, hqroots,
      hpfac, hqfac, hub, hvc, hav, hbw⟩ :=
    exists_roots_order_of_positiveSplitRootCountPair_three_three
      hpair hpdeg hqdeg
  have hc0 : c ≤ 0 := by
    have hc_mem : c ∈ p.roots := by
      rw [hproots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hpnn c hc_mem
  have hw0 : w ≤ 0 := by
    have hw_mem : w ∈ q.roots := by
      rw [hqroots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hqnn w hw_mem
  let A : ℝ := p.leadingCoeff
  let B : ℝ := q.leadingCoeff
  have hA_pos : 0 < A := by
    dsimp [A]
    exact hpair.left_pos
  have hB_pos : 0 < B := by
    dsimp [B]
    exact hpair.right_pos
  let ν : ℝ := μ * B / A
  have hν_pos : 0 < ν := by
    dsimp [ν]
    exact div_pos (mul_pos hμ hB_pos) hA_pos
  let inner : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C ν * ((X - C u) * (X - C v) * (X - C w))
  have hinner_splits : inner.Splits := by
    dsimp [inner]
    exact hmono hab hbc huv hvw hub hvc hav hbw hc0 hw0 hν_pos
  have hpoly : X * p - C μ * q = C A * inner := by
    rw [hpfac, hqfac]
    dsimp [inner, ν, A, B]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    field_simp [hpair.left_pos.ne']
  rw [hpoly]
  exact hinner_splits.C_mul A

/-- The normalized monic cubic/cubic x-subtraction leaf implies the
degree-three/degree-three positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_three
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 3) (hqdeg : q.natDegree = 3)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits :=
  splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_three_of_monic
    xSubCubicCubicSplits hpair hpnn hqnn hpdeg hqdeg hμ

/-- Degree-three right endpoint reduction for the same-degree sign-normalized
x-subtraction leaf, modulo the normalized monic cubic/cubic arithmetic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg : f.natDegree = 3 := by lia
  have hFdeg : (f.comp (X + C r)).natDegree = 3 := by simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 3 := by simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_three_of_monic
    hmono (hpair.comp_X_add_C r) hfnn hgnn hFdeg hGdeg hμ

/-- Degree-three right endpoint reduction for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_three
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
    xSubCubicCubicSplits hpair hfnn hgnn hdeg hgdeg

/-- Endpoint cases through right degree three for the same-degree sign-normalized
x-subtraction leaf, modulo the normalized monic cubic/cubic arithmetic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hle_two : g.natDegree ≤ 2
  · exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
      hpair hfnn hgnn hdeg hle_two
  · have hthree : g.natDegree = 3 := by lia
    exact
      positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
        hmono hpair hfnn hgnn hdeg hthree

/-- Endpoint cases through right degree three for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
    xSubCubicCubicSplits hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-three right endpoint reduction as a predicate-restricted
same-degree sign-normalized x-subtraction target, modulo the normalized monic
cubic/cubic arithmetic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement) :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact
    positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
      hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-three right endpoint reduction as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) :=
  positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
    xSubCubicCubicSplits

/-- Pack the endpoint cases through degree three as a predicate-restricted
same-degree sign-normalized x-subtraction target, modulo the normalized monic
cubic/cubic arithmetic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement) :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact
    positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
      hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the endpoint cases through degree three as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) :=
  positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three_of_monic
    xSubCubicCubicSplits

end LiuOppositeSigns
end RealRooted
