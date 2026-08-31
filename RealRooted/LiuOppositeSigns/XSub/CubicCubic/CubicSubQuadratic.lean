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
end LiuOppositeSigns
end RealRooted
