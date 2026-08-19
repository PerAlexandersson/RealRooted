import RealRooted.LiuOppositeSigns.XSub.LeftSucc
import RealRooted.LiuOppositeSigns.XSub.SplittingTools
import RealRooted.MaWang

/-!
# Liu cubic/quadratic x-subtraction leaf

This module contains the normalized positive cubic/quadratic x-subtraction
arithmetic leaf used by the left-successor right-degree-two endpoint.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Normalized monic arithmetic leaf for the degree-three/degree-two
x-subtraction endpoint.  The inequalities are exactly the finite root-order
data supplied by `PositiveSplitRootCountPair`, while `c ≤ 0` and `v ≤ 0`
record coefficientwise nonnegativity after translation. -/
def xSubCubicQuadraticSplitsStatement : Prop :=
  ∀ {a b c u v μ : ℝ},
    a ≤ b → b ≤ c → u ≤ v → a ≤ u → b ≤ v → u ≤ c →
      c ≤ 0 → v ≤ 0 → 0 < μ →
        (X * ((X - C a) * (X - C b) * (X - C c)) -
            C μ * ((X - C u) * (X - C v))).Splits

/-- The normalized cubic/quadratic x-subtraction polynomial is a genuine
quartic. -/
lemma natDegree_xSubCubicQuadratic (a b c u v μ : ℝ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).natDegree = 4 := by
  compute_degree <;> norm_num

/-- The normalized cubic/quadratic x-subtraction polynomial is nonzero. -/
lemma xSubCubicQuadratic_ne_zero (a b c u v μ : ℝ) :
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v)) ≠ 0 := by
  intro hzero
  have hdeg := natDegree_xSubCubicQuadratic a b c u v μ
  rw [hzero] at hdeg
  norm_num at hdeg

/-- The normalized cubic/quadratic x-subtraction polynomial has positive
leading coefficient. -/
lemma hasPosLeadingCoeff_xSubCubicQuadratic (a b c u v μ : ℝ) :
    HasPosLeadingCoeff
      (X * ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C v))) := by
  have hcubic_pos : HasPosLeadingCoeff ((X - C a) * (X - C b) * (X - C c)) := by
    exact ((hasPosLeadingCoeff_X_sub_C a).mul (hasPosLeadingCoeff_X_sub_C b)).mul
      (hasPosLeadingCoeff_X_sub_C c)
  have hleft_pos : HasPosLeadingCoeff (X * ((X - C a) * (X - C b) * (X - C c))) :=
    hcubic_pos.X_mul
  have hleft_deg :
      (X * ((X - C a) * (X - C b) * (X - C c))).natDegree = 4 := by
    compute_degree <;> norm_num
  have hdeg_lt : (C μ * ((X - C u) * (X - C v))).natDegree <
      (X * ((X - C a) * (X - C b) * (X - C c))).natDegree := by
    rw [hleft_deg]
    compute_degree
    norm_num
  unfold HasPosLeadingCoeff at hleft_pos ⊢
  have hdegree_lt : degree (C μ * ((X - C u) * (X - C v))) <
      degree (X * ((X - C a) * (X - C b) * (X - C c))) :=
    degree_lt_degree hdeg_lt
  rw [leadingCoeff_sub_of_degree_lt hdegree_lt]
  exact hleft_pos

/-- Evaluation form of the normalized cubic/quadratic x-subtraction leaf. -/
lemma eval_xSubCubicQuadratic (a b c u v μ x : ℝ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).eval x =
      x * ((x - a) * (x - b) * (x - c)) - μ * ((x - u) * (x - v)) := by
  simp only [eval_sub, eval_mul, eval_X, eval_C]

/-- The normalized cubic/quadratic x-subtraction polynomial tends to `+∞` at
`-∞`. -/
lemma tendsto_eval_xSubCubicQuadratic_atBot_atTop (a b c u v μ : ℝ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v))).eval x)
      atBot atTop := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubCubicQuadratic a b c u v μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      dsimp [P]
      rw [natDegree_xSubCubicQuadratic]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  have hP_even : Even P.natDegree := by
    dsimp [P]
    rw [natDegree_xSubCubicQuadratic]
    norm_num
  exact tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hP_pos hP_deg_pos hP_even

/-- The normalized cubic/quadratic x-subtraction polynomial tends to `+∞` at
`+∞`. -/
lemma tendsto_eval_xSubCubicQuadratic_atTop_atTop (a b c u v μ : ℝ) :
    Tendsto
      (fun x =>
        (X * ((X - C a) * (X - C b) * (X - C c)) -
          C μ * ((X - C u) * (X - C v))).eval x)
      atTop atTop := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_xSubCubicQuadratic a b c u v μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      dsimp [P]
      rw [natDegree_xSubCubicQuadratic]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  exact P.tendsto_atTop_of_leadingCoeff_nonneg hP_deg_pos hP_pos.le

/-- The monic cubic minus a linear term is still a genuine cubic. -/
lemma natDegree_cubicSubLinear (a b c u μ : ℝ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * (X - C u)).natDegree = 3 := by
  compute_degree <;> norm_num

/-- The monic cubic minus a linear term is nonzero. -/
lemma cubicSubLinear_ne_zero (a b c u μ : ℝ) :
    ((X - C a) * (X - C b) * (X - C c)) -
      C μ * (X - C u) ≠ 0 := by
  intro hzero
  have hdeg := natDegree_cubicSubLinear a b c u μ
  rw [hzero] at hdeg
  norm_num at hdeg

/-- Evaluation form of a monic cubic minus a linear term. -/
lemma eval_cubicSubLinear (a b c u μ x : ℝ) :
    (((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)).eval x =
      (x - a) * (x - b) * (x - c) - μ * (x - u) := by
  simp only [eval_sub, eval_mul, eval_X, eval_C]

/-- Coefficient expansion of a monic cubic minus a linear term. -/
lemma cubicSubLinear_eq_cubic_expansion (a b c u μ : ℝ) :
    ((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u) =
      C 1 * X ^ 3 + C (-(a + b + c)) * X ^ 2 +
        C (a * b + a * c + b * c - μ) * X +
          C (-(a * b * c) + μ * u) := by
  simp only [C_add, C_mul, C_neg, C_sub, C_1]
  ring

/-- The monic cubic minus a lower-degree linear term has positive leading
coefficient. -/
lemma hasPosLeadingCoeff_cubicSubLinear (a b c u μ : ℝ) :
    HasPosLeadingCoeff
      (((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)) := by
  have hcubic_pos : HasPosLeadingCoeff ((X - C a) * (X - C b) * (X - C c)) := by
    exact ((hasPosLeadingCoeff_X_sub_C a).mul (hasPosLeadingCoeff_X_sub_C b)).mul
      (hasPosLeadingCoeff_X_sub_C c)
  have hcubic_deg : ((X - C a) * (X - C b) * (X - C c)).natDegree = 3 := by
    compute_degree <;> norm_num
  have hdeg_lt : (C μ * (X - C u)).natDegree <
      ((X - C a) * (X - C b) * (X - C c)).natDegree := by
    rw [hcubic_deg]
    compute_degree
    norm_num
  unfold HasPosLeadingCoeff at hcubic_pos ⊢
  have hdegree_lt : degree (C μ * (X - C u)) <
      degree ((X - C a) * (X - C b) * (X - C c)) :=
    degree_lt_degree hdeg_lt
  rw [leadingCoeff_sub_of_degree_lt hdegree_lt]
  exact hcubic_pos

/-- The monic cubic minus a linear term tends to `-∞` at `-∞`. -/
lemma tendsto_eval_cubicSubLinear_atBot_atBot (a b c u μ : ℝ) :
    Tendsto
      (fun x => (((X - C a) * (X - C b) * (X - C c)) -
        C μ * (X - C u)).eval x)
      atBot atBot := by
  let P : ℝ[X] := ((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_cubicSubLinear a b c u μ
  have hP_deg : P.natDegree = 3 := by
    dsimp [P]
    exact natDegree_cubicSubLinear a b c u μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      rw [hP_deg]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  have hP_odd : Odd P.natDegree := by
    rw [hP_deg]
    norm_num
  exact tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hP_pos hP_deg_pos hP_odd

/-- The monic cubic minus a linear term tends to `+∞` at `+∞`. -/
lemma tendsto_eval_cubicSubLinear_atTop_atTop (a b c u μ : ℝ) :
    Tendsto
      (fun x => (((X - C a) * (X - C b) * (X - C c)) -
        C μ * (X - C u)).eval x)
      atTop atTop := by
  let P : ℝ[X] := ((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)
  have hP_pos : HasPosLeadingCoeff P := by
    dsimp [P]
    exact hasPosLeadingCoeff_cubicSubLinear a b c u μ
  have hP_deg : P.natDegree = 3 := by
    dsimp [P]
    exact natDegree_cubicSubLinear a b c u μ
  have hP_deg_pos : 0 < P.degree := by
    have hnat : 0 < P.natDegree := by
      rw [hP_deg]
      norm_num
    exact natDegree_pos_iff_degree_pos.mp hnat
  exact P.tendsto_atTop_of_leadingCoeff_nonneg hP_deg_pos hP_pos.le

/-- A monic quadratic minus a positive constant splits over `ℝ`. -/
lemma quadraticSubConst_splits (a b μ : ℝ) (hμ : 0 < μ) :
    (((X - C a) * (X - C b)) - C μ).Splits := by
  have hpoly :
      ((X - C a) * (X - C b)) - C μ =
        C 1 * X ^ 2 + C (-(a + b)) * X + C (a * b - μ) := by
    simp only [C_add, C_mul, C_neg, C_sub, C_1]
    ring
  have hdisc : 0 ≤ discrim 1 (-(a + b)) (a * b - μ) := by
    rw [discrim]
    nlinarith [sq_nonneg (a - b), hμ]
  rw [hpoly]
  exact quadraticPoly_splits_of_discrim_nonneg one_ne_zero hdisc

/-- A monic cubic minus a positive linear term splits when the linear root lies
in the closed interval spanned by the cubic roots. -/
lemma cubicSubLinear_splits_of_root_mem_closed_interval
    {a b c u μ : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hau : a ≤ u) (huc : u ≤ c) (hμ : 0 < μ) :
    (((X - C a) * (X - C b) * (X - C c)) -
      C μ * (X - C u)).Splits := by
  by_cases hua_eq : u = a
  · subst u
    let Q : ℝ[X] := ((X - C b) * (X - C c)) - C μ
    have hQ : Q.Splits := by
      dsimp [Q]
      exact quadraticSubConst_splits b c μ hμ
    have hfactor :
        ((X - C a) * (X - C b) * (X - C c)) -
          C μ * (X - C a) = (X - C a) * Q := by
      dsimp [Q]
      ring
    rw [hfactor]
    exact (Polynomial.Splits.X_sub_C a).mul hQ
  by_cases hub_eq : u = b
  · subst u
    let Q : ℝ[X] := ((X - C a) * (X - C c)) - C μ
    have hQ : Q.Splits := by
      dsimp [Q]
      exact quadraticSubConst_splits a c μ hμ
    have hfactor :
        ((X - C a) * (X - C b) * (X - C c)) -
          C μ * (X - C b) = (X - C b) * Q := by
      dsimp [Q]
      ring
    rw [hfactor]
    exact (Polynomial.Splits.X_sub_C b).mul hQ
  by_cases huc_eq : u = c
  · subst u
    let Q : ℝ[X] := ((X - C a) * (X - C b)) - C μ
    have hQ : Q.Splits := by
      dsimp [Q]
      exact quadraticSubConst_splits a b μ hμ
    have hfactor :
        ((X - C a) * (X - C b) * (X - C c)) -
          C μ * (X - C c) = (X - C c) * Q := by
      dsimp [Q]
      ring
    rw [hfactor]
    exact (Polynomial.Splits.X_sub_C c).mul hQ
  have hau_lt : a < u := lt_of_le_of_ne hau (by intro h; exact hua_eq h.symm)
  have huc_lt : u < c := lt_of_le_of_ne huc huc_eq
  by_cases hub : u < b
  · let P : ℝ[X] :=
      ((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)
    have hP_a_pos : 0 < P.eval a := by
      dsimp [P]
      rw [eval_cubicSubLinear]
      nlinarith [mul_pos hμ (sub_pos.mpr hau_lt)]
    have hP_u_pos : 0 < P.eval u := by
      dsimp [P]
      rw [eval_cubicSubLinear, sub_self, mul_zero, sub_zero]
      have hua_pos : 0 < u - a := sub_pos.mpr hau_lt
      have hub_neg : u - b < 0 := sub_neg.mpr hub
      have huc_neg : u - c < 0 := sub_neg.mpr huc_lt
      exact mul_pos_of_neg_of_neg
        (mul_neg_of_pos_of_neg hua_pos hub_neg) huc_neg
    have hP_b_neg : P.eval b < 0 := by
      dsimp [P]
      rw [eval_cubicSubLinear]
      nlinarith [mul_pos hμ (sub_pos.mpr hub)]
    have hP_c_neg : P.eval c < 0 := by
      dsimp [P]
      rw [eval_cubicSubLinear]
      nlinarith [mul_pos hμ (sub_pos.mpr huc_lt)]
    have hP_deg : P.natDegree = 3 := by
      dsimp [P]
      exact natDegree_cubicSubLinear a b c u μ
    have ht_bot : Tendsto (fun x => P.eval x) atBot atBot := by
      dsimp [P]
      exact tendsto_eval_cubicSubLinear_atBot_atBot a b c u μ
    have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
      dsimp [P]
      exact tendsto_eval_cubicSubLinear_atTop_atTop a b c u μ
    obtain ⟨rL, hrL_le, hrL_root⟩ :=
      exists_isRoot_le_of_eval_nonneg_of_tendsto_atBot_atBot
        (le_of_lt hP_a_pos) ht_bot
    obtain ⟨r₁, hu_r₁, hr₁_b, hr₁_root⟩ :=
      exists_isRoot_between_of_eval_mul_neg hub
        (mul_neg_of_pos_of_neg hP_u_pos hP_b_neg)
    obtain ⟨rR, hrR_ge, hrR_root⟩ :=
      exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
        (le_of_lt hP_c_neg) ht_top
    have hL1 : rL < r₁ :=
      lt_of_le_of_lt (hrL_le.trans (le_of_lt hau_lt)) hu_r₁
    have h1R : r₁ < rR :=
      lt_of_lt_of_le (lt_of_lt_of_le hr₁_b hbc) hrR_ge
    have hP_ne : P ≠ 0 := by
      dsimp [P]
      exact cubicSubLinear_ne_zero a b c u μ
    have hdeg_le : P.natDegree ≤ [rL, r₁, rR].length := by
      rw [hP_deg]
      norm_num
    have hsplits := splits_of_three_ordered_roots_of_natDegree_le
      hP_ne (by simpa using hdeg_le) hL1 h1R hrL_root hr₁_root hrR_root
    simpa [P] using hsplits
  · have hbu : b < u :=
      lt_of_le_of_ne (le_of_not_gt hub) (by intro h; exact hub_eq h.symm)
    let P : ℝ[X] :=
      ((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)
    have hP_a_pos : 0 < P.eval a := by
      dsimp [P]
      rw [eval_cubicSubLinear]
      nlinarith [mul_pos hμ (sub_pos.mpr hau_lt)]
    have hP_b_pos : 0 < P.eval b := by
      dsimp [P]
      rw [eval_cubicSubLinear]
      nlinarith [mul_pos hμ (sub_pos.mpr hbu)]
    have hP_u_neg : P.eval u < 0 := by
      dsimp [P]
      rw [eval_cubicSubLinear, sub_self, mul_zero, sub_zero]
      have hua_pos : 0 < u - a := sub_pos.mpr hau_lt
      have hub_pos : 0 < u - b := sub_pos.mpr hbu
      have huc_neg : u - c < 0 := sub_neg.mpr huc_lt
      exact mul_neg_of_pos_of_neg (mul_pos hua_pos hub_pos) huc_neg
    have hP_c_neg : P.eval c < 0 := by
      dsimp [P]
      rw [eval_cubicSubLinear]
      nlinarith [mul_pos hμ (sub_pos.mpr huc_lt)]
    have hP_deg : P.natDegree = 3 := by
      dsimp [P]
      exact natDegree_cubicSubLinear a b c u μ
    have ht_bot : Tendsto (fun x => P.eval x) atBot atBot := by
      dsimp [P]
      exact tendsto_eval_cubicSubLinear_atBot_atBot a b c u μ
    have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
      dsimp [P]
      exact tendsto_eval_cubicSubLinear_atTop_atTop a b c u μ
    obtain ⟨rL, hrL_le, hrL_root⟩ :=
      exists_isRoot_le_of_eval_nonneg_of_tendsto_atBot_atBot
        (le_of_lt hP_a_pos) ht_bot
    obtain ⟨r₁, hb_r₁, hr₁_u, hr₁_root⟩ :=
      exists_isRoot_between_of_eval_mul_neg hbu
        (mul_neg_of_pos_of_neg hP_b_pos hP_u_neg)
    obtain ⟨rR, hrR_ge, hrR_root⟩ :=
      exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop
        (le_of_lt hP_c_neg) ht_top
    have hL1 : rL < r₁ := lt_of_le_of_lt (hrL_le.trans hab) hb_r₁
    have h1R : r₁ < rR := lt_of_lt_of_le (lt_trans hr₁_u huc_lt) hrR_ge
    have hP_ne : P ≠ 0 := by
      dsimp [P]
      exact cubicSubLinear_ne_zero a b c u μ
    have hdeg_le : P.natDegree ≤ [rL, r₁, rR].length := by
      rw [hP_deg]
      norm_num
    have hsplits := splits_of_three_ordered_roots_of_natDegree_le
      hP_ne (by simpa using hdeg_le) hL1 h1R hrL_root hr₁_root hrR_root
    simpa [P] using hsplits

/-- Common-root boundary for a monic quartic-minus-quadratic pencil.  Factoring
out the shared root leaves the cubic-minus-linear closed-interval leaf. -/
lemma quarticSubQuadratic_splits_of_common_root {r a b c u μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hau : a ≤ u) (huc : u ≤ c)
    (hμ : 0 < μ) :
    (((X - C r) * ((X - C a) * (X - C b) * (X - C c))) -
      C μ * ((X - C r) * (X - C u))).Splits := by
  let Q : ℝ[X] := ((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)
  have hQ : Q.Splits := by
    dsimp [Q]
    exact cubicSubLinear_splits_of_root_mem_closed_interval hab hbc hau huc hμ
  have hfactor :
      ((X - C r) * ((X - C a) * (X - C b) * (X - C c))) -
        C μ * ((X - C r) * (X - C u)) = (X - C r) * Q := by
    dsimp [Q]
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C r).mul hQ

/-- A quadratic whose roots lie between consecutive roots of a monic cubic
interlaces that cubic. -/
lemma interlaces_quadratic_cubic_of_roots_between {a b c u v : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v) (hvc : v ≤ c) :
    Interlaces ((X - C u) * (X - C v))
      ((X - C a) * (X - C b) * (X - C c)) := by
  let f : ℝ[X] := (X - C a) * (X - C b) * (X - C c)
  let g : ℝ[X] := (X - C u) * (X - C v)
  have hf_ne : f ≠ 0 := by
    dsimp [f]
    exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b))
      (X_sub_C_ne_zero c)
  have hg_ne : g ≠ 0 := by
    dsimp [g]
    exact mul_ne_zero (X_sub_C_ne_zero u) (X_sub_C_ne_zero v)
  have hf_split : f.Splits := by
    dsimp [f]
    exact ((Polynomial.Splits.X_sub_C a).mul (Polynomial.Splits.X_sub_C b)).mul
      (Polynomial.Splits.X_sub_C c)
  have hg_split : g.Splits := by
    dsimp [g]
    exact (Polynomial.Splits.X_sub_C u).mul (Polynomial.Splits.X_sub_C v)
  have hf_deg : f.natDegree = 3 := by
    dsimp [f]
    rw [natDegree_mul (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b))
        (X_sub_C_ne_zero c),
      natDegree_mul (X_sub_C_ne_zero a) (X_sub_C_ne_zero b),
      natDegree_X_sub_C, natDegree_X_sub_C, natDegree_X_sub_C]
  have hg_deg : g.natDegree = 2 := by
    dsimp [g]
    rw [natDegree_mul (X_sub_C_ne_zero u) (X_sub_C_ne_zero v),
      natDegree_X_sub_C, natDegree_X_sub_C]
  have hf_roots : f.roots = {a, b, c} := by
    dsimp [f] at hf_ne ⊢
    rw [roots_mul hf_ne,
      roots_mul (mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)),
      roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
    rfl
  have hg_roots : g.roots = {u, v} := by
    dsimp [g] at hg_ne ⊢
    rw [roots_mul hg_ne, roots_X_sub_C, roots_X_sub_C]
    rfl
  change Interlaces g f
  exact Interlaces.of_quadratic_cubic_root_lists
    hf_ne hf_split hg_ne hg_split hf_deg hg_deg
    (by rw [hf_roots]; rfl) (by rw [hg_roots]; rfl)
    hab hbc huv hau hub hbv hvc

/-- In the ordinary interlacing subcase of the normalized cubic/quadratic
leaf, the desired splitting follows from the Ma--Wang coefficient criterion. -/
lemma xSubCubicQuadraticSplits_of_interlacing_roots {a b c u v μ : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (huv : u ≤ v)
    (hau : a ≤ u) (hub : u ≤ b) (hbv : b ≤ v) (hvc : v ≤ c)
    (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  let f : ℝ[X] := (X - C a) * (X - C b) * (X - C c)
  let g : ℝ[X] := (X - C u) * (X - C v)
  have hgf : Interlaces g f := by
    dsimp [f, g]
    exact interlaces_quadratic_cubic_of_roots_between
      hab hbc huv hau hub hbv hvc
  have hf_ne : f ≠ 0 := hgf.1.1
  have hg_pos : HasPosLeadingCoeff g := by
    dsimp [g]
    exact (hasPosLeadingCoeff_X_sub_C u).mul (hasPosLeadingCoeff_X_sub_C v)
  have hf_pos : HasPosLeadingCoeff f := by
    dsimp [f]
    exact ((hasPosLeadingCoeff_X_sub_C a).mul (hasPosLeadingCoeff_X_sub_C b)).mul
      (hasPosLeadingCoeff_X_sub_C c)
  have hXf_pos : HasPosLeadingCoeff (X * f) := hf_pos.X_mul
  have hXf_deg : (X * f).natDegree = f.natDegree + 1 := natDegree_X_mul hf_ne
  have hXf_deg_lo : f.natDegree ≤ (X * f).natDegree := by
    rw [hXf_deg]
    exact Nat.le_succ _
  have hsum_eq : X * f + (-C μ) * g = X * f - C μ * g := by ring
  have hsum_deg : (X * f + (-C μ) * g).natDegree = (X * f).natDegree := by
    rw [hsum_eq]
    exact natDegree_sub_C_mul_eq_of_interlaces_degree_lower_bound hgf hXf_deg_lo μ
  have hF_pos : HasPosLeadingCoeff (X * f + (-C μ) * g) := by
    rw [hsum_eq]
    exact hasPosLeadingCoeff_sub_C_mul_of_interlaces_degree_lower_bound
      hgf hXf_deg_lo hXf_pos μ
  have hdeg_lo : f.natDegree ≤ (X * f + (-C μ) * g).natDegree := by
    rw [hsum_deg]
    exact hXf_deg_lo
  have hdeg_hi : (X * f + (-C μ) * g).natDegree ≤ f.natDegree + 1 := by rw [hsum_deg, hXf_deg]
  have hcoeff_nonpos : ∀ r, f.IsRoot r → (-C μ).eval r ≤ 0 := by
    intro r _
    simpa only [eval_neg, eval_C, Left.neg_nonpos_iff] using le_of_lt hμ
  have hprec : Prec f (X * f + (-C μ) * g) :=
    prec_of_interlaces_evalCoeff_nonpos hgf hg_pos hF_pos hdeg_lo hdeg_hi
      hcoeff_nonpos
  have hsplits : (X * f + (-C μ) * g).Splits := hprec.2.1.2
  dsimp [f, g] at hsplits ⊢
  simpa [sub_eq_add_neg] using hsplits

/-- Strict nonordinary subcase of the normalized cubic/quadratic leaf where the
quadratic roots lie between `b` and `c`.  The proof finds four distinct real
roots by sign changes on `(-∞, a]`, `(b, u)`, `(v, c)`, and `[0, ∞)`, then
uses the quartic degree to conclude splitting. -/
lemma xSubCubicQuadraticSplits_of_middle_quadratic_roots_strict
    {a b c u v μ : ℝ} (hab : a ≤ b) (hbu : b < u) (huv : u ≤ v)
    (hvc : v < c) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hau : a < u := lt_of_le_of_lt hab hbu
  have hav : a < v := lt_of_lt_of_le hau huv
  have huc : u < c := lt_of_le_of_lt huv hvc
  have hu0 : u < 0 := lt_of_lt_of_le huc hc0
  have hv0 : v < 0 := lt_of_lt_of_le hvc hc0
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hG : 0 < (a - u) * (a - v) := by
      exact mul_pos_of_neg_of_neg (sub_neg.mpr hau) (sub_neg.mpr hav)
    nlinarith [mul_pos hμ hG]
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hbv : b < v := lt_of_lt_of_le hbu huv
    have hG : 0 < (b - u) * (b - v) := by
      exact mul_pos_of_neg_of_neg (sub_neg.mpr hbu) (sub_neg.mpr hbv)
    nlinarith [mul_pos hμ hG]
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_pos : 0 < u - b := sub_pos.mpr hbu
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 := by
      have h12 : 0 < (u - a) * (u - b) := mul_pos hua_pos hub_pos
      exact mul_neg_of_pos_of_neg h12 huc_neg
    have hH_pos : 0 < u * ((u - a) * (u - b) * (u - c)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_v_pos : 0 < P.eval v := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hbv : b < v := lt_of_lt_of_le hbu huv
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_neg : v - c < 0 := sub_neg.mpr hvc
    have hprod_neg : (v - a) * (v - b) * (v - c) < 0 := by
      have h12 : 0 < (v - a) * (v - b) := mul_pos hva_pos hvb_pos
      exact mul_neg_of_pos_of_neg h12 hvc_neg
    have hH_pos : 0 < v * ((v - a) * (v - b) * (v - c)) :=
      mul_pos_of_neg_of_neg hv0 hprod_neg
    nlinarith
  have hP_c_neg : P.eval c < 0 := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hcu_pos : 0 < c - u := sub_pos.mpr huc
    have hcv_pos : 0 < c - v := sub_pos.mpr hvc
    have hG : 0 < (c - u) * (c - v) := mul_pos hcu_pos hcv_pos
    nlinarith [mul_pos hμ hG]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hG : 0 < (0 - u) * (0 - v) := by exact mul_pos (sub_pos.mpr hu0) (sub_pos.mpr hv0)
    nlinarith [mul_pos hμ hG]
  have ht_bot : Tendsto (fun x => P.eval x) atBot atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicQuadratic_atBot_atTop a b c u v μ
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicQuadratic_atTop_atTop a b c u v μ
  obtain ⟨rL, hrL_le, hrL_root⟩ :=
    exists_isRoot_le_of_eval_nonpos_of_tendsto_atBot_atTop (le_of_lt hP_a_neg) ht_bot
  obtain ⟨r₁, hb_r₁, hr₁_u, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hbu (mul_neg_of_neg_of_pos hP_b_neg hP_u_pos)
  obtain ⟨r₂, hv_r₂, hr₂_c, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hvc (mul_neg_of_pos_of_neg hP_v_pos hP_c_neg)
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop (le_of_lt hP_zero_neg) ht_top
  have hL1 : rL < r₁ := lt_of_le_of_lt (hrL_le.trans hab) hb_r₁
  have h12 : r₁ < r₂ := lt_trans hr₁_u (lt_of_le_of_lt huv hv_r₂)
  have h2R : r₂ < rR := lt_of_lt_of_le (lt_of_lt_of_le hr₂_c hc0) hrR_ge
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicQuadratic_ne_zero a b c u v μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicQuadratic]
  have hsplits := splits_of_four_ordered_roots_of_natDegree_le
    hP_ne hdeg_le hL1 h12 h2R hrL_root hr₁_root hr₂_root hrR_root
  simpa [P] using hsplits

/-- Boundary case of the middle-root quartic leaf when the upper quadratic root
is the upper cubic root.  Factoring out `X - c` reduces the claim to the
existing normalized quadratic/linear cubic-discriminant terminal. -/
lemma xSubCubicQuadraticSplits_of_middle_quadratic_roots_at_right_endpoint
    {a b c u μ : ℝ} (hab : a ≤ b) (hbu : b < u) (huc : u ≤ c)
    (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C c))).Splits := by
  let Q : ℝ[X] := X * ((X - C a) * (X - C b)) - C μ * (X - C u)
  have hau : a ≤ u := hab.trans (le_of_lt hbu)
  have hb0 : b ≤ 0 := (le_of_lt hbu).trans (huc.trans hc0)
  have hu0 : u ≤ 0 := huc.trans hc0
  have hQ_deg : Q.natDegree ≤ 3 := by
    dsimp [Q]
    compute_degree
  have hQ_disc : 0 ≤ cubicDiscr Q := by
    dsimp [Q]
    exact xSubQuadraticLinearCubicDiscrimNonneg hab hau hb0 hu0 hμ
  have hQ_splits : Q.Splits :=
    splits_of_natDegree_le_three_cubicDiscr_nonneg hQ_deg hQ_disc
  have hfactor :
      X * ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * (X - C c)) = (X - C c) * Q := by
    dsimp [Q]
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C c).mul hQ_splits

/-- Closed middle-root subcase of the normalized cubic/quadratic leaf.  This
packages the strict middle-root proof together with the `v = c` boundary
factorization. -/
lemma xSubCubicQuadraticSplits_of_middle_quadratic_roots
    {a b c u v μ : ℝ} (hab : a ≤ b) (hbu : b < u) (huv : u ≤ v)
    (hvc : v ≤ c) (hc0 : c ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  by_cases hv_lt : v < c
  · exact xSubCubicQuadraticSplits_of_middle_quadratic_roots_strict
      hab hbu huv hv_lt hc0 hμ
  · have hcv : c ≤ v := le_of_not_gt hv_lt
    have hv_eq : v = c := le_antisymm hvc hcv
    subst v
    exact xSubCubicQuadraticSplits_of_middle_quadratic_roots_at_right_endpoint
      hab hbu huv hc0 hμ

/-- Strict nonordinary subcase of the normalized cubic/quadratic leaf where the
upper quadratic root lies strictly to the right of the upper cubic root.  This
version assumes the lower quadratic root lies strictly below `c`; the boundary
`u = c` factors through the lower-degree cubic terminal. -/
lemma xSubCubicQuadraticSplits_of_right_quadratic_root_strict
    {a b c u v μ : ℝ} (hab : a ≤ b) (hbu : b < u) (huc : u < c)
    (hcv : c < v) (hv0 : v < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hau : a < u := lt_of_le_of_lt hab hbu
  have hbv : b < v := lt_trans hbu (lt_trans huc hcv)
  have hav : a < v := lt_of_le_of_lt hab hbv
  have hu0 : u < 0 := lt_trans (lt_trans huc hcv) hv0
  have hcu_pos : 0 < c - u := sub_pos.mpr huc
  have hcv_neg : c - v < 0 := sub_neg.mpr hcv
  have hP_b_neg : P.eval b < 0 := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hG : 0 < (b - u) * (b - v) := by
      exact mul_pos_of_neg_of_neg (sub_neg.mpr hbu) (sub_neg.mpr hbv)
    nlinarith [mul_pos hμ hG]
  have hP_u_pos : 0 < P.eval u := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_pos : 0 < u - b := sub_pos.mpr hbu
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 := by
      have h12 : 0 < (u - a) * (u - b) := mul_pos hua_pos hub_pos
      exact mul_neg_of_pos_of_neg h12 huc_neg
    have hH_pos : 0 < u * ((u - a) * (u - b) * (u - c)) :=
      mul_pos_of_neg_of_neg hu0 hprod_neg
    nlinarith
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hG_neg : (c - u) * (c - v) < 0 :=
      mul_neg_of_pos_of_neg hcu_pos hcv_neg
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hvb_pos : 0 < v - b := sub_pos.mpr hbv
    have hvc_pos : 0 < v - c := sub_pos.mpr hcv
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) := by
      exact mul_pos (mul_pos hva_pos hvb_pos) hvc_pos
    have hH_neg : v * ((v - a) * (v - b) * (v - c)) < 0 :=
      mul_neg_of_neg_of_pos hv0 hprod_pos
    nlinarith
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hG : 0 < (0 - u) * (0 - v) := by exact mul_pos (sub_pos.mpr hu0) (sub_pos.mpr hv0)
    nlinarith [mul_pos hμ hG]
  have ht_bot : Tendsto (fun x => P.eval x) atBot atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicQuadratic_atBot_atTop a b c u v μ
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicQuadratic_atTop_atTop a b c u v μ
  obtain ⟨rL, hrL_le, hrL_root⟩ :=
    exists_isRoot_le_of_eval_nonpos_of_tendsto_atBot_atTop (le_of_lt hP_b_neg) ht_bot
  obtain ⟨r₁, hb_r₁, hr₁_u, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hbu (mul_neg_of_neg_of_pos hP_b_neg hP_u_pos)
  obtain ⟨r₂, hc_r₂, hr₂_v, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hcv (mul_neg_of_pos_of_neg hP_c_pos hP_v_neg)
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop (le_of_lt hP_zero_neg) ht_top
  have hL1 : rL < r₁ := lt_of_le_of_lt hrL_le hb_r₁
  have h12 : r₁ < r₂ := lt_trans hr₁_u (lt_trans huc hc_r₂)
  have h2R : r₂ < rR := lt_of_lt_of_le (lt_trans hr₂_v hv0) hrR_ge
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicQuadratic_ne_zero a b c u v μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicQuadratic]
  have hsplits := splits_of_four_ordered_roots_of_natDegree_le
    hP_ne hdeg_le hL1 h12 h2R hrL_root hr₁_root hr₂_root hrR_root
  simpa [P] using hsplits

/-- Boundary case of the right-root quartic leaf when the lower quadratic root
is the upper cubic root.  Factoring out `X - c` reduces again to the normalized
quadratic/linear cubic-discriminant terminal. -/
lemma xSubCubicQuadraticSplits_of_right_quadratic_root_lower_at_endpoint
    {a b c v μ : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcv : c < v)
    (hv0 : v ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C c) * (X - C v))).Splits := by
  let Q : ℝ[X] := X * ((X - C a) * (X - C b)) - C μ * (X - C v)
  have hav : a ≤ v := (hab.trans hbc).trans (le_of_lt hcv)
  have hb0 : b ≤ 0 := (hbc.trans (le_of_lt hcv)).trans hv0
  have hQ_deg : Q.natDegree ≤ 3 := by
    dsimp [Q]
    compute_degree
  have hQ_disc : 0 ≤ cubicDiscr Q := by
    dsimp [Q]
    exact xSubQuadraticLinearCubicDiscrimNonneg hab hav hb0 hv0 hμ
  have hQ_splits : Q.Splits :=
    splits_of_natDegree_le_three_cubicDiscr_nonneg hQ_deg hQ_disc
  have hfactor :
      X * ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C c) * (X - C v)) = (X - C c) * Q := by
    dsimp [Q]
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C c).mul hQ_splits

/-- Right-root subcase of the normalized cubic/quadratic leaf with `v < 0`.
This packages the strict interval proof with the `u = c` boundary
factorization. -/
lemma xSubCubicQuadraticSplits_of_right_quadratic_root_of_v_neg
    {a b c u v μ : ℝ} (hab : a ≤ b) (hbu : b < u) (huc : u ≤ c)
    (hcv : c < v) (hv0 : v < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  by_cases hu_lt : u < c
  · exact xSubCubicQuadraticSplits_of_right_quadratic_root_strict
      hab hbu hu_lt hcv hv0 hμ
  · have hcu : c ≤ u := le_of_not_gt hu_lt
    have hu_eq : u = c := le_antisymm huc hcu
    subst u
    have hbc : b ≤ c := le_of_lt hbu
    exact xSubCubicQuadraticSplits_of_right_quadratic_root_lower_at_endpoint
      hab hbc hcv (le_of_lt hv0) hμ

/-- Boundary case of the right-root quartic leaf when the upper quadratic root
is zero and the lower quadratic root is strictly below `c`.  Factoring out `X`
leaves a monic cubic, which has three real roots by interval sign changes. -/
lemma xSubCubicQuadraticSplits_of_right_quadratic_root_at_zero_strict
    {a b c u μ : ℝ} (hab : a ≤ b) (hbu : b < u) (huc : u < c)
    (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * X)).Splits := by
  let R : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)
  have hau : a < u := lt_of_le_of_lt hab hbu
  have hR_a_pos : 0 < R.eval a := by
    dsimp [R]
    simp only [eval_sub, eval_mul, eval_X, eval_C]
    nlinarith [mul_pos hμ (sub_pos.mpr hau)]
  have hR_b_pos : 0 < R.eval b := by
    dsimp [R]
    simp only [eval_sub, eval_mul, eval_X, eval_C]
    nlinarith [mul_pos hμ (sub_pos.mpr hbu)]
  have hR_u_neg : R.eval u < 0 := by
    dsimp [R]
    simp only [eval_sub, eval_mul, eval_X, eval_C]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_pos : 0 < u - b := sub_pos.mpr hbu
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hprod_neg : (u - a) * (u - b) * (u - c) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hua_pos hub_pos) huc_neg
    nlinarith
  have hR_c_neg : R.eval c < 0 := by
    dsimp [R]
    simp only [eval_sub, eval_mul, eval_X, eval_C]
    nlinarith [mul_pos hμ (sub_pos.mpr huc)]
  have hR_deg : R.natDegree = 3 := by
    dsimp [R]
    exact natDegree_cubicSubLinear a b c u μ
  have ht_bot : Tendsto (fun x => R.eval x) atBot atBot := by
    dsimp [R]
    exact tendsto_eval_cubicSubLinear_atBot_atBot a b c u μ
  have ht_top : Tendsto (fun x => R.eval x) atTop atTop := by
    dsimp [R]
    exact tendsto_eval_cubicSubLinear_atTop_atTop a b c u μ
  obtain ⟨rL, hrL_le, hrL_root⟩ :=
    exists_isRoot_le_of_eval_nonneg_of_tendsto_atBot_atBot (le_of_lt hR_a_pos) ht_bot
  obtain ⟨r₁, hb_r₁, hr₁_u, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hbu (mul_neg_of_pos_of_neg hR_b_pos hR_u_neg)
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop (le_of_lt hR_c_neg) ht_top
  have hL1 : rL < r₁ := lt_of_le_of_lt (hrL_le.trans hab) hb_r₁
  have h1R : r₁ < rR := lt_of_lt_of_le (lt_trans hr₁_u huc) hrR_ge
  have hR_ne : R ≠ 0 := by
    dsimp [R]
    exact cubicSubLinear_ne_zero a b c u μ
  have hdeg_le : R.natDegree ≤ [rL, r₁, rR].length := by
    rw [hR_deg]
    norm_num
  have hR_splits := splits_of_three_ordered_roots_of_natDegree_le
    hR_ne (by simpa using hdeg_le) hL1 h1R hrL_root hr₁_root hrR_root
  have hfactor :
      X * ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * X) = X * R := by
    dsimp [R]
    ring
  rw [hfactor]
  exact Polynomial.Splits.X.mul hR_splits

/-- Corner case of the right-root quartic leaf when the quadratic roots are
`c` and `0`.  After factoring out `X * (X - c)`, the remaining monic quadratic
minus a positive constant splits. -/
lemma xSubCubicQuadraticSplits_of_right_quadratic_root_at_zero_lower_at_endpoint
    {a b c μ : ℝ} (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C c) * X)).Splits := by
  let Q : ℝ[X] := ((X - C a) * (X - C b)) - C μ
  have hQ_splits : Q.Splits := by
    dsimp [Q]
    exact quadraticSubConst_splits a b μ hμ
  have hfactor :
      X * ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C c) * X) = X * ((X - C c) * Q) := by
    dsimp [Q]
    ring
  rw [hfactor]
  exact Polynomial.Splits.X.mul ((Polynomial.Splits.X_sub_C c).mul hQ_splits)

/-- Boundary case of the right-root quartic leaf when the upper quadratic root
is zero.  This packages the strict cubic-factor proof with the `u = c`
corner factorization. -/
lemma xSubCubicQuadraticSplits_of_right_quadratic_root_at_zero
    {a b c u μ : ℝ} (hab : a ≤ b) (hbu : b < u) (huc : u ≤ c)
    (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * X)).Splits := by
  by_cases hu_lt : u < c
  · exact xSubCubicQuadraticSplits_of_right_quadratic_root_at_zero_strict
      hab hbu hu_lt hμ
  · have hcu : c ≤ u := le_of_not_gt hu_lt
    have hu_eq : u = c := le_antisymm huc hcu
    subst u
    exact xSubCubicQuadraticSplits_of_right_quadratic_root_at_zero_lower_at_endpoint
      hμ

/-- Complete nonordinary branch where the lower quadratic root lies strictly to
the right of the middle cubic root `b`. -/
lemma xSubCubicQuadraticSplits_of_lower_quadratic_root_right
    {a b c u v μ : ℝ} (hab : a ≤ b) (hbu : b < u) (huv : u ≤ v)
    (huc : u ≤ c) (hc0 : c ≤ 0) (hv0 : v ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  by_cases hvc : v ≤ c
  · exact xSubCubicQuadraticSplits_of_middle_quadratic_roots
      hab hbu huv hvc hc0 hμ
  · have hcv : c < v := lt_of_not_ge hvc
    by_cases hv_lt : v < 0
    · exact xSubCubicQuadraticSplits_of_right_quadratic_root_of_v_neg
        hab hbu huc hcv hv_lt hμ
    · have h0v : 0 ≤ v := le_of_not_gt hv_lt
      have hv_eq : v = 0 := le_antisymm hv0 h0v
      subst v
      simpa using xSubCubicQuadraticSplits_of_right_quadratic_root_at_zero
        hab hbu huc hμ

/-- Boundary case of the upper-root-right quartic leaf when the lower quadratic
root is the lower cubic root.  Factoring out `X - a` reduces the claim to the
normalized quadratic/linear cubic-discriminant terminal. -/
lemma xSubCubicQuadraticSplits_of_lower_quadratic_root_at_left_endpoint
    {a b c v μ : ℝ} (hbc : b ≤ c) (hcv : c < v) (hv0 : v ≤ 0)
    (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C a) * (X - C v))).Splits := by
  let Q : ℝ[X] := X * ((X - C b) * (X - C c)) - C μ * (X - C v)
  have hbv : b ≤ v := hbc.trans (le_of_lt hcv)
  have hc0 : c ≤ 0 := (le_of_lt hcv).trans hv0
  have hQ_deg : Q.natDegree ≤ 3 := by
    dsimp [Q]
    compute_degree
  have hQ_disc : 0 ≤ cubicDiscr Q := by
    dsimp [Q]
    exact xSubQuadraticLinearCubicDiscrimNonneg hbc hbv hc0 hv0 hμ
  have hQ_splits : Q.Splits :=
    splits_of_natDegree_le_three_cubicDiscr_nonneg hQ_deg hQ_disc
  have hfactor :
      X * ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C a) * (X - C v)) = (X - C a) * Q := by
    dsimp [Q]
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C a).mul hQ_splits

/-- Boundary case of the upper-root-right quartic leaf when the lower quadratic
root is the middle cubic root.  Factoring out `X - b` reduces the claim to the
normalized quadratic/linear cubic-discriminant terminal. -/
lemma xSubCubicQuadraticSplits_of_lower_quadratic_root_at_middle_endpoint
    {a b c v μ : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcv : c < v)
    (hv0 : v ≤ 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C b) * (X - C v))).Splits := by
  let Q : ℝ[X] := X * ((X - C a) * (X - C c)) - C μ * (X - C v)
  have hac : a ≤ c := hab.trans hbc
  have hav : a ≤ v := hac.trans (le_of_lt hcv)
  have hc0 : c ≤ 0 := (le_of_lt hcv).trans hv0
  have hQ_deg : Q.natDegree ≤ 3 := by
    dsimp [Q]
    compute_degree
  have hQ_disc : 0 ≤ cubicDiscr Q := by
    dsimp [Q]
    exact xSubQuadraticLinearCubicDiscrimNonneg hac hav hc0 hv0 hμ
  have hQ_splits : Q.Splits :=
    splits_of_natDegree_le_three_cubicDiscr_nonneg hQ_deg hQ_disc
  have hfactor :
      X * ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C b) * (X - C v)) = (X - C b) * Q := by
    dsimp [Q]
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C b).mul hQ_splits

/-- Strict nonordinary subcase where the lower quadratic root lies between
`a` and `b`, and the upper quadratic root lies strictly to the right of `c`.
The proof again finds four distinct roots from sign changes. -/
lemma xSubCubicQuadraticSplits_of_upper_quadratic_root_right_strict
    {a b c u v μ : ℝ} (hau : a < u) (hub : u < b) (hbc : b ≤ c)
    (hcv : c < v) (hv0 : v < 0) (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  let P : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))
  have hav : a < v := lt_trans hau (lt_trans hub (lt_of_le_of_lt hbc hcv))
  have huc : u < c := lt_of_lt_of_le hub hbc
  have hu0 : u < 0 := lt_trans (lt_trans huc hcv) hv0
  have hP_a_neg : P.eval a < 0 := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hG : 0 < (a - u) * (a - v) := by
      exact mul_pos_of_neg_of_neg (sub_neg.mpr hau) (sub_neg.mpr hav)
    nlinarith [mul_pos hμ hG]
  have hP_u_neg : P.eval u < 0 := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    have hprod_pos : 0 < (u - a) * (u - b) * (u - c) := by
      exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hua_pos hub_neg) huc_neg
    nlinarith [mul_neg_of_neg_of_pos hu0 hprod_pos]
  have hP_b_pos : 0 < P.eval b := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hbv : b < v := lt_of_le_of_lt hbc hcv
    have hG_neg : (b - u) * (b - v) < 0 := by
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hub) (sub_neg.mpr hbv)
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_c_pos : 0 < P.eval c := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hG_neg : (c - u) * (c - v) < 0 := by
      exact mul_neg_of_pos_of_neg (sub_pos.mpr huc) (sub_neg.mpr hcv)
    nlinarith [mul_pos hμ (neg_pos.mpr hG_neg)]
  have hP_v_neg : P.eval v < 0 := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hvb_pos : 0 < v - b := sub_pos.mpr (lt_of_le_of_lt hbc hcv)
    have hvc_pos : 0 < v - c := sub_pos.mpr hcv
    have hva_pos : 0 < v - a := sub_pos.mpr hav
    have hprod_pos : 0 < (v - a) * (v - b) * (v - c) := by
      exact mul_pos (mul_pos hva_pos hvb_pos) hvc_pos
    nlinarith [mul_neg_of_neg_of_pos hv0 hprod_pos]
  have hP_zero_neg : P.eval 0 < 0 := by
    dsimp [P]
    rw [eval_xSubCubicQuadratic]
    have hG : 0 < (0 - u) * (0 - v) := by exact mul_pos (sub_pos.mpr hu0) (sub_pos.mpr hv0)
    nlinarith [mul_pos hμ hG]
  have ht_bot : Tendsto (fun x => P.eval x) atBot atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicQuadratic_atBot_atTop a b c u v μ
  have ht_top : Tendsto (fun x => P.eval x) atTop atTop := by
    dsimp [P]
    exact tendsto_eval_xSubCubicQuadratic_atTop_atTop a b c u v μ
  obtain ⟨rL, hrL_le, hrL_root⟩ :=
    exists_isRoot_le_of_eval_nonpos_of_tendsto_atBot_atTop (le_of_lt hP_a_neg) ht_bot
  obtain ⟨r₁, hu_r₁, hr₁_b, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hub (mul_neg_of_neg_of_pos hP_u_neg hP_b_pos)
  obtain ⟨r₂, hc_r₂, hr₂_v, hr₂_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hcv (mul_neg_of_pos_of_neg hP_c_pos hP_v_neg)
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop (le_of_lt hP_zero_neg) ht_top
  have hL1 : rL < r₁ := lt_of_le_of_lt (hrL_le.trans (le_of_lt hau)) hu_r₁
  have h12 : r₁ < r₂ := lt_trans (lt_of_lt_of_le hr₁_b hbc) hc_r₂
  have h2R : r₂ < rR := lt_of_lt_of_le (lt_trans hr₂_v hv0) hrR_ge
  have hP_ne : P ≠ 0 := by
    dsimp [P]
    exact xSubCubicQuadratic_ne_zero a b c u v μ
  have hdeg_le : P.natDegree ≤ 4 := by
    dsimp [P]
    rw [natDegree_xSubCubicQuadratic]
  have hsplits := splits_of_four_ordered_roots_of_natDegree_le
    hP_ne hdeg_le hL1 h12 h2R hrL_root hr₁_root hr₂_root hrR_root
  simpa [P] using hsplits

/-- Boundary case of the upper-root-right quartic leaf when the upper
quadratic root is zero and the lower quadratic root lies strictly between
`a` and `b`.  After factoring out `X`, the cubic factor splits by three
interval roots. -/
lemma xSubCubicQuadraticSplits_of_upper_quadratic_root_at_zero_strict
    {a b c u μ : ℝ} (hau : a < u) (hub : u < b) (hbc : b ≤ c)
    (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * X)).Splits := by
  let R : ℝ[X] :=
    ((X - C a) * (X - C b) * (X - C c)) - C μ * (X - C u)
  have huc : u < c := lt_of_lt_of_le hub hbc
  have hR_a_pos : 0 < R.eval a := by
    dsimp [R]
    rw [eval_cubicSubLinear]
    nlinarith [mul_pos hμ (sub_pos.mpr hau)]
  have hR_u_pos : 0 < R.eval u := by
    dsimp [R]
    rw [eval_cubicSubLinear, sub_self, mul_zero, sub_zero]
    have hua_pos : 0 < u - a := sub_pos.mpr hau
    have hub_neg : u - b < 0 := sub_neg.mpr hub
    have huc_neg : u - c < 0 := sub_neg.mpr huc
    exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hua_pos hub_neg) huc_neg
  have hR_b_neg : R.eval b < 0 := by
    dsimp [R]
    rw [eval_cubicSubLinear]
    nlinarith [mul_pos hμ (sub_pos.mpr hub)]
  have hR_c_neg : R.eval c < 0 := by
    dsimp [R]
    rw [eval_cubicSubLinear]
    nlinarith [mul_pos hμ (sub_pos.mpr huc)]
  have hR_deg : R.natDegree = 3 := by
    dsimp [R]
    exact natDegree_cubicSubLinear a b c u μ
  have ht_bot : Tendsto (fun x => R.eval x) atBot atBot := by
    dsimp [R]
    exact tendsto_eval_cubicSubLinear_atBot_atBot a b c u μ
  have ht_top : Tendsto (fun x => R.eval x) atTop atTop := by
    dsimp [R]
    exact tendsto_eval_cubicSubLinear_atTop_atTop a b c u μ
  obtain ⟨rL, hrL_le, hrL_root⟩ :=
    exists_isRoot_le_of_eval_nonneg_of_tendsto_atBot_atBot (le_of_lt hR_a_pos) ht_bot
  obtain ⟨r₁, hu_r₁, hr₁_b, hr₁_root⟩ :=
    exists_isRoot_between_of_eval_mul_neg hub (mul_neg_of_pos_of_neg hR_u_pos hR_b_neg)
  obtain ⟨rR, hrR_ge, hrR_root⟩ :=
    exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop (le_of_lt hR_c_neg) ht_top
  have hL1 : rL < r₁ := lt_of_le_of_lt (hrL_le.trans (le_of_lt hau)) hu_r₁
  have h1R : r₁ < rR := lt_of_lt_of_le (lt_of_lt_of_le hr₁_b hbc) hrR_ge
  have hR_ne : R ≠ 0 := by
    dsimp [R]
    exact cubicSubLinear_ne_zero a b c u μ
  have hdeg_le : R.natDegree ≤ [rL, r₁, rR].length := by
    rw [hR_deg]
    norm_num
  have hR_splits := splits_of_three_ordered_roots_of_natDegree_le
    hR_ne (by simpa using hdeg_le) hL1 h1R hrL_root hr₁_root hrR_root
  have hfactor :
      X * ((X - C a) * (X - C b) * (X - C c)) -
        C μ * ((X - C u) * X) = X * R := by
    dsimp [R]
    ring
  rw [hfactor]
  exact Polynomial.Splits.X.mul hR_splits

/-- Complete nonordinary branch where the lower quadratic root is at or to the
left of the middle cubic root while the upper quadratic root lies to the right
of the upper cubic root. -/
lemma xSubCubicQuadraticSplits_of_upper_quadratic_root_right
    {a b c u v μ : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hau : a ≤ u) (hub : u ≤ b) (hcv : c < v) (hv0 : v ≤ 0)
    (hμ : 0 < μ) :
    (X * ((X - C a) * (X - C b) * (X - C c)) -
      C μ * ((X - C u) * (X - C v))).Splits := by
  by_cases hau_lt : a < u
  · by_cases hub_lt : u < b
    · by_cases hv_lt : v < 0
      · exact xSubCubicQuadraticSplits_of_upper_quadratic_root_right_strict
          hau_lt hub_lt hbc hcv hv_lt hμ
      · have h0v : 0 ≤ v := le_of_not_gt hv_lt
        have hv_eq : v = 0 := le_antisymm hv0 h0v
        subst v
        simpa using xSubCubicQuadraticSplits_of_upper_quadratic_root_at_zero_strict
          hau_lt hub_lt hbc hμ
    · have hbu : b ≤ u := le_of_not_gt hub_lt
      have hu_eq : u = b := le_antisymm hub hbu
      subst u
      exact xSubCubicQuadraticSplits_of_lower_quadratic_root_at_middle_endpoint
        hab hbc hcv hv0 hμ
  · have hua : u ≤ a := le_of_not_gt hau_lt
    have hu_eq : u = a := le_antisymm hua hau
    subst u
    exact xSubCubicQuadraticSplits_of_lower_quadratic_root_at_left_endpoint
      hbc hcv hv0 hμ

/-- The normalized monic cubic/quadratic x-subtraction leaf. -/
theorem xSubCubicQuadraticSplits : xSubCubicQuadraticSplitsStatement := by
  intro a b c u v μ hab hbc huv hau hbv huc hc0 hv0 hμ
  by_cases hub : u ≤ b
  · by_cases hvc : v ≤ c
    · exact xSubCubicQuadraticSplits_of_interlacing_roots
        hab hbc huv hau hub hbv hvc hμ
    · have hcv : c < v := lt_of_not_ge hvc
      exact xSubCubicQuadraticSplits_of_upper_quadratic_root_right
        hab hbc hau hub hcv hv0 hμ
  · have hbu : b < u := lt_of_not_ge hub
    exact xSubCubicQuadraticSplits_of_lower_quadratic_root_right
      hab hbu huv huc hc0 hv0 hμ

end LiuOppositeSigns
end RealRooted
