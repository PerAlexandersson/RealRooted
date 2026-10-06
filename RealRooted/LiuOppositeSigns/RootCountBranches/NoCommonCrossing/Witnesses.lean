import RealRooted.CommonInterleaver.RightPencil
import RealRooted.CommonInterleaver.SuccDegreeLowDegree
import RealRooted.LiuOppositeSigns
import RealRooted.LiuOppositeSigns.NoCommonRoots
import RealRooted.PositiveParameterLocalLowerCount
import RealRooted.RootContinuity
import RealRooted.RootCountLocalConstancy

/-!
# Crossing witnesses for Liu's no-common-root argument

This module contains the even-root x-subtraction witness and the
right-pencil crossing criteria for the odd upper root-count difference.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

theorem RootCountCompatible.exists_two_isRoot_between_X_mul_sub_C_mul_of_even_right_roots
    {p q : ℝ[X]} (hcount : RootCountCompatible p q)
    (hp_ne : p ≠ 0) (hq_ne : q ≠ 0)
    (hp : p.Splits) (hq : q.Splits)
    (hp_pos : 0 < p.leadingCoeff) (hq_pos : 0 < q.leadingCoeff)
    {a b y μ : ℝ} (hay : a < y) (hyb : y < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) (hy : q.IsRoot y)
    (hμ : 0 < μ) (hy_neg : y < 0)
    (hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z)
    (hqa : ¬ q.IsRoot a) (hqb : ¬ q.IsRoot b)
    (heven : Even (q.roots.filter (fun x => a < x ∧ x < b)).card) :
    ∃ c₁ c₂ : ℝ,
      a < c₁ ∧ c₁ < y ∧ y < c₂ ∧ c₂ < b ∧
        (X * p - C μ * q).IsRoot c₁ ∧ (X * p - C μ * q).IsRoot c₂ := by
  have hab : a < b := lt_trans hay hyb
  have htwo := two_le_card_roots_filter_Ioo_of_even_of_isRoot
    hq_ne hy hay hyb heven
  have hodd_a :=
    hcount.odd_card_roots_gt_add_of_left_no_isRoot_Ioo
      hp_ne hq_ne hab hp_no hqb htwo
  have hp_count_eq :
      (p.roots.filter (a < ·)).card = (p.roots.filter (y < ·)).card := by
    refine card_filter_lt_eq_of_no_mem_Ioc p.roots (le_of_lt hay) ?_
    intro r hr
    by_cases hra : r ≤ a
    · exact Or.inl hra
    · right
      by_contra hyr
      have har : a < r := lt_of_not_ge hra
      have hry : r ≤ y := le_of_not_gt hyr
      exact hp_no r har (lt_of_le_of_lt hry hyb)
        ((Polynomial.mem_roots hp_ne).mp hr)
  have hodd_y :
      Odd ((p.roots.filter (y < ·)).card +
        (q.roots.filter (a < ·)).card) := by
    simpa [hp_count_eq] using hodd_a
  have hp_not_y : ¬ p.IsRoot y := hp_no y hay hyb
  have hp_y_q_a_neg : p.eval y * q.eval a < 0 :=
    hp.eval_mul_eval_neg_of_odd_card_roots_gt_add
      hq hp_pos hq_pos hp_not_y hqa hodd_y
  have hq_a_p_y_neg : q.eval a * p.eval y < 0 := by simpa [mul_comm] using hp_y_q_a_neg
  exact exists_two_isRoot_between_X_mul_sub_C_mul_of_even_right_roots_left_sign
    hq_ne hq hay hyb ha hb hy hμ hy_neg heven hqb hq_a_p_y_neg

/-- Positive-split, no-common-root corollary for the even right-polynomial root
case.  The no-common-root hypothesis supplies the endpoint nonroot facts for
`q`, and nonnegative coefficients on the left polynomial force the interior
right-polynomial root `y` to be negative because it lies left of the right
left-polynomial endpoint `b`. -/
theorem
    PositiveSplitRootCountPair.exists_two_isRoot_between_X_mul_sub_C_mul_of_even_right_roots
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hp_nonneg : HasNonnegCoeffs p) (hno : NoCommonRoots p q)
    {a b y μ : ℝ} (hay : a < y) (hyb : y < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) (hy : q.IsRoot y)
    (hμ : 0 < μ)
    (hp_no : ∀ z : ℝ, a < z → z < b → ¬ p.IsRoot z)
    (heven : Even (q.roots.filter (fun x => a < x ∧ x < b)).card) :
    ∃ c₁ c₂ : ℝ,
      a < c₁ ∧ c₁ < y ∧ y < c₂ ∧ c₂ < b ∧
        (X * p - C μ * q).IsRoot c₁ ∧ (X * p - C μ * q).IsRoot c₂ := by
  have hy_neg : y < 0 :=
    lt_zero_of_lt_isRoot_of_hasNonnegCoeffs hp_nonneg hpair.left_pos.ne_zero hb hyb
  exact hpair.count.exists_two_isRoot_between_X_mul_sub_C_mul_of_even_right_roots
    hpair.left_pos.ne_zero hpair.right_pos.ne_zero
    hpair.left_splits hpair.right_splits hpair.left_pos hpair.right_pos
    hay hyb ha hb hy hμ hy_neg hp_no (hno a ha) (hno b hb) heven

/-- For splitting polynomials with opposite leading signs, odd upper
root-count difference at a common non-root is equivalent to the absence of a
positive right-pencil member through that threshold. -/
theorem OppositeLeadingSigns.odd_intCard_roots_gt_sub_iff_not_exists_pos_isRoot_add_right
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔
      ¬ ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  have hfx_eval : f.eval x ≠ 0 :=
    (Polynomial.not_isRoot_iff_eval_ne_zero f x).mp hxf
  have hgx_eval : g.eval x ≠ 0 :=
    (Polynomial.not_isRoot_iff_eval_ne_zero g x).mp hxg
  rw [hsgn.odd_intCard_roots_gt_sub_iff_eval_pos_iff hf hg hxf hxg]
  exact (not_exists_pos_isRoot_add_right_iff_eval_pos_iff hfx_eval hgx_eval).symm

/-- Contrapositive crossing form of
`OppositeLeadingSigns.odd_intCard_roots_gt_sub_iff_not_exists_pos_isRoot_add_right`. -/
theorem OppositeLeadingSigns.not_odd_intCard_roots_gt_sub_iff_exists_pos_isRoot_add_right
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hf : f.Splits) (hg : g.Splits)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x) :
    (¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card) ↔
      ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) := by
  simpa using
    (not_congr
      (hsgn.odd_intCard_roots_gt_sub_iff_not_exists_pos_isRoot_add_right
        hf hg hxf hxg))

/-- In a no-common positive-combination family with opposite leading signs,
failure of odd upper root-count difference at a common non-root gives the
unique positive right-pencil crossing through that threshold. -/
theorem OppositeLeadingSigns.exists_unique_pos_crossing_add_right_of_not_odd_intCard_roots_gt_sub
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (hfg : PosComboRealRooted f g) (hno : NoCommonRoots f g)
    (hf : f.Splits) (hg : g.Splits)
    {x : ℝ} (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hnot_odd : ¬ Odd (((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card)) :
    ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x ∧
      μ = -f.eval x / g.eval x ∧
      (f + C μ * g).derivative.eval x ≠ 0 ∧
      (∀ ν : ℝ, 0 < ν → (f + C ν * g).IsRoot x → ν = μ) := by
  have hcross :=
    (hsgn.not_odd_intCard_roots_gt_sub_iff_exists_pos_isRoot_add_right
      hf hg hxf hxg).mp hnot_odd
  have hfx_eval : f.eval x ≠ 0 :=
    (Polynomial.not_isRoot_iff_eval_ne_zero f x).mp hxf
  have hsign : f.eval x * g.eval x < 0 :=
    (exists_pos_isRoot_add_right_iff_eval_mul_neg hfx_eval).mp hcross
  exact hfg.exists_unique_pos_parameter_crossing_add_right_of_sign hno hsign

end LiuOppositeSigns
end RealRooted
