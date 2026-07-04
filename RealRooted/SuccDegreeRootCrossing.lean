import RealRooted.Basic
import Mathlib.Tactic

/-!
# Succ-degree root crossing

This module records a small checked base case for the succ-degree
root-crossing target and a concrete warning example for the stronger fixed
orientation route.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Degree-one analytic core of the succ-degree root-crossing target.

For a linear factor with root `α` and a quadratic with ordered roots
`γ ≤ β`, if every strictly positive linear combination is real-rooted, then
the smaller quadratic root lies to the left of the linear root. -/
theorem root_le_of_posCombo_deg1
    {α β γ : ℝ} (hβγ : γ ≤ β)
    (hsplit : ∀ lam μ : ℝ, 0 < lam → 0 < μ →
      (C lam * (X - C α) + C μ * ((X - C β) * (X - C γ))).Splits) :
    γ ≤ α := by
  contrapose! hsplit
  refine ⟨β + γ - 2 * α, 1, ?_, ?_, ?_⟩ <;> try linarith
  rw [Polynomial.splits_iff_card_roots]
  erw [Polynomial.natDegree_add_eq_right_of_natDegree_lt]
  · erw [Polynomial.natDegree_C_mul] <;> norm_num
    erw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _)
        (Polynomial.X_sub_C_ne_zero _), Polynomial.natDegree_X_sub_C,
      Polynomial.natDegree_X_sub_C]
    exact ne_of_lt
      (lt_of_le_of_lt
        (Multiset.card_le_card <|
          show Polynomial.roots _ ≤ 0 from by
            exact Multiset.le_zero.mpr <| by
              exact Multiset.eq_zero_of_forall_notMem fun r hr => by
                norm_num at hr
                nlinarith [sq_nonneg (r - α)])
        (by norm_num))
  · rw [Polynomial.natDegree_C_mul, Polynomial.natDegree_C_mul] <;> norm_num
    · rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _)
        (Polynomial.X_sub_C_ne_zero _), Polynomial.natDegree_X_sub_C,
        Polynomial.natDegree_X_sub_C]
      norm_num
    · linarith

/-- Every strictly positive combination of `f = 2 * X + 1` and
`g = (X + 1) * (X + 2)` is real-rooted.

The example is useful because the root `-1 / 2` of `f` lies to the right of
both roots of `g`; positive-combination real-rootedness alone does not force
the fixed succ-degree orientation `Prec f g`. -/
theorem posCombo_deg1_all_splits :
    ∀ lam μ : ℝ, 0 < lam → 0 < μ →
      (C lam * (C 2 * X + C 1) + C μ * ((X + C 1) * (X + C 2))).Splits := by
  intro lam μ hlam hμ
  have h_discriminant : (2 * lam + 3 * μ)^2 - 4 * μ * (lam + 2 * μ) > 0 := by
    nlinarith
  rw [Polynomial.splits_iff_card_roots]
  rw [show
      C lam * (C 2 * X + C 1) + C μ * ((X + C 1) * (X + C 2)) =
        C μ *
          ((X -
              C ((-(2 * lam + 3 * μ) +
                    Real.sqrt ((2 * lam + 3 * μ)^2 - 4 * μ * (lam + 2 * μ))) /
                  (2 * μ))) *
            (X -
              C ((-(2 * lam + 3 * μ) -
                    Real.sqrt ((2 * lam + 3 * μ)^2 - 4 * μ * (lam + 2 * μ))) /
                  (2 * μ)))) from ?_]
  · rw [Polynomial.roots_mul, Polynomial.roots_mul]
    · rw [Polynomial.natDegree_mul', Polynomial.natDegree_mul'] <;> aesop
    · exact mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _)
    · exact mul_ne_zero (Polynomial.C_ne_zero.mpr hμ.ne')
        (mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _))
  · refine Polynomial.funext fun x => ?_
    norm_num
    ring_nf
    norm_num [hμ.ne', hlam.ne']
    ring_nf
    grind

private lemma roots_X_add_one_mul_X_add_two_le_neg_one :
    ∀ r ∈ (((X + C 1) * (X + C 2) : ℝ[X]).roots), r ≤ -1 := by
  intro r hr
  rw [Polynomial.mem_roots] at hr
  · norm_num at hr ⊢
    rcases hr with hr | hr <;> linarith
  · exact mul_ne_zero (by simpa using Polynomial.X_add_C_ne_zero (1 : ℝ))
      (by simpa using Polynomial.X_add_C_ne_zero (2 : ℝ))

private lemma neg_half_mem_roots_two_mul_X_add_one :
    (-1 / 2 : ℝ) ∈ ((C 2 * X + C 1 : ℝ[X]).roots) := by
  rw [Polynomial.mem_roots]
  · norm_num
  · intro h
    have hc := congrArg (fun p : ℝ[X] => p.coeff 1) h
    norm_num [Polynomial.coeff_one] at hc

/-- The explicit positive-combination example is not in the fixed succ-degree
orientation `Prec f g`. -/
theorem not_prec_deg1_example :
    ¬ Prec (C 2 * X + C 1 : ℝ[X]) ((X + C 1) * (X + C 2)) := by
  intro hprec
  have hle : (-1 / 2 : ℝ) ≤ -1 :=
    roots_le_of_prec_right hprec roots_X_add_one_mul_X_add_two_le_neg_one
      (-1 / 2) neg_half_mem_roots_two_mul_X_add_one
  linarith

end RealRooted
