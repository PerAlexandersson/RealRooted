module

import RealRooted.MaWang.Weak.Endpoint
import RealRooted.Linear
public import RealRooted.Basic.ProperPosition

/-!
# Quadratic-seed derivative recurrences

Strict interlacing of the first two rows `1 + X`, `1 + u X + X ^ 2` of a recurrence with a
quadratic seed.  The later rows are covered by the first-order derivative recurrence theorems
applied to the shifted sequence `fun m => P (m + 2)`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

lemma strictInterl_one_add_X_quadratic_of_two_le (u : ℝ) (hu : 2 ≤ u) :
    StrictInterl (1 + X : ℝ[X]) (1 + X * C u + X ^ 2) := by
  have hInter : Interlaces (1 : ℝ[X]) (1 + X) :=
    interlaces_one_linear (p := 1 + X) (by compute_degree!)
  have hg_pos : HasPosLeadingCoeff (1 : ℝ[X]) := by
    norm_num [HasPosLeadingCoeff, leadingCoeff]
  have hF_eq :
      (1 + X) * (1 + X) + (C (u - 2) * X) * (1 : ℝ[X]) =
        1 + X * C u + X ^ 2 := by
    apply Polynomial.funext
    intro r
    simp only [eval_add, eval_mul, eval_one, eval_X, eval_C, eval_pow]
    ring
  have hF_pos :
      HasPosLeadingCoeff ((1 + X) * (1 + X) + (C (u - 2) * X) * (1 : ℝ[X])) := by
    rw [hF_eq]
    rw [HasPosLeadingCoeff, leadingCoeff,
      show (1 + X * C u + X ^ 2 : ℝ[X]).natDegree = 2 by compute_degree!]
    norm_num [coeff_add, coeff_C_mul, coeff_X, coeff_X_pow, coeff_one]
  have hdeg_lo :
      (1 + X : ℝ[X]).natDegree ≤
        ((1 + X) * (1 + X) + (C (u - 2) * X) * (1 : ℝ[X])).natDegree := by
    rw [hF_eq]
    norm_num [show (1 + X : ℝ[X]).natDegree = 1 by compute_degree!,
      show (1 + C u * X + X ^ 2 : ℝ[X]).natDegree = 2 by compute_degree!]
  have hdeg_hi :
      ((1 + X) * (1 + X) + (C (u - 2) * X) * (1 : ℝ[X])).natDegree ≤
        (1 + X : ℝ[X]).natDegree + 1 := by
    rw [hF_eq]
    norm_num [show (1 + X : ℝ[X]).natDegree = 1 by compute_degree!,
      show (1 + C u * X + X ^ 2 : ℝ[X]).natDegree = 2 by compute_degree!]
  have hb_nonpos : ∀ r, (1 + X : ℝ[X]).IsRoot r →
      (C (u - 2) * X : ℝ[X]).eval r ≤ 0 := by
    intro r hr
    have hr' : r = -1 := by
      change (1 + X : ℝ[X]).eval r = 0 at hr
      simp only [eval_add, eval_one, eval_X] at hr
      grind
    simp_all
  have := strictInterl_of_interlaces_evalCoeff_nonpos
    (f := (1 + X : ℝ[X])) (g := (1 : ℝ[X]))
    (a := 1 + X) (b := C (u - 2) * X)
    hInter hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
  simp_all

end RealRooted
