module

import RealRooted.CoefficientShape
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Newton inequalities for splitting real cubics

The two coefficient-wise Newton inequalities for a real polynomial of degree at most three
that is zero or splits over `ℝ`, as the level-`3` case of
`RealRooted.coeffUltraLogConcaveUpTo_of_natDegree_le`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Newton's adjacent coefficient inequalities for a real polynomial of degree
at most three that is zero or splits: the level-`3` ultra-log-concavity
inequalities `coeffUltraLogConcaveUpTo_of_natDegree_le` at `k = 1, 2`. -/
theorem three_mul_coeff_newton_of_natDegree_le_three
    {p : ℝ[X]} (hdeg : p.natDegree ≤ 3) (hs : p = 0 ∨ p.Splits) :
    3 * (p.coeff 0 * p.coeff 2) ≤ p.coeff 1 ^ 2 ∧
      3 * (p.coeff 1 * p.coeff 3) ≤ p.coeff 2 ^ 2 := by
  have h := coeffUltraLogConcaveUpTo_of_natDegree_le hdeg hs
  have h1 := h 1 (by norm_num) (by norm_num)
  have h2 := h 2 (by norm_num) (by norm_num)
  norm_num at h1 h2
  constructor <;> linarith

/-- Jensen-normalized cubic log-concavity from splitting of a polynomial whose
coefficients are the binomially weighted `gᵢ`. -/
theorem jensen_three_logConcave_of_natDegree_le_three
    {p : ℝ[X]} {g0 g1 g2 g3 : ℝ}
    (hdeg : p.natDegree ≤ 3) (hs : p = 0 ∨ p.Splits)
    (h0 : p.coeff 0 = g0) (h1 : p.coeff 1 = 3 * g1)
    (h2 : p.coeff 2 = 3 * g2) (h3 : p.coeff 3 = g3) :
    g0 * g2 ≤ g1 ^ 2 ∧ g1 * g3 ≤ g2 ^ 2 := by
  obtain ⟨hleft, hright⟩ := three_mul_coeff_newton_of_natDegree_le_three hdeg hs
  rw [h0, h1, h2] at hleft
  rw [h1, h2, h3] at hright
  exact ⟨by linarith [hleft], by linarith [hright]⟩

end RealRooted
