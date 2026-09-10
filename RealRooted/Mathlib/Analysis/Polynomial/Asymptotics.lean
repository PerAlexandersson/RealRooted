import Mathlib.Analysis.Polynomial.Basic

/-!
# Asymptotics of polynomial evaluations

This file records asymptotic consequences for polynomial evaluations along
natural arguments.
-/

open Filter

namespace Polynomial

/-- Evaluations of a nonzero real polynomial at two fixed translates of the
natural numbers have ratio tending to one. -/
theorem tendsto_eval_nat_add_div {p : ℝ[X]} (hp : p ≠ 0) (u v : ℝ) :
    Tendsto (fun n : ℕ => p.eval ((n : ℝ) + u) / p.eval ((n : ℝ) + v))
      atTop (nhds 1) := by
  have hu : 0 < (X + C u : ℝ[X]).degree := by simp
  have hv : 0 < (X + C v : ℝ[X]).degree := by simp
  have hdeg : (p.comp (X + C u)).degree = (p.comp (X + C v)).degree := by
    rw [degree_comp hu, degree_comp hv]
    simp
  have h := div_tendsto_atTop_leadingCoeff_div_of_degree_eq
    (p.comp (X + C u)) (p.comp (X + C v)) hdeg
  have hnat := h.comp tendsto_natCast_atTop_atTop
  convert hnat using 1 <;>
    simp [Function.comp_def, eval_comp, leadingCoeff_comp, hp]

/-- Evaluations of a nonzero real polynomial at two fixed natural-number
offsets below the argument have ratio tending to one. -/
theorem tendsto_eval_nat_sub_div {p : ℝ[X]} (hp : p ≠ 0) (c d : ℕ) :
    Tendsto (fun n : ℕ => p.eval ((n - c : ℕ) : ℝ) /
      p.eval ((n - d : ℕ) : ℝ)) atTop (nhds 1) := by
  apply (tendsto_eval_nat_add_div hp (-(c : ℝ)) (-(d : ℝ))).congr'
  filter_upwards [eventually_ge_atTop c, eventually_ge_atTop d] with n hcn hdn
  rw [Nat.cast_sub hcn, Nat.cast_sub hdn]
  congr 1

end Polynomial
