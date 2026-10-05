import RealRooted.Applications.OEIS.A144438.IntervalPreserver.ResidueAlgebra

/-!
# Differentiating the finite residue expansion

This is the direct rational-function substitute for differentiating the
arrowhead secular equation.  It will identify the positive successor residue
`p(ρ)/q'(ρ)` with the reciprocal squared norm of the root vector.
-/

open Polynomial BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS

/-- Evaluation of the derivative of a monic linear cofactor away from its
removed root. -/
theorem eval_derivative_divByMonic_X_sub_C
    {p : ℝ[X]} {r x : ℝ} (hr : p.IsRoot r) (hxr : x - r ≠ 0) :
    (p /ₘ (X - C r)).derivative.eval x =
      p.derivative.eval x / (x - r) - p.eval x / (x - r) ^ 2 := by
  have hfactor := mul_divByMonic_eq_iff_isRoot.mpr hr
  have hfactorEval := congrArg (Polynomial.eval x) hfactor
  simp only [eval_mul, eval_sub, eval_X, eval_C] at hfactorEval
  have hderivative :=
    Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative p r
  have hderivativeEval := congrArg (Polynomial.eval x) hderivative
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C] at hderivativeEval
  have hcofactor : (p /ₘ (X - C r)).eval x = p.eval x / (x - r) := by
    rw [eq_div_iff hxr]
    simpa only [mul_comm] using hfactorEval
  rw [hcofactor] at hderivativeEval
  field_simp [hxr] at hderivativeEval ⊢
  linarith

/-- Differentiating the Lagrange residue expansion at a point outside the
roots of the denominator. -/
theorem eval_derivative_eq_residue_sums
    {p h : ℝ[X]} (hp : p.Splits) (hpnd : p.roots.Nodup)
    (hpdeg : 1 ≤ p.natDegree) (hhdeg : h.degree < p.natDegree)
    {x : ℝ} (hpx : p.eval x ≠ 0) :
    h.derivative.eval x =
      p.derivative.eval x *
          (∑ r ∈ p.roots.toFinset,
            (h.eval r / p.derivative.eval r) / (x - r)) -
        p.eval x *
          (∑ r ∈ p.roots.toFinset,
            (h.eval r / p.derivative.eval r) / (x - r) ^ 2) := by
  have hlag : lagInterp p h = h := lagInterp_eq_g hp hpnd hpdeg hhdeg
  calc
    h.derivative.eval x = (lagInterp p h).derivative.eval x := by rw [hlag]
    _ = p.derivative.eval x *
          (∑ r ∈ p.roots.toFinset,
            (h.eval r / p.derivative.eval r) / (x - r)) -
        p.eval x *
          (∑ r ∈ p.roots.toFinset,
            (h.eval r / p.derivative.eval r) / (x - r) ^ 2) := by
      simp only [lagInterp, derivative_sum, derivative_mul, derivative_C,
        zero_mul, zero_add, eval_finsetSum, eval_mul, eval_C]
      have hterm : ∀ r ∈ p.roots.toFinset,
          (h.eval r / p.derivative.eval r) *
              (p /ₘ (X - C r)).derivative.eval x =
            p.derivative.eval x *
                ((h.eval r / p.derivative.eval r) / (x - r)) -
              p.eval x *
                ((h.eval r / p.derivative.eval r) / (x - r) ^ 2) := by
        intro r hr
        have hrroot : p.IsRoot r :=
          isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)
        have hxr : x - r ≠ 0 := by
          intro hzero
          have : x = r := sub_eq_zero.mp hzero
          subst r
          exact hpx hrroot
        rw [eval_derivative_divByMonic_X_sub_C hrroot hxr]
        ring
      apply Eq.trans (Finset.sum_congr rfl hterm)
      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]

end RealRooted.Applications.OEIS
