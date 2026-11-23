module

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import RealRooted.Mathlib.RingTheory.PowerSeries.ExpCoefficient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The first nontrivial monomial image of an expanded exponential
-/

public section

open Polynomial

namespace RealRooted.HermitePoulain

/-- In input degree equal to the stride, only the constant and first
nonconstant coefficients of the expanded exponential act. -/
theorem formalDifferentialOperator_exp_stride_X_pow
    (β : ℝ) {p : ℕ} (hp : 0 < p) :
    formalDifferentialOperator
      (PowerSeries.expand p hp.ne' (PowerSeries.rescale β (PowerSeries.exp ℝ))) (X ^ p) =
      X ^ p + C (β * (p.factorial : ℝ)) := by
  have hcoeff : ∀ k ≤ (X ^ p : ℝ[X]).natDegree,
      PowerSeries.coeff k
          (PowerSeries.expand p hp.ne' (PowerSeries.rescale β (PowerSeries.exp ℝ))) =
        (1 + C β * X ^ p : ℝ[X]).coeff k := by
    intro k hk
    rw [natDegree_X_pow] at hk
    by_cases hk0 : k = 0
    · subst k
      simp [PowerSeries.coeff_expand, hp.ne]
    · by_cases hkp : k = p
      · subst k
        simp [PowerSeries.coeff_expand, Nat.div_self hp, coeff_one, hp.ne']
      · have hnd : ¬ p ∣ k := by
          intro h
          have hpk := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h
          lia
        rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hnd]
        simp [coeff_C_mul, coeff_X_pow, coeff_one, hk0, hkp]
  rw [formalDifferentialOperator_eq_applyAsDifferentialOperator _ _ _ hcoeff,
    applyAsDifferentialOperator_add, applyAsDifferentialOperator_one,
    applyAsDifferentialOperator_C_mul]
  have hpower : applyAsDifferentialOperator (X ^ p) (X ^ p) = C (p.factorial : ℝ) := by
    have h := applyAsDifferentialOperator_X_pow_mul p 1 (X ^ p)
    simpa only [mul_one, applyAsDifferentialOperator_one,
      iterate_derivative_X_pow_eq_C_mul, Nat.descFactorial_self, Nat.sub_self,
      pow_zero, mul_one] using h
  rw [hpower, ← C_mul]

end RealRooted.HermitePoulain
