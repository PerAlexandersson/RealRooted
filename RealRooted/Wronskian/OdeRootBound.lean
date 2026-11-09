module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
import RealRooted.Mathlib.Algebra.Polynomial.FieldDivision
import RealRooted.LaguerreInequalities.Forms

/-!
# Root bounds from second-order polynomial differential equations

Laguerre's inequality bounds the roots of a splitting polynomial that satisfies a
second-order differential equation with polynomial coefficients.
-/

public section

open Polynomial

namespace RealRooted

/-- A root away from the zeros of the leading ODE coefficient is simple. -/
theorem eval_derivative_ne_zero_of_ode
    {p A B C : ℝ[X]} {z : ℝ} (hp0 : p ≠ 0)
    (hode : A * p.derivative.derivative + B * p.derivative + C * p = 0)
    (hz : p.IsRoot z) (hA : A.eval z ≠ 0) :
    p.derivative.eval z ≠ 0 := by
  intro hp'
  have hz' : p.derivative.IsRoot z := hp'
  have hm : 1 < p.rootMultiplicity z :=
    (one_lt_rootMultiplicity_iff_isRoot hp0).2 ⟨hz, hz'⟩
  have hp'_mult := derivative_rootMultiplicity_of_root hz
  have hp'0 : p.derivative ≠ 0 := by
    intro hzero
    rw [hzero, rootMultiplicity_zero] at hp'_mult
    lia
  have hp'_degree : p.derivative.natDegree ≠ 0 := by
    have hmult_pos : 0 < p.derivative.rootMultiplicity z :=
      (rootMultiplicity_pos hp'0).2 hz'
    have hmult_le := rootMultiplicity_le_natDegree p.derivative z
    lia
  have hp''0 : p.derivative.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr hp'_degree
  have hA0 : A ≠ 0 := by
    intro hzero
    simp [hzero] at hA
  have hprod0 : A * p.derivative.derivative ≠ 0 := mul_ne_zero hA0 hp''0
  have hA_mult : A.rootMultiplicity z = 0 :=
    rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot.def] using hA)
  have hp''_mult : p.derivative.derivative.rootMultiplicity z =
      p.rootMultiplicity z - 2 := by
    rw [derivative_rootMultiplicity_of_root hz',
      derivative_rootMultiplicity_of_root hz, Nat.sub_sub]
  have hdiv_p' : (X - Polynomial.C z) ^ (p.rootMultiplicity z - 1) ∣
      p.derivative := by
    apply (le_rootMultiplicity_iff hp'0).mp
    rw [hp'_mult]
  have hdiv_p : (X - Polynomial.C z) ^ (p.rootMultiplicity z - 1) ∣ p := by
    apply (le_rootMultiplicity_iff hp0).mp
    exact Nat.sub_le _ _
  have hdiv_rhs : (X - Polynomial.C z) ^ (p.rootMultiplicity z - 1) ∣
      B * p.derivative + C * p :=
    dvd_add (dvd_mul_of_dvd_right hdiv_p' B) (dvd_mul_of_dvd_right hdiv_p C)
  have hleft : A * p.derivative.derivative = -(B * p.derivative + C * p) := by
    linear_combination hode
  have hdiv_left : (X - Polynomial.C z) ^ (p.rootMultiplicity z - 1) ∣
      A * p.derivative.derivative := by
    rw [hleft]
    exact dvd_neg.mpr hdiv_rhs
  have hmult_left : p.rootMultiplicity z - 1 ≤
      (A * p.derivative.derivative).rootMultiplicity z :=
    (le_rootMultiplicity_iff hprod0).2 hdiv_left
  rw [rootMultiplicity_mul hprod0, hA_mult, zero_add, hp''_mult] at hmult_left
  lia

/-- At a root of a splitting polynomial, the first three derivatives satisfy
`3 * p''(z)^2 - 4 * p'(z) * p'''(z) ≥ 0`. -/
theorem three_mul_sq_eval_derivative_derivative_sub_four_mul_nonneg
    {p : ℝ[X]} (hp : p.Splits) {z : ℝ} (hz : p.IsRoot z) :
    0 ≤ 3 * p.derivative.derivative.eval z ^ 2 -
      4 * p.derivative.eval z * p.derivative.derivative.derivative.eval z := by
  have h := secondLaguerreForm_eval_nonneg hp z
  rw [eval_secondLaguerreForm, hz.eq_zero] at h
  linarith

/-- At a nonsingular root of a splitting solution to a second-order polynomial ODE,
the ODE discriminant expression is nonpositive. -/
theorem ode_discriminant_eval_nonpos_of_isRoot
    {p A B C : ℝ[X]} (hp0 : p ≠ 0) (hp : p.Splits)
    (hode : A * p.derivative.derivative + B * p.derivative + C * p = 0)
    {z : ℝ} (hz : p.IsRoot z) (hA : A.eval z ≠ 0) :
    (B ^ 2 + 4 * A.derivative * B - 4 * A * (B.derivative + C)).eval z ≤ 0 := by
  have hp'0 := eval_derivative_ne_zero_of_ode hp0 hode hz hA
  have hlag := three_mul_sq_eval_derivative_derivative_sub_four_mul_nonneg hp hz
  have hode_eval := congrArg (Polynomial.eval z) hode
  have hode_derivative := congrArg (Polynomial.eval z) (congrArg derivative hode)
  simp only [eval_add, eval_mul, eval_zero, hz.eq_zero, mul_zero, add_zero] at hode_eval
  simp only [derivative_add, derivative_mul, derivative_zero, eval_add, eval_mul,
    eval_zero, hz.eq_zero, mul_zero, zero_add] at hode_derivative
  have hidentity :
      A.eval z ^ 2 *
          (3 * p.derivative.derivative.eval z ^ 2 -
            4 * p.derivative.eval z * p.derivative.derivative.derivative.eval z) =
        -(B.eval z ^ 2 + 4 * A.derivative.eval z * B.eval z -
            4 * A.eval z * (B.derivative.eval z + C.eval z)) *
          p.derivative.eval z ^ 2 := by
    linear_combination
      (3 * A.eval z * p.derivative.derivative.eval z +
          (4 * A.derivative.eval z + B.eval z) * p.derivative.eval z) * hode_eval +
        (-4 * A.eval z * p.derivative.eval z) * hode_derivative
  have hnonneg :
      0 ≤ -(B.eval z ^ 2 + 4 * A.derivative.eval z * B.eval z -
          4 * A.eval z * (B.derivative.eval z + C.eval z)) *
        p.derivative.eval z ^ 2 := by
    rw [← hidentity]
    exact mul_nonneg (sq_nonneg _) hlag
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat]
  nlinarith [sq_pos_of_ne_zero hp'0]

/-- A nonsingular point where the ODE discriminant expression is positive is not a root. -/
theorem not_isRoot_of_ode_discriminant_eval_pos
    {p A B C : ℝ[X]} (hp0 : p ≠ 0) (hp : p.Splits)
    (hode : A * p.derivative.derivative + B * p.derivative + C * p = 0)
    {z : ℝ}
    (hpos : 0 < (B ^ 2 + 4 * A.derivative * B -
      4 * A * (B.derivative + C)).eval z)
    (hA : A.eval z ≠ 0) :
    ¬p.IsRoot z := by
  intro hz
  linarith [ode_discriminant_eval_nonpos_of_isRoot hp0 hp hode hz hA]

end RealRooted
