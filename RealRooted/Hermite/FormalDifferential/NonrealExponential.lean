module

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import RealRooted.Hermite.FormalDifferential.ExponentialMonomial
import RealRooted.Hermite.FormalDifferential.Derivative
import RealRooted.Hermite.FormalDifferential.Structure
import RealRooted.BasisTransform.EventuallyGeometric
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Nonreal roots of higher differential exponentials

Differentiation reduces the obstruction to `X^p+c`. For `p>=3`, a multiple
zero of its derivative would force an impossible root at zero if it split.
For `p=2` and positive `c`, it is strictly positive on the real line.
-/

public section

open Polynomial

namespace RealRooted.HermitePoulain

/-- A nontrivial binomial of degree at least three cannot split over the reals. -/
private theorem not_splits_X_pow_add_C {p : ℕ} (hp : 3 ≤ p)
    {c : ℝ} (hc : c ≠ 0) : ¬ (X ^ p + C c : ℝ[X]).Splits := by
  have hp0 : p ≠ 0 := by lia
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp0
  have hm : ((X ^ p + C c : ℝ[X]).derivative).rootMultiplicity 0 = p - 1 := by
    rw [derivative_add, derivative_C, add_zero, derivative_X_pow,
      rootMultiplicity_C_mul hpR]
    simpa only [map_zero, sub_zero] using
      rootMultiplicity_X_sub_C_pow (0 : ℝ) (p - 1)
  have hz : (X ^ p + C c : ℝ[X]).rootMultiplicity 0 = 0 :=
    rootMultiplicity_eq_zero (by simp [IsRoot.def, hp0, hc])
  intro hsplit
  have h := rootMultiplicity_eq_add_one_of_derivative_ge_two hsplit
    (a := 0) (by rw [hm]; lia)
  rw [hz, hm] at h
  lia

/-- A positive constant added to `X^2` leaves no real root. -/
private theorem not_splits_X_sq_add_C {c : ℝ} (hc : 0 < c) :
    ¬ (X ^ 2 + C c : ℝ[X]).Splits := by
  have hP : IsMonicOfDegree (X ^ 2 + C c : ℝ[X]) 2 :=
    (isMonicOfDegree_X_pow ℝ 2).add_right (by simp)
  intro hsplit
  obtain ⟨x, hx⟩ := hsplit.exists_eval_eq_zero (by
    rw [degree_eq_natDegree hP.monic.ne_zero, hP.natDegree_eq]
    norm_num)
  have hx' : x ^ 2 + c = 0 := by simpa only [eval_add, eval_pow, eval_X, eval_C] using hx
  nlinarith [sq_nonneg x]

/-- A higher differential exponential has a nonreal root in every input
degree at least its stride, except for the negative quadratic case. -/
theorem not_splits_formalDifferentialOperator_exp_stride
    {β : ℝ} {p d : ℕ} (hp : 0 < p) (hpd : p ≤ d)
    (hbad : (p = 2 ∧ 0 < β) ∨ (3 ≤ p ∧ β ≠ 0)) :
    ¬ (formalDifferentialOperator
      (PowerSeries.expand p hp.ne' (PowerSeries.rescale β (PowerSeries.exp ℝ)))
      (X ^ d)).Splits := by
  let σ := PowerSeries.expand p hp.ne' (PowerSeries.rescale β (PowerSeries.exp ℝ))
  have hdesc : (d.descFactorial (d - p) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (Nat.sub_le d p)).ne'
  have hd : d - (d - p) = p := Nat.sub_sub_self hpd
  have heq : (derivative^[d - p]) (formalDifferentialOperator σ (X ^ d)) =
      C (d.descFactorial (d - p) : ℝ) * (X ^ p + C (β * (p.factorial : ℝ))) := by
    rw [iterate_derivative_formalDifferentialOperator, iterate_derivative_X_pow_eq_C_mul,
      hd, formalDifferentialOperator_mul_input, formalDifferentialOperator_exp_stride_X_pow β hp]
  intro hsplit
  have hlow := (hsplit.iterate_derivative (d - p)).C_mul
    ((d.descFactorial (d - p) : ℝ)⁻¹)
  rw [heq, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hdesc, C_1, one_mul] at hlow
  rcases hbad with ⟨rfl, hβ⟩ | ⟨hp3, hβ⟩
  · exact not_splits_X_sq_add_C (mul_pos hβ (by positivity)) hlow
  · exact not_splits_X_pow_add_C hp3 (mul_ne_zero hβ (by positivity)) hlow

end RealRooted.HermitePoulain
