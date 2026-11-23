module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Generalized Hermite polynomials as finite differential sums

For positive `p`, `generalizedHermite p d` is the finite action
`exp (-D^p) X^d`. Its definition uses polynomial derivatives, so no analytic
convergence convention is needed. At `p = 0` the finite definition is retained
without identifying it with an exponential operator.
-/

public section

open Polynomial Finset

namespace RealRooted

/-- The finite exponential of a power of differentiation, evaluated on `X^d`.
The interpretation as `exp (-D^p) X^d` is for positive `p`. -/
@[expose] noncomputable def generalizedHermite (p d : ℕ) : ℝ[X] :=
  ∑ k ∈ range (d / p + 1),
    C ((-1 : ℝ) ^ k / k.factorial) * (derivative^[p * k]) (X ^ d)

/-- The finite derivative definition has the usual factorial expansion. -/
theorem generalizedHermite_eq_sum (p d : ℕ) :
    generalizedHermite p d =
      ∑ k ∈ range (d / p + 1),
        C ((-1 : ℝ) ^ k * d.factorial /
          (k.factorial * (d - p * k).factorial)) * X ^ (d - p * k) := by
  unfold generalizedHermite
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ d / p := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hpk : p * k ≤ d :=
    (Nat.mul_le_mul_left p hk').trans (Nat.mul_div_le d p)
  have hdesc : (d.descFactorial (p * k) : ℝ) =
      d.factorial / (d - p * k).factorial := by
    apply (eq_div_iff (by positivity)).mpr
    exact_mod_cast (by simpa only [Nat.mul_comm] using Nat.factorial_mul_descFactorial hpk)
  rw [iterate_derivative_X_pow_eq_C_mul, ← mul_assoc, ← C_mul, hdesc]
  congr 1
  field_simp

/-- Below the derivative stride, the generalized Hermite polynomial is unchanged. -/
theorem generalizedHermite_eq_X_pow {p d : ℕ} (h : d < p) :
    generalizedHermite p d = X ^ d := by
  simp [generalizedHermite, Nat.div_eq_of_lt h]

end RealRooted
