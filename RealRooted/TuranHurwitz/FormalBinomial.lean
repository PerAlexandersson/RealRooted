module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Formal binomial differentiation

Real exponents are handled by Mathlib's binomial series and formal substitution.
All identities are coefficient identities; no convergence or branch choices are used.
-/

public section

open scoped PowerSeries

namespace RealRooted.TuranHurwitz

/-- The coefficient relation needed for differentiating a real binomial series. -/
theorem choose_succ_mul (r : ℝ) (n : ℕ) :
    Ring.choose r (n + 1) * (n + 1 : ℝ) = r * Ring.choose (r - 1) n := by
  have h := Ring.choose_smul_choose r (n := n + 1) (k := 1) (by lia)
  simpa only [Nat.choose_one_right, Ring.choose_one_right, Nat.add_sub_cancel,
    nsmul_eq_mul, mul_comm, Nat.cast_add, Nat.cast_one] using h

/-- Formal differentiation of the real binomial series over any commutative real algebra. -/
theorem derivative_binomialSeries {A : Type*} [CommRing A] [Algebra ℝ A] (r : ℝ) :
    PowerSeries.derivative (PowerSeries.binomialSeries A r) =
      PowerSeries.C (algebraMap ℝ A r) * PowerSeries.binomialSeries A (r - 1) := by
  ext n
  simp only [PowerSeries.coeff_derivative, PowerSeries.binomialSeries_coeff,
    PowerSeries.coeff_C_mul, Algebra.smul_def, mul_one]
  have h := congrArg (algebraMap ℝ A) (choose_succ_mul r n)
  simpa only [map_mul, map_add, map_natCast, map_one] using h

/-- Multiplication by `1 + X` raises the real binomial exponent by one. -/
theorem one_add_X_mul_binomialSeries_pred (r : ℝ) :
    (1 + PowerSeries.X : PowerSeries ℝ) * PowerSeries.binomialSeries ℝ (r - 1) =
      PowerSeries.binomialSeries ℝ r := by
  have h := PowerSeries.binomialSeries_add (A := ℝ) (1 : ℝ) (r - 1)
  have hone : PowerSeries.binomialSeries ℝ (1 : ℝ) = 1 + PowerSeries.X := by
    simpa using PowerSeries.binomialSeries_nat (R := ℝ) (A := ℝ) 1
  rw [hone] at h
  simpa using h.symm

/-- The Euler differential equation of the binomial series. -/
theorem one_add_X_mul_derivative_binomialSeries (r : ℝ) :
    (1 + PowerSeries.X) * PowerSeries.derivative (PowerSeries.binomialSeries ℝ r) =
      PowerSeries.C r * PowerSeries.binomialSeries ℝ r := by
  rw [derivative_binomialSeries]
  change (1 + PowerSeries.X) *
    (PowerSeries.C r * PowerSeries.binomialSeries ℝ (r - 1)) = _
  rw [mul_left_comm, one_add_X_mul_binomialSeries_pred]

/-- The chain rule for the real binomial series composed with a zero-constant series. -/
theorem derivative_binomialSeries_subst (r : ℝ) (g : PowerSeries ℝ)
    (hg : PowerSeries.HasSubst g) :
    PowerSeries.derivative ((PowerSeries.binomialSeries ℝ r).subst g) =
      PowerSeries.C r * (PowerSeries.binomialSeries ℝ (r - 1)).subst g *
        PowerSeries.derivative g := by
  rw [PowerSeries.derivative_subst hg, derivative_binomialSeries,
    PowerSeries.subst_mul hg, PowerSeries.subst_C]
  rfl

end RealRooted.TuranHurwitz
