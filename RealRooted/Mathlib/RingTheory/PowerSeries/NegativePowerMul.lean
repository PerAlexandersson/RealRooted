/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Binomial
import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialDerivative
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerRecurrence
import Mathlib.Tactic

/-! # Uniqueness and multiplicativity of normalized formal negative powers -/

public section

namespace PowerSeries

/-- A normalized formal negative-power differential equation has at most
one solution with a prescribed constant coefficient in a characteristic-zero domain. -/
theorem eq_of_negPower_ode {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (κ : R) (H q r : PowerSeries R) (hH : constantCoeff H = 1)
    (hzero : constantCoeff q = constantCoeff r)
    (hq : H * derivative q + C κ * derivative H * q = 0)
    (hr : H * derivative r + C κ * derivative H * r = 0) : q = r := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff_apply] using hzero
    | succ n =>
      apply mul_left_cancel₀ (show (n + 1 : R) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n)
      rw [coeff_recurrence_of_negPower_ode κ H q
        (by simpa only [coeff_zero_eq_constantCoeff_apply] using hH) hq,
        coeff_recurrence_of_negPower_ode κ H r
        (by simpa only [coeff_zero_eq_constantCoeff_apply] using hH) hr]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j (Finset.mem_range.mp hj)]

/-- Products of solutions satisfy the negative-power equation for the
product of their denominator series. -/
theorem mul_negPower_ode {R : Type*} [CommRing R]
    (κ : R) (H K q r : PowerSeries R)
    (hq : H * derivative q + C κ * derivative H * q = 0)
    (hr : K * derivative r + C κ * derivative K * r = 0) :
    (H * K) * derivative (q * r) + C κ * derivative (H * K) * (q * r) = 0 := by
  calc
    _ = (K * r) * (H * derivative q + C κ * derivative H * q) +
        (H * q) * (K * derivative r + C κ * derivative K * r) := by
      rw [derivative.leibniz, derivative.leibniz]
      ring
    _ = 0 := by rw [hq, hr]; simp

/-- Canonical formal negative powers are multiplicative on normalized series. -/
theorem subst_binomialSeries_neg_mul {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] [BinomialRing R] (κ : R) (H K : PowerSeries R)
    (hH : constantCoeff H = 1) (hK : constantCoeff K = 1) :
    subst (H * K - 1) (binomialSeries R (-κ)) =
      subst (H - 1) (binomialSeries R (-κ)) *
        subst (K - 1) (binomialSeries R (-κ)) := by
  have hHK : constantCoeff (H * K) = 1 := by rw [map_mul, hH, hK, mul_one]
  apply eq_of_negPower_ode κ (H * K)
  · exact hHK
  · rw [constantCoeff_subst_binomialSeries_neg κ (H * K) hHK, map_mul,
      constantCoeff_subst_binomialSeries_neg κ H hH,
      constantCoeff_subst_binomialSeries_neg κ K hK, mul_one]
  · exact subst_binomialSeries_neg_ode κ (H * K) hHK
  · exact mul_negPower_ode κ H K _ _ (subst_binomialSeries_neg_ode κ H hH)
      (subst_binomialSeries_neg_ode κ K hK)

end PowerSeries
