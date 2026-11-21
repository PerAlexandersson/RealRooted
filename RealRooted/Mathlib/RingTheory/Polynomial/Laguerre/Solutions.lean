/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Differential
import Mathlib.Tactic

/-!
# All polynomial solutions of the generalized Laguerre equation

The coefficient at the polynomial's degree forces that degree to equal the
spectral index. Thus the known monic solution spans the kernel at every parameter,
even when the value at zero vanishes. Source: unpublished proof notes in
RealRooted issue #2343, the Laguerre recognition example.
-/

public section

namespace Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Every nonzero Laguerre polynomial solution has the prescribed degree,
without any restriction on the parameter. -/
theorem natDegree_eq_of_laguerre_equation
    (n : ℕ) (α : K) {p : K[X]} (hp : p ≠ 0)
    (hode : laguerreDifferentialOperator α p = C (n : K) * p) : p.natDegree = n := by
  have hc := congrArg (fun q : K[X] => q.coeff p.natDegree) hode
  rw [coeff_laguerreDifferentialOperator, coeff_C_mul,
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), mul_zero, zero_add,
    coeff_natDegree] at hc
  exact Nat.cast_injective (R := K)
    (mul_right_cancel₀ (leadingCoeff_ne_zero.mpr hp) hc)

/-- A single top coefficient determines any solution of a Laguerre equation. -/
theorem eq_of_laguerre_equation_of_coeff_eq
    (n : ℕ) (α : K) {p q : K[X]}
    (hp : laguerreDifferentialOperator α p = C (n : K) * p)
    (hq : laguerreDifferentialOperator α q = C (n : K) * q)
    (hc : p.coeff n = q.coeff n) : p = q := by
  by_contra hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hode : laguerreDifferentialOperator α (p - q) = C (n : K) * (p - q) := by
    have hlin : laguerreDifferentialOperator α (p - q) =
        laguerreDifferentialOperator α p - laguerreDifferentialOperator α q := by
      simp only [laguerreDifferentialOperator, derivative_sub]
      ring
    rw [hlin, hp, hq]
    ring
  have hdeg := natDegree_eq_of_laguerre_equation n α hsub hode
  exact (leadingCoeff_ne_zero.mpr hsub) (by
    rw [leadingCoeff, hdeg, coeff_sub, hc, sub_self])

/-- The complete polynomial solution space of the Laguerre equation, at every
parameter: its solution is its degree-`n` coefficient times the monic model. -/
theorem laguerre_equation_iff_eq_C_mul_generalizedLaguerre
    (n : ℕ) (α : K) (p : K[X]) :
    laguerreDifferentialOperator α p = C (n : K) * p ↔
      p = C (p.coeff n) * generalizedLaguerre n α := by
  constructor
  · intro hp
    apply eq_of_laguerre_equation_of_coeff_eq n α hp
    · rw [laguerreDifferentialOperator_C_mul, generalizedLaguerre_ode]
      ring
    · simp
  · intro hp
    conv_lhs => rw [hp]
    rw [laguerreDifferentialOperator_C_mul, generalizedLaguerre_ode]
    conv_rhs => rw [hp]
    ring

end Polynomial
