/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic

/-!
# Exponentials of sums of formal series

We extend the linear-rescaling exponential identity to arbitrary series with
zero constant coefficient, using uniqueness of the formal first-order ODE.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- Formal solutions of `f' = f h` with equal constant coefficients agree. -/
theorem eq_of_derivative_eq_mul {f g h : PowerSeries R}
    (hf : derivative f = f * h) (hg : derivative g = g * h)
    (hzero : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simpa [coeff_zero_eq_constantCoeff_apply] using hzero
    | succ n =>
      have hfc := congrArg (coeff n) hf
      have hgc := congrArg (coeff n) hg
      rw [coeff_derivative, coeff_mul] at hfc hgc
      have hsum :
          (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, coeff q.1 f * coeff q.2 h) =
            ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, coeff q.1 g * coeff q.2 h := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [ih q.1 (Finset.Nat.antidiagonal.fst_lt hq)]
      rw [hsum] at hfc
      exact mul_right_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n) (hfc.trans hgc.symm)

/-- Formal exponentiation turns a sum of series with zero constant
coefficient into the product of their exponentials. -/
theorem subst_exp_add [Algebra ℚ R] {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    (exp R).subst (f + g) = (exp R).subst f * (exp R).subst g := by
  have hfsubst := HasSubst.of_constantCoeff_zero' hf
  have hgsubst := HasSubst.of_constantCoeff_zero' hg
  have haddsubst := hfsubst.add hgsubst
  apply eq_of_derivative_eq_mul (h := derivative f + derivative g)
  · rw [derivative_subst haddsubst, derivative_exp, derivative.map_add]
  · rw [derivative.leibniz, derivative_subst hfsubst, derivative_exp,
      derivative_subst hgsubst, derivative_exp]
    simp only [smul_eq_mul]
    ring
  · have hc {u : PowerSeries R} (hu : constantCoeff u = 0) :
        constantCoeff ((exp R).subst u) = 1 := by
      rw [constantCoeff_eq, constantCoeff_subst_of_constantCoeff_zero hu]
      simp
    rw [map_mul, hc (by simp [hf, hg]), hc hf, hc hg, mul_one]

end PowerSeries
