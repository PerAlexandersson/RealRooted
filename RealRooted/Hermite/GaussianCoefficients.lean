module

public import RealRooted.Hermite.GeneratingFunction
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Even and odd Taylor coefficients of a Gaussian

At the origin, quadratic exponentials have zero odd derivatives and even
Taylor coefficients `s^n/n!`. The homogeneous Hermite recurrence proves the
identities directly, including the zero quadratic parameter.
-/

public section

open Complex

namespace RealRooted

/-- Odd homogeneous Hermite values vanish at the origin. -/
theorem hermiteHomogeneous_zero_odd {R : Type*} [CommRing R] (s : R) (n : ℕ) :
    hermiteHomogeneous 0 s (2 * n + 1) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by lia,
        hermiteHomogeneous_add_two, ih]
      simp

/-- Even homogeneous Hermite values at the origin have the Gaussian factorial normalization. -/
theorem hermiteHomogeneous_zero_even (s : ℂ) (n : ℕ) :
    hermiteHomogeneous 0 s (2 * n) = (2 * n).factorial * s ^ n / n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by lia, hermiteHomogeneous_add_two, ih]
      simp only [zero_mul, zero_add, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, pow_succ]
      have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
      have hs : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
      field_simp
      ring

/-- Odd Taylor derivatives of a quadratic exponential vanish at zero. -/
theorem iteratedDeriv_exp_mul_sq_zero_odd (s : ℂ) (n : ℕ) :
    iteratedDeriv (2 * n + 1) (fun z => exp (s * z ^ 2)) 0 = 0 := by
  simpa only [zero_mul, zero_add, hermiteHomogeneous_zero_odd] using
    iteratedDeriv_exp_quadratic_zero 0 s (2 * n + 1)

/-- The even Taylor derivatives of a quadratic exponential have the heat-series normalization. -/
theorem iteratedDeriv_exp_mul_sq_zero_even (s : ℂ) (n : ℕ) :
    iteratedDeriv (2 * n) (fun z => exp (s * z ^ 2)) 0 =
      (2 * n).factorial * s ^ n / n.factorial := by
  simpa only [zero_mul, zero_add, hermiteHomogeneous_zero_even] using
    iteratedDeriv_exp_quadratic_zero 0 s (2 * n)

end RealRooted
