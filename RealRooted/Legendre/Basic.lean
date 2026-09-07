/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.RingTheory.Polynomial.ShiftedLegendre

import Mathlib.Tactic.NormNum

/-!
# Shifted Legendre polynomials over the reals

This file maps Mathlib's canonical shifted Legendre polynomial to `ℝ[X]`.
The normalization is `Pₙ(1 - 2X)`. Composing with `-X` gives the
positive-leading orientation `Pₙ(1 + 2X)` used by the OEIS A080721 auxiliary
Legendre family; the actual A080721 polynomial is a distinct quasi-Legendre
combination.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- Mathlib's canonical shifted Legendre polynomial, mapped to `ℝ[X]`. -/
abbrev shiftedLegendreReal (n : ℕ) : ℝ[X] :=
  (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)

/-- The mapped shifted Legendre polynomial is the zero-parameter shifted
Jacobi polynomial. -/
theorem shiftedLegendreReal_eq_shiftedJacobi (n : ℕ) :
    shiftedLegendreReal n = Polynomial.shiftedJacobi n 0 0 :=
  (Polynomial.shiftedJacobi_zero_zero_eq_map_shiftedLegendre n).symm

/-- Composing the real shifted Legendre polynomial with `-X` gives the
positive-leading affine normalization of the zero-parameter shifted Jacobi
polynomial. -/
theorem shiftedLegendreReal_comp_neg_X_eq_shiftedJacobi (n : ℕ) :
    (shiftedLegendreReal n).comp (-X) =
      (Polynomial.shiftedJacobi n 0 0).comp (-X) := by
  rw [shiftedLegendreReal_eq_shiftedJacobi]

@[simp] theorem coeff_shiftedLegendreReal (n k : ℕ) :
    (shiftedLegendreReal n).coeff k =
      ((Polynomial.shiftedLegendre n).coeff k : ℝ) := by
  simp [shiftedLegendreReal]

@[simp] theorem shiftedLegendreReal_natDegree (n : ℕ) :
    (shiftedLegendreReal n).natDegree = n := by
  rw [shiftedLegendreReal_eq_shiftedJacobi]
  exact Polynomial.natDegree_shiftedJacobi n (by norm_num) (by norm_num)

/-- The mapped shifted Legendre polynomial has alternating-sign central
binomial leading coefficient. -/
@[simp] theorem shiftedLegendreReal_leadingCoeff (n : ℕ) :
    (shiftedLegendreReal n).leadingCoeff =
      (-1 : ℝ) ^ n * (Nat.choose (2 * n) n : ℝ) := by
  rw [shiftedLegendreReal_eq_shiftedJacobi,
    Polynomial.leadingCoeff_shiftedJacobi n (by norm_num) (by norm_num)]
  norm_num [Ring.choose_natCast, two_mul]
  rw [← Nat.cast_add, Ring.choose_natCast]

@[simp] theorem shiftedLegendreReal_zero :
    shiftedLegendreReal 0 = 1 := by
  rw [shiftedLegendreReal_eq_shiftedJacobi,
    Polynomial.shiftedJacobi_zero]

@[simp] theorem shiftedLegendreReal_one :
    shiftedLegendreReal 1 = 1 - 2 * X := by
  ext (_ | _ | k) <;>
    norm_num [Polynomial.coeff_shiftedLegendre, coeff_sub, coeff_C_mul,
      coeff_one, Polynomial.coeff_X]

@[simp] theorem shiftedLegendreReal_two :
    shiftedLegendreReal 2 = 1 - 6 * X + 6 * X ^ 2 := by
  ext (_ | _ | _ | k)
  · norm_num [Polynomial.coeff_shiftedLegendre, coeff_sub, coeff_add,
      coeff_C_mul, coeff_one, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · norm_num [Polynomial.coeff_shiftedLegendre, coeff_sub, coeff_add,
      coeff_C_mul, coeff_one, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · norm_num [Polynomial.coeff_shiftedLegendre, coeff_sub, coeff_add,
      coeff_C_mul, coeff_one, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Nat.choose]
  · norm_num [Polynomial.coeff_shiftedLegendre, coeff_sub, coeff_add,
      coeff_C_mul, coeff_one, Polynomial.coeff_X_pow, Polynomial.coeff_X]
    lia

@[simp] theorem shiftedLegendreReal_one_comp_neg_X :
    (shiftedLegendreReal 1).comp (-X) = 1 + 2 * X := by
  rw [shiftedLegendreReal_one]
  simp

@[simp] theorem shiftedLegendreReal_two_comp_neg_X :
    (shiftedLegendreReal 2).comp (-X) = 1 + 6 * X + 6 * X ^ 2 := by
  rw [shiftedLegendreReal_two]
  simp

end RealRooted
