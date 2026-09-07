/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi

/-!
# Shifted Legendre and shifted Jacobi polynomials

This file identifies Mathlib's canonical integer-coefficient shifted Legendre
polynomial with the zero-parameter specialization of the real shifted Jacobi
family.
-/

@[expose] public section

open Nat

namespace Polynomial

/-- The shifted Jacobi polynomial with both parameters zero is Mathlib's
canonical shifted Legendre polynomial mapped to the reals. -/
@[simp] theorem shiftedJacobi_zero_zero_eq_map_shiftedLegendre (n : ℕ) :
    shiftedJacobi n 0 0 =
      (shiftedLegendre n).map (Int.castRingHom ℝ) := by
  ext k
  rw [coeff_shiftedJacobi, coeff_map, coeff_shiftedLegendre]
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    norm_num [Ring.choose_natCast]
    rw [← Nat.cast_add, Ring.choose_natCast, Nat.choose_symm hk,
      Nat.choose_symm_add]
  · rw [if_neg hk, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]
    simp

end Polynomial
