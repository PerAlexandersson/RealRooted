/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Generalized Laguerre polynomials

This file defines the division-free, monic, sign-reversed generalized
Laguerre polynomial

`generalizedLaguerre n α = n! L_n^(α)(-X)`.

Thus its roots lie on the nonpositive real axis in the classical parameter
range.  The explicit coefficient formula makes sense over any commutative
semiring and fixes the normalization independently of analytic conventions.
-/

@[expose] public section

open Finset

namespace Polynomial

universe u v

variable {R : Type u}

section CommSemiring

variable [CommSemiring R]

/-- The monic sign-reversed generalized Laguerre polynomial
`n! L_n^(α)(-X)` in a division-free normalization. -/
noncomputable def generalizedLaguerre (n : ℕ) (α : R) : R[X] :=
  ∑ k ∈ range (n + 1),
    C ((Nat.choose n k : R) *
      (ascPochhammer R (n - k)).eval (α + k + 1)) * X ^ k

/-- Coefficients of the monic sign-reversed generalized Laguerre family. -/
theorem coeff_generalizedLaguerre (n k : ℕ) (α : R) :
    (generalizedLaguerre n α).coeff k =
      if k ≤ n then
        (Nat.choose n k : R) *
          (ascPochhammer R (n - k)).eval (α + k + 1)
      else 0 := by
  rw [generalizedLaguerre, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  by_cases h : k ≤ n
  · simp [h, Nat.lt_succ_iff.mpr h]
  · simp [h, Nat.lt_succ_iff.not.mpr h]

@[simp] theorem generalizedLaguerre_zero (α : R) :
    generalizedLaguerre 0 α = 1 := by
  ext k
  cases k <;> simp [coeff_generalizedLaguerre, Polynomial.coeff_one]

@[simp] theorem generalizedLaguerre_one (α : R) :
    generalizedLaguerre 1 α = X + C (α + 1) := by
  ext k
  cases k with
  | zero =>
      simp [coeff_generalizedLaguerre, coeff_add, Polynomial.coeff_one]
  | succ k =>
      cases k <;>
        simp [coeff_generalizedLaguerre, coeff_add, Polynomial.coeff_one,
          Polynomial.coeff_X]

@[simp] theorem generalizedLaguerre_two (α : R) :
    generalizedLaguerre 2 α =
      X ^ 2 + C (2 * (α + 2)) * X + C ((α + 1) * (α + 2)) := by
  norm_num [generalizedLaguerre, Finset.sum_range_succ, ascPochhammer]
  simp only [map_ofNat]
  ring

/-- Generalized Laguerre polynomials have no coefficients above their index. -/
theorem natDegree_generalizedLaguerre_le (n : ℕ) (α : R) :
    (generalizedLaguerre n α).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  simp [coeff_generalizedLaguerre, Nat.not_le_of_lt hk]

@[simp] theorem coeff_generalizedLaguerre_self (n : ℕ) (α : R) :
    (generalizedLaguerre n α).coeff n = 1 := by
  simp [coeff_generalizedLaguerre]

/-- Evaluation at zero is the rising factorial of the shifted parameter. -/
@[simp] theorem generalizedLaguerre_eval_zero (n : ℕ) (α : R) :
    (generalizedLaguerre n α).eval 0 =
      (ascPochhammer R n).eval (α + 1) := by
  rw [← coeff_zero_eq_eval_zero, coeff_generalizedLaguerre,
    if_pos (Nat.zero_le _)]
  simp

variable [Nontrivial R]

@[simp] theorem natDegree_generalizedLaguerre (n : ℕ) (α : R) :
    (generalizedLaguerre n α).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_generalizedLaguerre_le n α)
    (by simp)

@[simp] theorem monic_generalizedLaguerre (n : ℕ) (α : R) :
    (generalizedLaguerre n α).Monic := by
  rw [Monic.def, leadingCoeff, natDegree_generalizedLaguerre]
  simp

@[simp] theorem leadingCoeff_generalizedLaguerre (n : ℕ) (α : R) :
    (generalizedLaguerre n α).leadingCoeff = 1 :=
  (monic_generalizedLaguerre n α).leadingCoeff

end CommSemiring

section Map

variable {S : Type v} [CommSemiring R] [CommSemiring S]

/-- Generalized Laguerre polynomials commute with coefficient-ring maps. -/
@[simp] theorem map_generalizedLaguerre (f : R →+* S) (n : ℕ) (α : R) :
    (generalizedLaguerre n α).map f = generalizedLaguerre n (f α) := by
  ext k
  rw [coeff_map, coeff_generalizedLaguerre, coeff_generalizedLaguerre]
  by_cases hk : k ≤ n
  · simp only [hk, if_pos, map_mul, map_natCast]
    rw [← eval_map_apply, ascPochhammer_map]
    simp
  · simp [hk]

end Map

end Polynomial
