/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Boundary
import RealRooted.CombinatorialExamples.LongCycleDescents.Coefficients
import Mathlib.Tactic

/-!
# Exact polynomial factorizations at the two exceptional supports

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

public section

namespace RealRooted.LongCycleDescents

open Polynomial Necklace

/-- Four-letter derangements have a double root at minus two. -/
theorem realDescentPolynomial_four_two :
    realDescentPolynomial 4 2 = X * (X + C 2) ^ 2 := by
  have counts : descentRowDP 4 2 = [0, 4, 4, 1] := by decide +kernel
  rw [realDescentPolynomial, ← coefficientPolynomial_descentRowDP (by decide) 2, counts]
  simp only [coefficientPolynomial, Int.cast_ofNat, Int.cast_zero, C_0, zero_add,
    mul_zero, add_zero, Int.cast_one, C_1, C_ofNat]
  ring

/-- Every cutoff from three through five gives the same five-letter polynomial. -/
theorem realDescentPolynomial_five {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 5) :
    realDescentPolynomial 5 k = C 6 * X * (X + C 1) ^ 2 := by
  have counts : ∀ i : Fin 3, descentRowDP 5 (i.val + 3) = [0, 6, 12, 6, 0] := by
    decide +kernel
  let i : Fin 3 := ⟨k - 3, by lia⟩
  have ki : i.val + 3 = k := Nat.sub_add_cancel hk
  have row := counts i
  rw [ki] at row
  rw [realDescentPolynomial, ← coefficientPolynomial_descentRowDP (by decide) k, row]
  simp only [coefficientPolynomial, Int.cast_ofNat, Int.cast_zero, C_0, zero_add,
    mul_zero, add_zero, C_1, C_ofNat]
  ring

/-- The exceptional five-letter row still splits over the reals. -/
theorem realDescentPolynomial_five_splits {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 5) :
    (realDescentPolynomial 5 k).Splits := by
  rw [realDescentPolynomial_five hk kn]
  exact ((Splits.C _).mul Splits.X).mul ((Splits.X_add_C _).pow _)

/-- The exceptional four-letter derangement row has exactly the asserted repeated root. -/
theorem realDescentPolynomial_four_two_roots :
    (realDescentPolynomial 4 2).roots = {0} + 2 • ({-2} : Multiset ℝ) := by
  rw [realDescentPolynomial_four_two,
    roots_mul (mul_ne_zero X_ne_zero (pow_ne_zero _ (monic_X_add_C 2).ne_zero)),
    roots_X, roots_pow, roots_X_add_C]

/-- The exceptional five-letter row has exactly one double negative root and one zero. -/
theorem realDescentPolynomial_five_roots {k : ℕ} (hk : 3 ≤ k) (kn : k ≤ 5) :
    (realDescentPolynomial 5 k).roots = {0} + 2 • ({-1} : Multiset ℝ) := by
  rw [realDescentPolynomial_five hk kn, mul_assoc, roots_C_mul _ (by norm_num),
    roots_mul (mul_ne_zero X_ne_zero (pow_ne_zero _ (monic_X_add_C 1).ne_zero)),
    roots_X, roots_pow, roots_X_add_C]

end RealRooted.LongCycleDescents
