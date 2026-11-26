/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Transforms.BrandenE.Basic
import RealRooted.Transforms.BrandenE.Inverse
public import Mathlib.RingTheory.Binomial
import Mathlib.Tactic

/-!
# Brändén's transform on shifted binomial polynomials

The normalization is `E (choose X n) = X^n`. Pascal's identity then gives
`E (choose (X+a) (a+b)) = X^b (1+X)^a`, the alphabet-to-descent substitution.
See Brändén, arXiv:math/0403364v2, Section 4, equation (4.1).
-/

public section

noncomputable section

open Polynomial

namespace RealRooted

/-- Brändén's transform sends the binomial polynomial to the corresponding monomial. -/
theorem brandenE_choose_X (n : ℕ) :
    brandenE (Ring.choose (X : ℝ[X]) n) = X ^ n := by
  have hp := Ring.descPochhammer_eq_factorial_smul_choose (X : ℝ[X]) n
  have he : (descPochhammer ℤ n).smeval (X : ℝ[X]) = descPochhammer ℝ n := by
    rw [← aeval_eq_smeval]
    change (descPochhammer ℤ n).map (Int.castRingHom ℝ) = _
    exact descPochhammer_map _ _
  rw [he, nsmul_eq_mul, ← C_eq_natCast] at hp
  have ht := congrArg brandenE hp
  rw [brandenE_descPochhammer, brandenE_C_mul] at ht
  exact mul_left_cancel₀ (C_ne_zero.mpr (by positivity : (n.factorial : ℝ) ≠ 0)) ht.symm

/-- Shifted binomial polynomials give the homogeneous descent basis under `E`. -/
theorem brandenE_choose_X_add_nat (a b : ℕ) :
    brandenE (Ring.choose (X + (a : ℝ[X])) (a + b)) =
      X ^ b * (X + 1) ^ a := by
  induction a generalizing b with
  | zero => simpa using brandenE_choose_X b
  | succ a ih =>
    have hp := Ring.choose_succ_succ (X + (a : ℝ[X])) (a + b)
    rw [show a + 1 + b = (a + b) + 1 by lia, Nat.cast_add, Nat.cast_one,
      ← add_assoc, hp, brandenE_add, ih,
      show a + b + 1 = a + (b + 1) by lia, ih]
    ring

end RealRooted
