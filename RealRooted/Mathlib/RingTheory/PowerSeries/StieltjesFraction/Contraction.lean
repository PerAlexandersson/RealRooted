/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Coefficients
public import RealRooted.Mathlib.RingTheory.PowerSeries.JacobiFraction.Step

/-!
# Contraction of formal Stieltjes fractions

Pairing adjacent Stieltjes tails gives the Jacobi tail equations. The first
diagonal coefficient is `a 0`; subsequent diagonal coefficients are
`a (2*n+1) + a (2*n+2)`, and the outgoing numerators are adjacent products.
These are the classical contraction formulas, over any commutative ring.

See Sokal and Walrad, "Continued-fraction characterization of Stieltjes moment
sequences with support in [ξ,∞)", equations (5) and (6).
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The denominator identity for the actual formal Stieltjes tail. -/
private theorem one_sub_mul_stieltjesTail (a : ℕ → R) (s : ℕ) :
    (1 - C (a s) * X * stieltjesTail a (s + 1)) * stieltjesTail a s = 1 := by
  conv_lhs => rw [stieltjesTail_eq_step a s]
  exact one_sub_mul_stieltjesStep _ _

/-- The shared coefficient recurrence in multiplicative order for contraction. -/
private theorem stieltjesTail_additive (a : ℕ → R) (s : ℕ) :
    stieltjesTail a s =
      1 + C (a s) * X * stieltjesTail a (s + 1) * stieltjesTail a s := by
  simpa only [mul_assoc, mul_comm, mul_left_comm] using stieltjesTail_eq_one_add a s

/-- The first Jacobi step obtained by contracting a Stieltjes fraction. -/
theorem stieltjesTail_eq_jacobiStep (a : ℕ → R) (s : ℕ) :
    stieltjesTail a s = jacobiStep (a s) (a s * a (s + 1))
      (stieltjesTail a (s + 1) * stieltjesTail a (s + 2)) := by
  apply eq_jacobiStep_of_mul_eq_one
  have h0 := one_sub_mul_stieltjesTail a s
  have h1 := stieltjesTail_additive a (s + 1)
  simp only [Nat.add_assoc] at h1
  simp only [map_mul]
  linear_combination h0 + C (a s) * X * stieltjesTail a s * h1

/-- A product of consecutive Stieltjes tails is the next contracted Jacobi tail. -/
theorem stieltjesTail_mul_eq_jacobiStep (a : ℕ → R) (s : ℕ) :
    stieltjesTail a s * stieltjesTail a (s + 1) =
      jacobiStep (a s + a (s + 1)) (a (s + 1) * a (s + 2))
        (stieltjesTail a (s + 2) * stieltjesTail a (s + 3)) := by
  apply eq_jacobiStep_of_mul_eq_one
  have h0 := one_sub_mul_stieltjesTail a s
  have h1 := one_sub_mul_stieltjesTail a (s + 1)
  have h2 := stieltjesTail_additive a (s + 2)
  simp only [Nat.add_assoc] at h1 h2
  simp only [map_add, map_mul]
  linear_combination h0 + stieltjesTail a s * h1 +
    C (a (s + 1)) * X * stieltjesTail a s * stieltjesTail a (s + 1) * h2

/-- The Jacobi tail family produced by pairing Stieltjes tails. -/
@[expose] noncomputable def stieltjesJacobiTail (a : ℕ → R) : ℕ → R⟦X⟧
  | 0 => stieltjesTail a 0
  | n + 1 => stieltjesTail a (2 * n + 1) * stieltjesTail a (2 * n + 2)

/-- The contracted Jacobi diagonal coefficients. -/
@[expose] def stieltjesJacobiDiagonal (a : ℕ → R) : ℕ → R
  | 0 => a 0
  | n + 1 => a (2 * n + 1) + a (2 * n + 2)

/-- The contracted Jacobi outgoing numerator coefficients. The value at `n`
corresponds to the classical coefficient `β_(n+1)`. -/
@[expose] def stieltjesJacobiNumerator (a : ℕ → R) (n : ℕ) : R :=
  a (2 * n) * a (2 * n + 1)

/-- The explicit contracted tails satisfy the Jacobi continued-fraction equations. -/
theorem stieltjesJacobiTail_eq_step (a : ℕ → R) (n : ℕ) :
    stieltjesJacobiTail a n =
      jacobiStep (stieltjesJacobiDiagonal a n) (stieltjesJacobiNumerator a n)
        (stieltjesJacobiTail a (n + 1)) := by
  cases n with
  | zero => simpa [stieltjesJacobiTail, stieltjesJacobiDiagonal,
      stieltjesJacobiNumerator] using stieltjesTail_eq_jacobiStep a 0
  | succ n =>
      simpa [stieltjesJacobiTail, stieltjesJacobiDiagonal,
        stieltjesJacobiNumerator, Nat.mul_add, Nat.add_assoc] using
          stieltjesTail_mul_eq_jacobiStep a (2 * n + 1)

/-- Any formal Jacobi tails with the contracted coefficient data equal the
explicit paired Stieltjes tails. This identifies the formal continued fractions. -/
theorem eq_stieltjesJacobiTail_of_step_eq {a : ℕ → R} {F : ℕ → R⟦X⟧}
    (hF : ∀ n, F n =
      jacobiStep (stieltjesJacobiDiagonal a n) (stieltjesJacobiNumerator a n)
        (F (n + 1))) : F = stieltjesJacobiTail a :=
  eq_of_jacobiStep_eq hF (stieltjesJacobiTail_eq_step a)

end PowerSeries
