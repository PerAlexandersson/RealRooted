/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Differential

/-!
# Recurrences for generalized Laguerre polynomials

This file proves the division-free three-term recurrence.  Its additive form
holds over a commutative semiring; the usual monic subtractive form is a ring
corollary.
-/

@[expose] public section

namespace Polynomial

universe u

variable {R : Type u}

section CommSemiring

variable [CommSemiring R]

/-- A lowering identity complementary to the first-order raising recurrence. -/
theorem generalizedLaguerre_lowering (n : ℕ) (α : R) :
    X * (generalizedLaguerre (n + 1) α).derivative +
        C ((n + 1 : R) * ((n : R) + α + 1)) * generalizedLaguerre n α =
      C (n + 1 : R) * generalizedLaguerre (n + 1) α := by
  have hode := generalizedLaguerre_ode n α
  simp only [laguerreDifferentialOperator] at hode
  have hxode := congrArg (fun p : R[X] => X * p) hode
  have hxode' :
      X * X * (generalizedLaguerre n α).derivative.derivative +
          X * (C (α + 1) + X) *
            (generalizedLaguerre n α).derivative =
        C (n : R) * X * generalizedLaguerre n α := by
    calc
      X * X * (generalizedLaguerre n α).derivative.derivative +
          X * (C (α + 1) + X) *
            (generalizedLaguerre n α).derivative =
        X * (X * (generalizedLaguerre n α).derivative.derivative +
          (C (α + 1) + X) *
            (generalizedLaguerre n α).derivative) := by ring
      _ = X * (C (n : R) * generalizedLaguerre n α) := hxode
      _ = C (n : R) * X * generalizedLaguerre n α := by ring
  rw [generalizedLaguerre_succ, laguerreRaisingStep]
  calc
    X * ((X + C ((n : R) + α + 1)) * generalizedLaguerre n α +
          X * (generalizedLaguerre n α).derivative).derivative +
        C ((n + 1 : R) * ((n : R) + α + 1)) *
          generalizedLaguerre n α =
      X * generalizedLaguerre n α +
          C ((n + 1 : R) * ((n : R) + α + 1)) *
            generalizedLaguerre n α +
        C (n + 1 : R) * X * (generalizedLaguerre n α).derivative +
        (X * X * (generalizedLaguerre n α).derivative.derivative +
          X * (C (α + 1) + X) *
            (generalizedLaguerre n α).derivative) := by
        simp only [derivative_add, derivative_mul, derivative_X,
          derivative_C, one_mul]
        simp only [map_add, map_one]
        ring
    _ = X * generalizedLaguerre n α +
          C ((n + 1 : R) * ((n : R) + α + 1)) *
            generalizedLaguerre n α +
        C (n + 1 : R) * X * (generalizedLaguerre n α).derivative +
          C (n : R) * X * generalizedLaguerre n α := by rw [hxode']
    _ = C (n + 1 : R) *
        ((X + C ((n : R) + α + 1)) * generalizedLaguerre n α +
          X * (generalizedLaguerre n α).derivative) := by
      simp only [map_add, map_mul, map_one]
      ring

/-- Additive, division-free three-term recurrence. -/
theorem generalizedLaguerre_three_term_add (n : ℕ) (α : R) :
    generalizedLaguerre (n + 2) α +
        C ((n + 1 : R) * ((n : R) + α + 1)) * generalizedLaguerre n α =
      (X + C (2 * (n : R) + α + 3)) *
        generalizedLaguerre (n + 1) α := by
  rw [show n + 2 = (n + 1) + 1 by lia, generalizedLaguerre_succ,
    laguerreRaisingStep]
  rw [add_assoc, generalizedLaguerre_lowering n α]
  simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_one,
    map_ofNat]
  ring

/-- Subdiagonal coefficient in the monic generalized Laguerre recurrence. -/
noncomputable def generalizedLaguerreSubdiag (n : ℕ) (α : R) : R :=
  (n : R) * ((n : R) + α)

end CommSemiring

section CommRing

variable [CommRing R]

/-- Diagonal coefficient in the monic generalized Laguerre recurrence. -/
noncomputable def generalizedLaguerreDiag (n : ℕ) (α : R) : R :=
  -(2 * (n : R) + α + 1)

/-- The usual monic three-term recurrence. -/
theorem generalizedLaguerre_three_term (n : ℕ) (α : R) :
    generalizedLaguerre (n + 2) α =
      (X - C (generalizedLaguerreDiag (n + 1) α)) *
          generalizedLaguerre (n + 1) α -
        C (generalizedLaguerreSubdiag (n + 1) α) *
          generalizedLaguerre n α := by
  rw [eq_sub_iff_add_eq]
  have h := generalizedLaguerre_three_term_add (R := R) n α
  simp only [generalizedLaguerreDiag, generalizedLaguerreSubdiag,
    Nat.cast_add, Nat.cast_one, map_add, map_mul, map_neg, map_one,
    map_ofNat] at h ⊢
  linear_combination h

/-- At the closed parameter boundary, every positive-index polynomial has a
single explicit factor `X`. -/
theorem generalizedLaguerre_succ_neg_one : ∀ n : ℕ,
    generalizedLaguerre (n + 1) (-1 : R) =
      X * generalizedLaguerre n 1
  | 0 => by simp
  | n + 1 => by
      rw [generalizedLaguerre_succ (n + 1) (-1),
        generalizedLaguerre_succ_neg_one n,
        generalizedLaguerre_succ n 1]
      simp only [laguerreRaisingStep, derivative_mul,
        derivative_X, one_mul, Nat.cast_add, Nat.cast_one,
        map_add, map_neg, map_one]
      ring

end CommRing

end Polynomial
