/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Moment
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Translation of polynomial moments

Translation of the variable acts on moment sequences by the binomial
transform. The functional identity makes composition and inverse translation
independent of a measure representation.

See Sokal and Walrad, arXiv:2404.12131v1, equation (7).
-/

public section

namespace Polynomial

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The moments obtained by translating the underlying variable by `c`. -/
@[expose] noncomputable def momentTranslate (c : R) (m : ℕ → R) (n : ℕ) : R :=
  momentFunctional m (taylor c (X ^ n))

/-- Translation preserves the zeroth moment. -/
@[simp] theorem momentTranslate_zero (c : R) (m : ℕ → R) :
    momentTranslate c m 0 = m 0 := by
  simp [momentTranslate]

/-- Translating by zero fixes every moment sequence. -/
@[simp] theorem momentTranslate_zero_left (m : ℕ → R) :
    momentTranslate 0 m = m := by
  funext n
  simp [momentTranslate]

/-- The zero moment sequence remains zero under translation. -/
@[simp] theorem momentTranslate_zero_right (c : R) :
    momentTranslate c (0 : ℕ → R) = 0 := by
  funext n
  simp [momentTranslate, momentFunctional, Polynomial.sum]

/-- Translating moments is dual to Taylor substitution on polynomials. -/
theorem momentFunctional_momentTranslate (c : R) (m : ℕ → R) (p : R[X]) :
    momentFunctional (momentTranslate c m) p =
      momentFunctional m (taylor c p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [momentFunctional_add, map_add, hp, hq]
  | monomial n a =>
      simp only [momentFunctional_monomial, taylor_monomial,
        momentFunctional_C_mul, momentTranslate, taylor_X_pow]

/-- Both inputs of a moment pairing transform by the same Taylor substitution. -/
theorem momentPairing_momentTranslate (c : R) (m : ℕ → R) (p q : R[X]) :
    momentPairing (momentTranslate c m) p q =
      momentPairing m (taylor c p) (taylor c q) := by
  simp only [momentPairing, momentFunctional_momentTranslate, taylor_mul]

/-- Successive translations add their parameters. -/
theorem momentTranslate_momentTranslate (b c : R) (m : ℕ → R) :
    momentTranslate b (momentTranslate c m) = momentTranslate (b + c) m := by
  funext n
  change momentFunctional (momentTranslate c m) (taylor b (X ^ n)) = _
  rw [momentFunctional_momentTranslate, taylor_taylor]
  simp only [momentTranslate, add_comm c b]

/-- The explicit binomial formula for translated moments. -/
theorem momentTranslate_eq_sum (c : R) (m : ℕ → R) (n : ℕ) :
    momentTranslate c m n =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : R) * m k * c ^ (n - k) := by
  rw [momentTranslate, taylor_X_pow, add_pow, momentFunctional_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hpoly : (X : R[X]) ^ k * C c ^ (n - k) * (n.choose k : R[X]) =
      C ((n.choose k : R) * c ^ (n - k)) * X ^ k := by
    simp only [map_mul, map_pow, map_natCast]
    ring
  rw [hpoly, momentFunctional_C_mul, momentFunctional_X_pow]
  ring

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- Translation by the negative parameter is a left inverse. -/
@[simp] theorem momentTranslate_neg_cancel (c : R) (m : ℕ → R) :
    momentTranslate (-c) (momentTranslate c m) = m := by
  rw [momentTranslate_momentTranslate, neg_add_cancel, momentTranslate_zero_left]

/-- Translation by the negative parameter is a right inverse. -/
@[simp] theorem momentTranslate_neg_cancel_right (c : R) (m : ℕ → R) :
    momentTranslate c (momentTranslate (-c) m) = m := by
  rw [momentTranslate_momentTranslate, add_neg_cancel, momentTranslate_zero_left]

/-- A fixed translation is injective on moment sequences. -/
theorem momentTranslate_injective (c : R) : Function.Injective (momentTranslate c) := by
  intro m n h
  simpa using congrArg (momentTranslate (-c)) h

end CommRing

end Polynomial
