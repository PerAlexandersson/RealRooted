import Mathlib.Algebra.Polynomial.Derivative

/-!
# Shifted Euler operators

This file defines the algebraic operator `a + X d/dX` over a general
coefficient semiring. It supplies the coefficientwise, additive, scalar,
commutation, iteration, and injectivity API independently of the real-rooted
polynomial theory.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The shifted Euler operator `a + X d/dX`. -/
def eulerShift {R : Type*} [Semiring R] (a : R) (p : R[X]) : R[X] :=
  X * p.derivative + C a * p

@[simp] theorem coeff_eulerShift {R : Type*} [CommSemiring R]
    (a : R) (p : R[X]) (k : ℕ) :
    (eulerShift a p).coeff k = ((k : R) + a) * p.coeff k := by
  cases k with
  | zero => simp [eulerShift]
  | succ k =>
      rw [eulerShift, coeff_add, coeff_X_mul, coeff_derivative, coeff_C_mul]
      push_cast
      ring

@[simp] theorem eulerShift_zero_polynomial {R : Type*} [Semiring R]
    (a : R) : eulerShift a 0 = 0 := by
  simp [eulerShift]

theorem eulerShift_add {R : Type*} [CommSemiring R]
    (a : R) (p q : R[X]) :
    eulerShift a (p + q) = eulerShift a p + eulerShift a q := by
  ext k
  simp [mul_add]

theorem eulerShift_smul {R : Type*} [CommSemiring R]
    (a c : R) (p : R[X]) :
    eulerShift a (c • p) = c • eulerShift a p := by
  ext k
  simp [mul_left_comm]

/-- Shifted Euler operators commute under composition. -/
theorem eulerShift_comm {R : Type*} [CommSemiring R]
    (a b : R) (p : R[X]) :
    eulerShift a (eulerShift b p) = eulerShift b (eulerShift a p) := by
  ext k
  simp [mul_left_comm]

theorem eulerShift_commute {R : Type*} [CommSemiring R] (a b : R) :
    Function.Commute (eulerShift a) (eulerShift b) :=
  fun p ↦ eulerShift_comm a b p

/-- Coefficients after iterating one shifted Euler operator. -/
@[simp] theorem coeff_eulerShift_iterate {R : Type*} [CommSemiring R]
    (a : R) (m : ℕ) (p : R[X]) (k : ℕ) :
    (((eulerShift a)^[m]) p).coeff k =
      ((k : R) + a) ^ m * p.coeff k := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', coeff_eulerShift, ih, pow_succ]
      ring

/-- On a bounded degree box, only the corresponding diagonal factors need to
be nonzero for injectivity. -/
theorem eulerShift_injOn_natDegree_le
    {R : Type*} [CommSemiring R] [IsDomain R] {a : R} {N : ℕ}
    (ha : ∀ k : ℕ, k ≤ N → (k : R) + a ≠ 0) :
    Set.InjOn (eulerShift a) {p : R[X] | p.natDegree ≤ N} := by
  intro p hp q hq hpq
  ext k
  by_cases hk : k ≤ N
  · have hcoeff := congrArg (fun f : R[X] ↦ f.coeff k) hpq
    simp only [coeff_eulerShift] at hcoeff
    exact mul_left_cancel₀ (ha k hk) hcoeff
  · have hNk : N < k := lt_of_not_ge hk
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hNk),
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq hNk)]

/-- The shifted Euler operator is injective when none of its diagonal factors
can vanish. -/
theorem eulerShift_injective {R : Type*} [CommSemiring R] [IsDomain R]
    {a : R} (ha : ∀ k : ℕ, (k : R) + a ≠ 0) :
    Function.Injective (eulerShift a) := by
  intro p q hpq
  ext k
  have hcoeff := congrArg (fun f : R[X] ↦ f.coeff k) hpq
  simp only [coeff_eulerShift] at hcoeff
  exact mul_left_cancel₀ (ha k) hcoeff

/-- A positive shift over an ordered field is injective. -/
theorem eulerShift_injective_of_pos
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {a : R} (ha : 0 < a) : Function.Injective (eulerShift a) :=
  eulerShift_injective fun k ↦
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) ha).ne'

end RealRooted
