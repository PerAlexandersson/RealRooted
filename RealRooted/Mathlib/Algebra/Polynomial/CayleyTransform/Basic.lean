/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
import RealRooted.Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring

/-!
# Finite-degree Cayley transform of a polynomial

The transform

`cayleyTransform n p = (1 - T)^n p(T / (1 - T))`

is defined through homogeneous evaluation, so no rational-function side
conditions are needed. The definition is functorial in the coefficient ring.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The degree-`n` Cayley transform `(1 - X)^n * p (X / (1 - X))`, computed without division by
substituting `X` and `1 - X` into the degree-`n` homogenization of `p`. -/
def cayleyTransform (n : ℕ) (p : R[X]) : R[X] :=
  MvPolynomial.aeval ![X, 1 - X] (p.homogenize n)

theorem map_cayleyTransform (f : R →+* S) (n : ℕ) (p : R[X]) :
    (cayleyTransform n p).map f = cayleyTransform n (p.map f) := by
  have h := MvPolynomial.map_eval₂Hom
    (Polynomial.C : R →+* R[X])
    (![(X : R[X]), (1 - X : R[X])] : Fin 2 → R[X])
    (Polynomial.mapRingHom f) (p.homogenize n)
  rw [cayleyTransform, cayleyTransform, Polynomial.homogenize_map]
  simp only [MvPolynomial.aeval_def]
  rw [MvPolynomial.eval₂_map]
  convert h using 1
  · simp
  · congr 1
    · ext r
      simp
    · funext i
      fin_cases i <;> simp

theorem cayleyTransform_sub (n : ℕ) (p q : R[X]) :
    cayleyTransform n (p - q) = cayleyTransform n p - cayleyTransform n q := by
  simp [cayleyTransform, Polynomial.homogenize_sub]

theorem cayleyTransform_add (n : ℕ) (p q : R[X]) :
    cayleyTransform n (p + q) = cayleyTransform n p + cayleyTransform n q := by
  simp [cayleyTransform, Polynomial.homogenize_add]

theorem cayleyTransform_C_mul (n : ℕ) (a : R) (p : R[X]) :
    cayleyTransform n (C a * p) = C a * cayleyTransform n p := by
  simp [cayleyTransform, Polynomial.homogenize_C_mul]

theorem cayleyTransform_finset_sum {ι : Type*} (n : ℕ)
    (s : Finset ι) (p : ι → R[X]) :
    cayleyTransform n (∑ i ∈ s, p i) = ∑ i ∈ s, cayleyTransform n (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cayleyTransform]
  | @insert i s hi ih => simp [hi, ih, cayleyTransform_add]

/-- A polynomial of degree at most `n` has Cayley transform `∑ k, a_k X^k (1 - X)^(n - k)`. -/
theorem cayleyTransform_eq_sum {p : R[X]} {n : ℕ} (hdeg : p.natDegree ≤ n) :
    cayleyTransform n p =
      ∑ k ∈ Finset.range (n + 1), C (p.coeff k) * X ^ k * (1 - X) ^ (n - k) := by
  rw [cayleyTransform, Polynomial.homogenize_eq_sum_range_C_mul_X_pow hdeg]
  simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_C]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [MvPolynomial.eval₂_X, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [← Polynomial.C_eq_algebraMap]
  ring

/-- The Cayley transform of a monomial of degree at most `n`. -/
theorem cayleyTransform_X_pow {n k : ℕ} (hk : k ≤ n) :
    cayleyTransform n (X ^ k : R[X]) = X ^ k * (1 - X) ^ (n - k) := by
  rw [cayleyTransform_eq_sum ((natDegree_X_pow_le k).trans hk), Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [coeff_X_pow, hj]
  · intro hk'
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hk'

/-- A polynomial of degree at most `n` as a sum of monomials. -/
private theorem eq_sum_C_mul_X_pow {p : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    p = ∑ k ∈ Finset.range (n + 1), C (p.coeff k) * X ^ k := by
  conv_lhs => rw [as_sum_range' p (n + 1) (Nat.lt_succ_of_le hp)]
  simp only [C_mul_X_pow_eq_monomial]

/-- Raising the transform degree multiplies the Cayley transform by `1 - X`. -/
theorem cayleyTransform_succ {p : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    cayleyTransform (n + 1) p = (1 - X) * cayleyTransform n p := by
  rw [eq_sum_C_mul_X_pow hp]
  simp only [cayleyTransform_finset_sum, cayleyTransform_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [cayleyTransform_X_pow (by lia), cayleyTransform_X_pow hk,
    show n + 1 - k = n - k + 1 by lia, pow_succ]
  ring

/-- Multiplication by `X` commutes with the Cayley transform when the degree goes up by one. -/
theorem cayleyTransform_succ_X_mul {p : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    cayleyTransform (n + 1) (X * p) = X * cayleyTransform n p := by
  rw [eq_sum_C_mul_X_pow hp]
  simp only [Finset.mul_sum, cayleyTransform_finset_sum, cayleyTransform_C_mul]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [mul_left_comm, ← pow_succ', cayleyTransform_C_mul, cayleyTransform_X_pow (by lia),
    cayleyTransform_X_pow hk, show n + 1 - (k + 1) = n - k by lia]
  ring

/-- `θ = X d/dX` on a monomial. -/
private theorem X_mul_derivative_X_pow (k : ℕ) :
    (X : R[X]) * (X ^ k).derivative = C (k : R) * X ^ k := by
  rcases k with _ | k
  · simp
  · rw [derivative_X_pow, Nat.add_sub_cancel, ← mul_assoc, mul_comm X, mul_assoc, ← pow_succ']

/-- The Euler operator on the Cayley transform of a monomial. -/
private theorem cayleyTransform_X_pow_euler {n k : ℕ} (hk : k ≤ n) :
    X * (1 - X) * (X ^ k * (1 - X) ^ (n - k) : R[X]).derivative +
        C (n : R) * X * (X ^ k * (1 - X) ^ (n - k)) =
      C (k : R) * (X ^ k * (1 - X) ^ (n - k)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left]
  rcases k with _ | k <;> rcases m with _ | m <;>
    simp [derivative_mul, derivative_pow] <;> ring

/-- The Euler operator `θ = X d/dX` under the Cayley transform:
`T (θ p) = X (1 - X) (T p)' + n X (T p)` for `p` of degree at most `n`. -/
theorem cayleyTransform_X_mul_derivative {p : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    cayleyTransform n (X * p.derivative) =
      X * (1 - X) * (cayleyTransform n p).derivative + C (n : R) * X * cayleyTransform n p := by
  rw [eq_sum_C_mul_X_pow hp]
  simp only [derivative_sum, Finset.mul_sum, cayleyTransform_finset_sum, cayleyTransform_C_mul,
    derivative_C_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [mul_left_comm, X_mul_derivative_X_pow]
  simp only [cayleyTransform_C_mul, cayleyTransform_X_pow hk]
  rw [← cayleyTransform_X_pow_euler hk]
  ring

end Polynomial
