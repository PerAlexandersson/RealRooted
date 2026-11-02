/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
import RealRooted.Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Tactic.FinCases
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

end Polynomial
