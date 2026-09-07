/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Polynomial.Basic

import Mathlib.Algebra.Polynomial.Inductions

/-!
# Polynomial moment functionals

This file packages the elementary algebra shared by moment proofs for
classical orthogonal polynomials. A moment sequence `μ : ℕ → R` defines a
functional by sending `X ^ k` to `μ k`; multiplication induces a symmetric
pairing.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommSemiring R]

/-- Evaluation of a polynomial against a prescribed sequence of moments. -/
def momentFunctional (μ : ℕ → R) (p : R[X]) : R :=
  p.sum fun k c => c * μ k

/-- The symmetric polynomial pairing induced by a moment sequence. -/
noncomputable def momentPairing (μ : ℕ → R) (p q : R[X]) : R :=
  momentFunctional μ (p * q)

@[simp] theorem momentFunctional_zero (μ : ℕ → R) :
    momentFunctional μ 0 = 0 := by
  simp [momentFunctional]

@[simp] theorem momentFunctional_add (μ : ℕ → R) (p q : R[X]) :
    momentFunctional μ (p + q) =
      momentFunctional μ p + momentFunctional μ q := by
  simp only [momentFunctional]
  apply sum_add_index <;> simp [add_mul]

@[simp] theorem momentFunctional_sum {ι : Type*} (μ : ℕ → R)
    (s : Finset ι) (p : ι → R[X]) :
    momentFunctional μ (∑ i ∈ s, p i) =
      ∑ i ∈ s, momentFunctional μ (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hs => simp [hi, hs]

@[simp] theorem momentFunctional_C_mul (μ : ℕ → R) (c : R) (p : R[X]) :
    momentFunctional μ (C c * p) = c * momentFunctional μ p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq]
  | monomial n a => simp [momentFunctional, C_mul_monomial, mul_assoc]

@[simp] theorem momentFunctional_monomial (μ : ℕ → R) (c : R) (k : ℕ) :
    momentFunctional μ (monomial k c) = c * μ k := by
  simp [momentFunctional]

@[simp] theorem momentFunctional_X_pow (μ : ℕ → R) (k : ℕ) :
    momentFunctional μ (X ^ k) = μ k := by
  rw [X_pow_eq_monomial, momentFunctional_monomial]
  simp

@[simp] theorem momentFunctional_one (μ : ℕ → R) :
    momentFunctional μ 1 = μ 0 := by
  simpa using momentFunctional_monomial μ 1 0

/-- The bundled linear map associated to a prescribed sequence of moments. -/
def momentFunctionalLinearMap (μ : ℕ → R) : R[X] →ₗ[R] R where
  toFun := momentFunctional μ
  map_add' := momentFunctional_add μ
  map_smul' c p := by
    simp only [Polynomial.smul_eq_C_mul, smul_eq_mul,
      momentFunctional_C_mul, RingHom.id_apply]

@[simp] theorem momentFunctionalLinearMap_apply (μ : ℕ → R) (p : R[X]) :
    momentFunctionalLinearMap μ p = momentFunctional μ p :=
  rfl

/-- The bundled bilinear form induced by a prescribed sequence of moments. -/
noncomputable def momentPairingBilinForm (μ : ℕ → R) : LinearMap.BilinForm R R[X] :=
  (LinearMap.mul R R[X]).compr₂ (momentFunctionalLinearMap μ)

@[simp] theorem momentPairingBilinForm_apply
    (μ : ℕ → R) (p q : R[X]) :
    momentPairingBilinForm μ p q = momentPairing μ p q :=
  rfl

theorem momentPairing_comm (μ : ℕ → R) (p q : R[X]) :
    momentPairing μ p q = momentPairing μ q p := by
  simp [momentPairing, mul_comm]

@[simp] theorem momentPairing_zero_left (μ : ℕ → R) (p : R[X]) :
    momentPairing μ 0 p = 0 := by
  simp [momentPairing]

@[simp] theorem momentPairing_zero_right (μ : ℕ → R) (p : R[X]) :
    momentPairing μ p 0 = 0 := by
  simp [momentPairing]

@[simp] theorem momentPairing_add_left (μ : ℕ → R) (p q s : R[X]) :
    momentPairing μ (p + q) s =
      momentPairing μ p s + momentPairing μ q s := by
  simp [momentPairing, add_mul]

@[simp] theorem momentPairing_add_right (μ : ℕ → R) (p q s : R[X]) :
    momentPairing μ p (q + s) =
      momentPairing μ p q + momentPairing μ p s := by
  rw [momentPairing_comm]
  simp only [momentPairing_add_left]
  rw [momentPairing_comm μ q p, momentPairing_comm μ s p]

section CommRing

variable {S : Type*} [CommRing S]

@[simp] theorem momentFunctional_neg (μ : ℕ → S) (p : S[X]) :
    momentFunctional μ (-p) = -momentFunctional μ p := by
  have h := momentFunctional_C_mul μ (-1) p
  simpa using h

@[simp] theorem momentFunctional_sub (μ : ℕ → S) (p q : S[X]) :
    momentFunctional μ (p - q) =
      momentFunctional μ p - momentFunctional μ q := by
  simp [sub_eq_add_neg]

@[simp] theorem momentPairing_neg_left (μ : ℕ → S) (p q : S[X]) :
    momentPairing μ (-p) q = -momentPairing μ p q := by
  simp [momentPairing]

@[simp] theorem momentPairing_neg_right (μ : ℕ → S) (p q : S[X]) :
    momentPairing μ p (-q) = -momentPairing μ p q := by
  simp [momentPairing]

@[simp] theorem momentPairing_sub_left (μ : ℕ → S) (p q s : S[X]) :
    momentPairing μ (p - q) s =
      momentPairing μ p s - momentPairing μ q s := by
  simp [sub_eq_add_neg]

@[simp] theorem momentPairing_sub_right (μ : ℕ → S) (p q s : S[X]) :
    momentPairing μ p (q - s) =
      momentPairing μ p q - momentPairing μ p s := by
  simp [sub_eq_add_neg]

end CommRing

@[simp] theorem momentPairing_sum_right {ι : Type*} (μ : ℕ → R)
    (p : R[X]) (s : Finset ι) (q : ι → R[X]) :
    momentPairing μ p (∑ i ∈ s, q i) =
      ∑ i ∈ s, momentPairing μ p (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hs => simp [hi, hs]

@[simp] theorem momentPairing_C_mul_left
    (μ : ℕ → R) (c : R) (p q : R[X]) :
    momentPairing μ (C c * p) q = c * momentPairing μ p q := by
  simp [momentPairing, mul_assoc]

@[simp] theorem momentPairing_C_mul_right
    (μ : ℕ → R) (c : R) (p q : R[X]) :
    momentPairing μ p (C c * q) = c * momentPairing μ p q := by
  rw [momentPairing_comm]
  simp only [momentPairing_C_mul_left]
  rw [momentPairing_comm]

@[simp] theorem momentPairing_monomial
    (μ : ℕ → R) (a b : R) (i j : ℕ) :
    momentPairing μ (monomial i a) (monomial j b) =
      a * b * μ (i + j) := by
  simp [momentPairing, monomial_mul_monomial, mul_assoc]

end Polynomial
