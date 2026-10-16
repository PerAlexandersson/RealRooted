/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import RealRooted.Mathlib.Algebra.LinearRecurrence.Annihilator

/-!
# Polynomial actions on recurrence sequences

A polynomial acts on a sequence by evaluating it at the forward shift.  We also prove that a
monic annihilator is determined by its initial values and compute its commutator with
multiplication by the sequence index.
-/

@[expose] public noncomputable section

open Finset Polynomial

namespace LinearRecurrence

variable {R : Type*}

section CommRing

variable [CommRing R]

/-- The action of a polynomial on a sequence, obtained by evaluating at the forward shift. -/
def shiftAction (p : R[X]) : (ℕ → R) →ₗ[R] ℕ → R :=
  Polynomial.aeval forwardShift p

@[simp]
theorem shiftAction_zero : shiftAction (0 : R[X]) = 0 := by
  simp [shiftAction]

@[simp]
theorem shiftAction_one : shiftAction (1 : R[X]) = LinearMap.id := by
  ext u
  simp [shiftAction]

/-- Products of shift polynomials act by composition. -/
theorem shiftAction_mul_apply (p q : R[X]) (u : ℕ → R) :
    shiftAction (p * q) u = shiftAction p (shiftAction q u) := by
  simp [shiftAction, Polynomial.aeval_mul, Module.End.mul_apply]

/-- Powers of a shift polynomial act by iterating its action. -/
theorem shiftAction_pow_apply (p : R[X]) (q : ℕ) (u : ℕ → R) :
    shiftAction (p ^ q) u = (shiftAction p ^ q) u := by
  induction q generalizing u with
  | zero => simp
  | succ q ih => simp [pow_succ, shiftAction_mul_apply, ih]

private def recurrenceOfMonic (p : R[X]) : LinearRecurrence R where
  order := p.natDegree
  coeffs i := -p.coeff i

private theorem charPoly_recurrenceOfMonic {p : R[X]} (hp : p.Monic) :
    (recurrenceOfMonic p).charPoly = p := by
  rw [LinearRecurrence.charPoly]
  dsimp only [recurrenceOfMonic]
  rw [monomial_one_right_eq_X_pow]
  change X ^ p.natDegree - ∑ i : Fin p.natDegree, monomial i (-p.coeff i) = p
  calc
    _ = X ^ p.natDegree + ∑ i ∈ range p.natDegree, C (p.coeff i) * X ^ i := by
      rw [Fin.sum_univ_eq_sum_range (fun i ↦ monomial i (-p.coeff i)) p.natDegree]
      simp [← C_mul_X_pow_eq_monomial]
    _ = p := hp.as_sum.symm

/-- A sequence annihilated by a monic shift polynomial is zero when its first
`p.natDegree` entries are zero. -/
theorem eq_zero_of_monic_of_shiftAction_eq_zero {p : R[X]} (hp : p.Monic)
    {u : ℕ → R} (hann : shiftAction p u = 0)
    (hinit : ∀ n < p.natDegree, u n = 0) : u = 0 := by
  let E := recurrenceOfMonic p
  have hsol : E.IsSolution u := by
    rw [isSolution_iff_aeval_charPoly_eq_zero, charPoly_recurrenceOfMonic hp]
    exact hann
  rw [E.eq_iff_eqOn_range_order u 0 hsol E.solSpace.zero_mem]
  intro n hn
  exact hinit n (mem_range.mp hn)

/-- Multiplication of a sequence by its index. -/
def indexMul : (ℕ → R) →ₗ[R] ℕ → R where
  toFun u n := (n : R) * u n
  map_add' u v := by ext n; simp [mul_add]
  map_smul' a u := by ext n; simp [mul_left_comm]

@[simp]
theorem indexMul_apply (u : ℕ → R) (n : ℕ) : indexMul u n = (n : R) * u n :=
  rfl

/-- A monomial in the shift acts by a scalar times an iterated forward shift. -/
theorem shiftAction_monomial_apply (a : R) (k : ℕ) (u : ℕ → R) :
    shiftAction (monomial k a) u = a • (forwardShift ^ k) u := by
  simp [shiftAction, ← C_mul_X_pow_eq_monomial, Polynomial.aeval_mul,
    Module.End.mul_apply]

/-- The commutator of a shift polynomial with index multiplication is the action of
`X * p.derivative`. -/
theorem shiftAction_indexMul_sub (p : R[X]) (u : ℕ → R) :
    shiftAction p (indexMul u) - indexMul (shiftAction p u) =
      shiftAction (X * p.derivative) u := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [shiftAction, map_add, mul_add]
      ext n
      have hp' := congr_fun hp n
      have hq' := congr_fun hq n
      simp only [shiftAction, LinearMap.add_apply, Pi.add_apply, Pi.sub_apply,
        indexMul_apply] at hp' hq' ⊢
      linear_combination hp' + hq'
  | monomial k a =>
      ext n
      simp only [shiftAction_monomial_apply, Pi.smul_apply, smul_eq_mul,
        forwardShift_pow_apply, indexMul_apply, Pi.sub_apply, derivative_monomial]
      by_cases hk : k = 0
      · simp only [hk, add_zero, zero_tsub, Nat.cast_zero, mul_zero, monomial_zero_right,
          shiftAction_zero, LinearMap.zero_apply, Pi.zero_apply]
        ring
      · rw [X_mul_monomial, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk),
          shiftAction_monomial_apply]
        simp only [Pi.smul_apply, smul_eq_mul, forwardShift_pow_apply]
        simp only [Nat.cast_add]
        ring

/-- The commutator form of `shiftAction_indexMul_sub`. -/
theorem shiftAction_indexMul (p : R[X]) (u : ℕ → R) :
    shiftAction p (indexMul u) =
      indexMul (shiftAction p u) + shiftAction (X * p.derivative) u := by
  have h := shiftAction_indexMul_sub p u
  rw [sub_eq_iff_eq_add] at h
  simpa only [add_comm] using h

end CommRing

end LinearRecurrence
