import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import RealRooted.Mathlib.Algebra.LinearRecurrence.Operator

/-!
# Differential operators on recurrence spaces

This module proves the coefficient-derivative product rule and the elementary closure
theorems underlying the finite recurrence certificates of RealRooted issue #1978.
-/

open Finset Polynomial

namespace RealRooted

noncomputable section

variable {K : Type*} [Field K]

/-- Differentiate every coefficient of a polynomial whose coefficients lie in `K[X]`. -/
def coefficientDerivative (p : Polynomial K[X]) : Polynomial K[X] :=
  p.sum fun n a ↦ monomial n a.derivative

@[simp]
theorem coefficientDerivative_zero : coefficientDerivative (0 : Polynomial K[X]) = 0 := by
  simp [coefficientDerivative]

@[simp]
theorem coefficientDerivative_add (p q : Polynomial K[X]) :
    coefficientDerivative (p + q) = coefficientDerivative p + coefficientDerivative q := by
  simp [coefficientDerivative, Polynomial.sum_add_index, derivative_add]

@[simp]
theorem coefficientDerivative_monomial (n : ℕ) (a : K[X]) :
    coefficientDerivative (monomial n a) = monomial n a.derivative := by
  simp [coefficientDerivative]

/-- Differentiate each entry of a polynomial-valued sequence. -/
def sequenceDerivative : (ℕ → K[X]) →ₗ[K] ℕ → K[X] where
  toFun f n := (f n).derivative
  map_add' f g := by ext n; simp
  map_smul' a f := by ext n; simp

@[simp]
theorem sequenceDerivative_apply (f : ℕ → K[X]) (n : ℕ) :
    sequenceDerivative f n = (f n).derivative :=
  rfl

/-- Differentiating the result of a shift-polynomial action differentiates both the
operator coefficients and the sequence entries. -/
theorem sequenceDerivative_shiftAction (p : Polynomial K[X]) (f : ℕ → K[X]) :
    sequenceDerivative (LinearRecurrence.shiftAction p f) =
      LinearRecurrence.shiftAction (coefficientDerivative p) f +
        LinearRecurrence.shiftAction p (sequenceDerivative f) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show LinearRecurrence.shiftAction (p + q) f =
        LinearRecurrence.shiftAction p f + LinearRecurrence.shiftAction q f by
          simp [LinearRecurrence.shiftAction]]
      rw [sequenceDerivative.map_add, hp, hq, coefficientDerivative_add]
      simp only [LinearRecurrence.shiftAction, map_add, LinearMap.add_apply]
      abel
  | monomial j a =>
      ext n
      simp [LinearRecurrence.shiftAction_monomial_apply, sequenceDerivative,
        LinearRecurrence.forwardShift_pow_apply, derivative_mul]

/-- A shift-polynomial action commutes with multiplication of every sequence entry by a
fixed coefficient polynomial. -/
theorem shiftAction_smul (p : Polynomial K[X]) (a : K[X]) (f : ℕ → K[X]) :
    LinearRecurrence.shiftAction p (a • f) =
      a • LinearRecurrence.shiftAction p f := by
  exact (LinearRecurrence.shiftAction p).map_smul a f

/-- Two shift-polynomial actions commute. -/
theorem shiftAction_commute (p q : Polynomial K[X]) (f : ℕ → K[X]) :
    LinearRecurrence.shiftAction p (LinearRecurrence.shiftAction q f) =
      LinearRecurrence.shiftAction q (LinearRecurrence.shiftAction p f) := by
  rw [← LinearRecurrence.shiftAction_mul_apply,
    ← LinearRecurrence.shiftAction_mul_apply, mul_comm]

private theorem pow_succ_apply_eq_zero_of_commutator
    {M : Type*} [AddCommGroup M] [Module K M]
    (T N C : Module.End K M) (hcomm : T * N = N * T + C)
    (hTC : Commute T C) {q : ℕ} {x : M} (hx : (T ^ q) x = 0) :
    (T ^ (q + 1)) (N x) = 0 := by
  induction q generalizing x with
  | zero =>
      simp only [pow_zero, Module.End.one_apply] at hx
      subst x
      simp
  | succ q ih =>
      have hTx : (T ^ q) (T x) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hx
      have hN : (T ^ (q + 1)) (N (T x)) = 0 := ih hTx
      have hC : (T ^ (q + 1)) (C x) = 0 := by
        have hc := LinearMap.congr_fun (hTC.pow_left (q + 1)).eq x
        simp only [Module.End.mul_apply] at hc
        rw [hc, hx, map_zero]
      rw [show q + 1 + 1 = (q + 1) + 1 by rfl, pow_succ, Module.End.mul_apply,
        show T (N x) = N (T x) + C x by
          simpa only [Module.End.mul_apply, LinearMap.add_apply] using
            LinearMap.congr_fun hcomm x,
        map_add, hN, hC, add_zero]

private def polynomialShiftEnd (p : Polynomial K[X]) : Module.End K (ℕ → K[X]) :=
  (LinearRecurrence.shiftAction p).restrictScalars K

private theorem polynomialShiftEnd_pow_apply (p : Polynomial K[X]) (q : ℕ)
    (f : ℕ → K[X]) :
    (polynomialShiftEnd p ^ q) f = LinearRecurrence.shiftAction (p ^ q) f := by
  induction q generalizing f with
  | zero => simp [polynomialShiftEnd]
  | succ q ih =>
      rw [pow_succ, Module.End.mul_apply, ih]
      exact (LinearRecurrence.shiftAction_mul_apply (p ^ q) p f).symm

private def polynomialIndexEnd : Module.End K (ℕ → K[X]) :=
  (LinearRecurrence.indexMul (R := K[X])).restrictScalars K

/-- If `p(S)^q` annihilates a polynomial sequence, then `p(S)^(q+1)` annihilates its
index multiple. -/
theorem shiftAction_pow_succ_indexMul_eq_zero (p : Polynomial K[X]) (q : ℕ)
    (f : ℕ → K[X]) (hf : LinearRecurrence.shiftAction (p ^ q) f = 0) :
    LinearRecurrence.shiftAction (p ^ (q + 1))
      (LinearRecurrence.indexMul f) = 0 := by
  let T := polynomialShiftEnd p
  let N := polynomialIndexEnd (K := K)
  let C := polynomialShiftEnd (X * p.derivative)
  have hcomm : T * N = N * T + C := by
    apply LinearMap.ext
    intro f
    simpa [T, N, C, polynomialShiftEnd, polynomialIndexEnd, Module.End.mul_apply]
      using LinearRecurrence.shiftAction_indexMul p f
  have hTC : Commute T C := by
    change T * C = C * T
    apply LinearMap.ext
    intro f
    change LinearRecurrence.shiftAction p
        (LinearRecurrence.shiftAction (X * p.derivative) f) =
      LinearRecurrence.shiftAction (X * p.derivative)
        (LinearRecurrence.shiftAction p f)
    exact shiftAction_commute p (X * p.derivative) f
  have hpow : (T ^ q) f = 0 := by
    dsimp only [T]
    rw [polynomialShiftEnd_pow_apply]
    exact hf
  have h := pow_succ_apply_eq_zero_of_commutator T N C hcomm hTC hpow
  dsimp only [T] at h
  rw [polynomialShiftEnd_pow_apply] at h
  exact h

private def polynomialDerivativeEnd : Module.End K (ℕ → K[X]) :=
  sequenceDerivative

/-- If `p(S)^q` annihilates a polynomial sequence, then `p(S)^(q+1)` annihilates its
coefficientwise derivative. -/
theorem shiftAction_pow_succ_sequenceDerivative_eq_zero (p : Polynomial K[X]) (q : ℕ)
    (f : ℕ → K[X]) (hf : LinearRecurrence.shiftAction (p ^ q) f = 0) :
    LinearRecurrence.shiftAction (p ^ (q + 1)) (sequenceDerivative f) = 0 := by
  let T := polynomialShiftEnd p
  let N := polynomialDerivativeEnd (K := K)
  let C := -polynomialShiftEnd (coefficientDerivative p)
  have hcomm : T * N = N * T + C := by
    apply LinearMap.ext
    intro f
    have h := sequenceDerivative_shiftAction p f
    change LinearRecurrence.shiftAction p (sequenceDerivative f) =
      sequenceDerivative (LinearRecurrence.shiftAction p f) -
        LinearRecurrence.shiftAction (coefficientDerivative p) f
    rw [h]
    abel
  have hTC : Commute T C := by
    change T * C = C * T
    apply LinearMap.ext
    intro f
    change LinearRecurrence.shiftAction p
        (-LinearRecurrence.shiftAction (coefficientDerivative p) f) =
      -LinearRecurrence.shiftAction (coefficientDerivative p)
        (LinearRecurrence.shiftAction p f)
    rw [map_neg]
    congr 1
    exact shiftAction_commute p (coefficientDerivative p) f
  have hpow : (T ^ q) f = 0 := by
    dsimp only [T]
    rw [polynomialShiftEnd_pow_apply]
    exact hf
  have h := pow_succ_apply_eq_zero_of_commutator T N C hcomm hTC hpow
  dsimp only [T] at h
  rw [polynomialShiftEnd_pow_apply] at h
  exact h

end

end RealRooted
