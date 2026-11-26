/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.IntervalDifferential.DiskTransfer
public import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

/-!
# The alphabet series and the interval operator

We prove the generating-series form of identity (1) in the unpublished structural
long-cycle descent notes. All operations take place in formal power series.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

noncomputable section

open Polynomial

namespace RealRooted.LongCycleDescents.Structural

open IntervalDifferential

/-- The formal inverse of `1-t`. -/
def inverseOneSub : PowerSeries ℝ := (PowerSeries.invOneSubPow ℝ 1).val

private theorem one_sub_mul_inverse :
    (1 - PowerSeries.X) * inverseOneSub = 1 := by
  simpa only [inverseOneSub, PowerSeries.invOneSubPow_inv_eq_one_sub_pow, pow_one] using
    (PowerSeries.invOneSubPow ℝ 1).inv_val

private theorem derivative_inverse :
    PowerSeries.derivative inverseOneSub = inverseOneSub ^ 2 := by
  have hd := congrArg (fun s : PowerSeries ℝ => PowerSeries.derivative s)
    one_sub_mul_inverse
  simp only [Derivation.leibniz, map_sub, PowerSeries.derivative_one,
    PowerSeries.derivative_X, zero_sub, smul_eq_mul] at hd
  linear_combination inverseOneSub * hd -
    (PowerSeries.derivative inverseOneSub) * one_sub_mul_inverse

/-- The formal Cayley parameter `(1+t)/(1-t)`. -/
def cayleySeries : PowerSeries ℝ := (1 + PowerSeries.X) * inverseOneSub
/-- The series `6t/(1-t)^4` of the alphabet factor `q(q²-1)`. -/
def baseSeries : PowerSeries ℝ := 6 * PowerSeries.X * inverseOneSub ^ 4

private theorem derivative_cayley :
    PowerSeries.derivative cayleySeries = 2 * inverseOneSub ^ 2 := by
  simp only [cayleySeries, Derivation.leibniz, map_add, PowerSeries.derivative_one,
    PowerSeries.derivative_X, derivative_inverse, zero_add, smul_eq_mul]
  linear_combination -inverseOneSub * one_sub_mul_inverse

private theorem cayley_chain_identity :
    2 * PowerSeries.X * PowerSeries.derivative cayleySeries = cayleySeries ^ 2 - 1 := by
  rw [derivative_cayley]
  dsimp [cayleySeries]
  linear_combination -(inverseOneSub * (1 - PowerSeries.X) + 1) * one_sub_mul_inverse

private theorem six_eq_C : (6 : PowerSeries ℝ) = PowerSeries.C (6 : ℝ) := by
  exact (map_ofNat (PowerSeries.C (R := ℝ)) 6).symm

private theorem base_derivative_identity :
    baseSeries + PowerSeries.X * PowerSeries.derivative baseSeries =
      2 * baseSeries * cayleySeries := by
  have hd6 : PowerSeries.derivative (6 : PowerSeries ℝ) = 0 := by
    rw [six_eq_C, PowerSeries.derivative_C]
  simp only [baseSeries, cayleySeries, Derivation.leibniz, hd6,
    PowerSeries.derivative_pow, PowerSeries.derivative_X, derivative_inverse,
    smul_eq_mul, mul_one]
  norm_num only [show 4 - 1 = 3 by rfl]
  linear_combination -12 * PowerSeries.X * inverseOneSub ^ 4 * one_sub_mul_inverse

/-- The series of `q(q²-1)Q(q)`, with the exponent `q-1`. -/
def alphabetFactorSeries (Q : ℝ[X]) : PowerSeries ℝ :=
  PowerSeries.mk fun r => (((r : ℝ) + 1) ^ 3 - ((r : ℝ) + 1)) * Q.eval ((r : ℝ) + 1)

private theorem alphabetFactorSeries_one : alphabetFactorSeries 1 = baseSeries := by
  have hu : inverseOneSub ^ 4 = (PowerSeries.invOneSubPow ℝ 4).val := by
    simp [inverseOneSub, PowerSeries.invOneSubPow_eq_inv_one_sub_pow]
  ext r
  rw [alphabetFactorSeries, PowerSeries.coeff_mk]
  simp only [eval_one, mul_one, baseSeries, hu]
  cases r with
  | zero => norm_num
  | succ r =>
    rw [mul_assoc, six_eq_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk]
    have hc := Nat.ascFactorial_eq_factorial_mul_choose r 3
    norm_num [Nat.ascFactorial_succ, Nat.factorial_succ] at hc
    have hcr : (r + 1 : ℝ) * (r + 2) * (r + 3) = 6 * ((3 + r).choose 3 : ℝ) := by
      rw [show r + 3 = 3 + r by lia] at hc
      exact_mod_cast (by nlinarith [hc] : (r + 1) * (r + 2) * (r + 3) =
        6 * (3 + r).choose 3)
    push_cast
    nlinarith

private theorem alphabetFactorSeries_add (Q R : ℝ[X]) :
    alphabetFactorSeries (Q + R) = alphabetFactorSeries Q + alphabetFactorSeries R := by
  ext r
  simp only [alphabetFactorSeries, PowerSeries.coeff_mk, map_add,
    eval_add, mul_add]

private theorem alphabetFactorSeries_C_mul (a : ℝ) (Q : ℝ[X]) :
    alphabetFactorSeries (C a * Q) = PowerSeries.C a * alphabetFactorSeries Q := by
  ext r
  simp only [alphabetFactorSeries, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    eval_mul, eval_C]
  ring

private theorem alphabetFactorSeries_X_mul (Q : ℝ[X]) :
    alphabetFactorSeries (X * Q) = alphabetFactorSeries Q +
      PowerSeries.X * PowerSeries.derivative (alphabetFactorSeries Q) := by
  ext r
  simp only [alphabetFactorSeries, PowerSeries.coeff_mk, map_add,
    eval_mul, eval_X]
  cases r with
  | zero => simp
  | succ r =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
      PowerSeries.coeff_mk]
    push_cast
    ring

/-- Conjugating the series Euler operator gives half the interval operator. -/
private theorem interval_series_conjugation (H : ℝ[X]) :
    baseSeries * aeval cayleySeries ((1 / 2 : ℝ) • intervalOperator 4 H) =
      baseSeries * aeval cayleySeries H + PowerSeries.X *
        PowerSeries.derivative (baseSeries * aeval cayleySeries H) := by
  have hu : baseSeries * aeval cayleySeries (intervalOperator 4 H) =
      2 * (baseSeries * aeval cayleySeries H + PowerSeries.X *
        PowerSeries.derivative (baseSeries * aeval cayleySeries H)) := by
    have hc := cayley_chain_identity
    have hb := base_derivative_identity
    simp only [intervalOperator_apply, map_add, map_mul, map_sub, map_pow,
      aeval_X, map_one, map_ofNat, Derivation.leibniz,
      Derivation.comp_aeval_eq, smul_eq_mul]
    linear_combination -baseSeries * (aeval cayleySeries H.derivative) * hc -
      2 * (aeval cayleySeries H) * hb
  rw [map_smul, mul_smul_comm, hu, two_mul, smul_add]
  module

/-- Generating-series identity for the alphabet factor `q(q²-1)Q(q)`. -/
theorem alphabetFactorSeries_eq_interval (Q : ℝ[X]) :
    alphabetFactorSeries Q = baseSeries * aeval cayleySeries (intervalSpectralApply 4 Q 1) := by
  have hp (n : ℕ) : alphabetFactorSeries (X ^ n) =
      baseSeries * aeval cayleySeries (intervalSpectralApply 4 (X ^ n) 1) := by
    induction n with
    | zero => simp [intervalSpectralApply, alphabetFactorSeries_one]
    | succ n ih =>
      rw [pow_succ', alphabetFactorSeries_X_mul, ih]
      have hh : intervalSpectralApply 4 (X * X ^ n) 1 =
          (1 / 2 : ℝ) • intervalOperator 4 (intervalSpectralApply 4 (X ^ n) 1) := by
        simp [intervalSpectralApply, mul_apply_eq_comp]
      rw [hh, interval_series_conjugation]
  induction Q using Polynomial.induction_on' with
  | add Q R hQ hR =>
    simp only [alphabetFactorSeries_add, hQ, hR, intervalSpectralApply, map_add,
      LinearMap.add_apply, mul_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, alphabetFactorSeries_C_mul, hp]
    simp only [intervalSpectralApply, map_mul, aeval_C, mul_apply_eq_comp,
      Module.algebraMap_end_apply, Algebra.smul_def, Polynomial.algebraMap_eq,
      aeval_C, PowerSeries.algebraMap_eq]
    ring

end RealRooted.LongCycleDescents.Structural
