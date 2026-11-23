/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.StieltjesGram
public import RealRooted.Mathlib.LinearAlgebra.Matrix.PowerSeries.Resolvent
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
public import RealRooted.Mathlib.RingTheory.PowerSeries.JacobiFraction.Step
import RealRooted.Mathlib.LinearAlgebra.Matrix.PowerSeries.FinSchur
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.TailOffset

/-!
# Stabilization of finite Stieltjes matrix moments

The first-coordinate formal resolvents of the finite Jacobi Gram matrices
approach the formal Stieltjes tail coefficient by coefficient. Every Jacobi
step adds two powers of `X` to the error. This algebraic argument permits
zero numerators and does not require bounded numerator data or convergence
of a numerical continued fraction.
-/

public section

open PowerSeries Filter

namespace Matrix

/-- The first-coordinate resolvent of a Jacobi Gram matrix satisfies the
contracted Stieltjes recursion. -/
theorem powerSeriesResolvent_stieltjesJacobiMatrix_succ
    (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (c : ℝ) (n : ℕ) :
    powerSeriesResolvent (stieltjesJacobiMatrix a c (n + 1)) 0 0 =
      jacobiStep (c + a 0) (a 0 * a 1)
        (powerSeriesResolvent
          (stieltjesJacobiMatrix (fun k => a (k + 2)) (a 1) n) 0 0) := by
  have hcoup : (Real.sqrt (a 0) * Real.sqrt (a 1)) *
      (Real.sqrt (a 0) * Real.sqrt (a 1)) = a 0 * a 1 := by
    calc
      _ = Real.sqrt (a 0) ^ 2 * Real.sqrt (a 1) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (ha 0), Real.sq_sqrt (ha 1)]
  rw [powerSeriesResolvent_zero_eq_jacobiStep
    (stieltjesJacobiMatrix a c (n + 1))
    (Real.sqrt (a 0) * Real.sqrt (a 1)) (Real.sqrt (a 0) * Real.sqrt (a 1))
    (stieltjesJacobiMatrix_zero_succ a c n) (stieltjesJacobiMatrix_succ_zero a c n),
    hcoup, stieltjesJacobiMatrix_zero_zero a c (n + 1) (ha 0),
    stieltjesJacobiMatrix_submatrix_succ a c n (ha 1)]

/-- A finite Jacobi Gram resolvent agrees with its limiting formal Stieltjes
tail with first-diagonal correction through every degree below `2*n`. -/
theorem X_pow_dvd_resolvent_stieltjesJacobiMatrix_sub
    (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (c : ℝ) (n : ℕ) :
    (X : ℝ⟦X⟧) ^ (2 * n) ∣
      powerSeriesResolvent (stieltjesJacobiMatrix a c n) 0 0 -
        stieltjesStep c (stieltjesTail a 0) * stieltjesTail a 0 := by
  induction n generalizing a c with
  | zero => simp
  | succ n ih =>
      rw [powerSeriesResolvent_stieltjesJacobiMatrix_succ a ha c n,
        stieltjesStep_mul_tail_eq_jacobiStep]
      simpa only [Nat.mul_succ] using
        X_pow_dvd_jacobiStep_sub (c + a 0) (a 0 * a 1)
          (ih (fun k => a (k + 2)) (fun k => ha (k + 2)) (a 1))

/-- A sufficiently large finite Jacobi Gram matrix realizes a prescribed
coefficient of the infinite formal Stieltjes fraction as a matrix moment. -/
theorem pow_stieltjesJacobiMatrix_zero_zero_eq_coeff
    (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) {n k : ℕ} (hk : k < 2 * n) :
    (stieltjesJacobiMatrix a 0 n ^ k) 0 0 = coeff k (stieltjesTail a 0) := by
  have h := X_pow_dvd_iff.mp
    (X_pow_dvd_resolvent_stieltjesJacobiMatrix_sub a ha 0 n) k hk
  simpa only [map_sub, coeff_powerSeriesResolvent, stieltjesStep_zero,
    one_mul, sub_eq_zero] using h

/-- Each finite-matrix moment is eventually exactly the corresponding formal
Stieltjes coefficient. This is stronger than numerical convergence. -/
theorem eventually_pow_stieltjesJacobiMatrix_eq_coeff
    (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (k : ℕ) :
    ∀ᶠ n in atTop, (stieltjesJacobiMatrix a 0 n ^ k) 0 0 =
      coeff k (stieltjesTail a 0) := by
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  exact pow_stieltjesJacobiMatrix_zero_zero_eq_coeff a ha (by lia)

end Matrix
