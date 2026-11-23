/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.FourierPolynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Derivatives of the xi Fourier-kernel summands

These are finite summand identities. Passing derivatives through the full infinite
series requires separate local uniform convergence estimates.
-/

public section

open Real Polynomial

/-- The explicit derivative expression of order `j` for the `n`-th Fourier summand. -/
@[expose] noncomputable def riemannXiFourierTerm (j n : ℕ) (t : ℝ) : ℝ :=
  π * (n : ℝ) ^ 2 * (riemannXiFourierPolynomial j).eval (π * (n : ℝ) ^ 2 * exp (4 * t)) *
    exp (5 * t - π * (n : ℝ) ^ 2 * exp (4 * t))

/-- Differentiating a Fourier summand advances its derivative-polynomial index. -/
theorem hasDerivAt_riemannXiFourierTerm (j n : ℕ) (t : ℝ) :
    HasDerivAt (riemannXiFourierTerm j n) (riemannXiFourierTerm (j + 1) n t) t := by
  let u (s : ℝ) := π * (n : ℝ) ^ 2 * exp (4 * s)
  have hu : HasDerivAt u (4 * u t) t := by
    convert (((hasDerivAt_id t).const_mul 4).exp).const_mul (π * (n : ℝ) ^ 2) using 1
    · simp only [u, id_eq]
    · simp only [u, id_eq, mul_one]
      ring
  have hv : HasDerivAt (fun s => exp (5 * s - u s))
      (exp (5 * t - u t) * (5 - 4 * u t)) t := by
    simpa using (((hasDerivAt_id t).const_mul 5).sub hu).exp
  have hp := (riemannXiFourierPolynomial j).hasDerivAt (u t)
  have h := ((hp.comp t hu).mul hv).const_mul (π * (n : ℝ) ^ 2)
  convert h using 1
  · funext s
    simp only [riemannXiFourierTerm, u, Pi.mul_apply, Function.comp_apply]
    ring
  · simp only [riemannXiFourierTerm, riemannXiFourierPolynomial_succ, eval_add,
      eval_mul, eval_sub, eval_X, eval_ofNat, u, Function.comp_apply]
    ring

/-- The polynomial formula is the actual derivative of every finite Fourier summand. -/
theorem iteratedDeriv_riemannXiFourierTerm (j n : ℕ) :
    iteratedDeriv j (riemannXiFourierTerm 0 n) = riemannXiFourierTerm j n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext fun t => (hasDerivAt_riemannXiFourierTerm j n t).deriv

/-- The first three Fourier summands, used for certified endpoint bounds. -/
@[expose] noncomputable def riemannXiFourierPartial (j : ℕ) (t : ℝ) : ℝ :=
  riemannXiFourierTerm j 1 t + riemannXiFourierTerm j 2 t + riemannXiFourierTerm j 3 t
