/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.StrictMoment
import RealRooted.Mathlib.MeasureTheory.Integral.HankelSupport

/-!
# Stieltjes fractions for measures with no finite carrier

The strict Hankel criterion applies to arbitrary nonnegative measures with
all natural moments whenever no finite set carries the measure. Atomicity,
compact support and analytic moment growth are not required.
-/

public section

open Polynomial MeasureTheory

namespace PowerSeries

/-- The moment series of a nonnegative measure with no finite carrier has a
strictly positive formal S-fraction. The outer scalar is its exact total mass. -/
theorem exists_pos_stieltjesTail_of_no_finite_carrier
    {mu : Measure ℝ} (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) mu)
    (hpos : ∀ᵐ x ∂mu, 0 ≤ x)
    (hfinite : ∀ S : Set ℝ, S.Finite → mu Sᶜ ≠ 0) :
    ∃ a : ℕ → ℝ, (∀ k, 0 < a k) ∧
      mk (fun k => ∫ x : ℝ, x ^ k ∂mu) = C (mu.real Set.univ) * stieltjesTail a 0 := by
  let m : ℕ → ℝ := fun k => ∫ x : ℝ, x ^ k ∂mu
  have hd (n : ℕ) : (momentHankelMatrix m n).PosDef := by
    simpa only [m, Nat.add_zero] using
      posDef_integral_pow_hankel_of_no_finite_carrier hmom hpos hfinite n 0
  have hs (n : ℕ) : (momentHankelMatrix (fun k => m (k + 1)) n).PosDef :=
    posDef_integral_pow_hankel_of_no_finite_carrier hmom hpos hfinite n 1
  obtain ⟨a, ha, _, hf⟩ := exists_pos_stieltjesTail_of_hankel_posDef m hd hs
  refine ⟨a, ha, ?_⟩
  simpa only [m, pow_zero, integral_const, smul_eq_mul, mul_one] using hf

end PowerSeries
