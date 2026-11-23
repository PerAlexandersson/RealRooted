/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Tactic.Ring

/-!
# Recovering canonical Taylor coefficients from a scalar-series germ

A scalar series representing an analytic function near zero has its
actual derivatives divided by factorial as coefficients. For an entire
function, a real scalar-series germ extends to the same series everywhere
and proves conjugation symmetry. This makes real-entire source hypotheses
explicit rather than assuming symmetry in addition to a real expansion.
-/

public section

open Filter Topology
open scoped ComplexConjugate

namespace Complex

/-- Coefficients of an actual scalar-series germ are the canonical
Taylor derivatives divided by factorial. -/
theorem iteratedDeriv_div_factorial_eq_of_hasSum
    {f : ℂ → ℂ} {a : ℕ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hs : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n : ℕ ↦ a n * z ^ n) (f z)) (n : ℕ) :
    iteratedDeriv n f 0 / (n.factorial : ℂ) = a n := by
  have hp : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
    simpa only [hasFPowerSeriesAt_iff, FormalMultilinearSeries.coeff_ofScalars,
      zero_add, smul_eq_mul, mul_comm] using hs
  have heq := hf.hasFPowerSeriesAt.eq_formalMultilinearSeries hp
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p.coeff n) heq
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using hc

/-- Real scalar-series coefficients equal the real Taylor derivatives
with the same factorial normalization. -/
theorem re_iteratedDeriv_div_factorial_eq_of_hasSum
    {f : ℂ → ℂ} {a : ℕ → ℝ} (hf : AnalyticAt ℂ f 0)
    (hs : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n : ℕ ↦ (a n : ℂ) * z ^ n) (f z))
    (n : ℕ) : (iteratedDeriv n f 0).re / (n.factorial : ℝ) = a n := by
  have h := congrArg Complex.re (iteratedDeriv_div_factorial_eq_of_hasSum hf hs n)
  simpa only [Complex.div_natCast_re, Complex.ofReal_re] using h

/-- A scalar-series germ of an entire function represents the same
function at every complex argument. -/
theorem hasSum_of_entire_of_hasSum_germ {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : Differentiable ℂ f)
    (hs : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n : ℕ ↦ a n * z ^ n) (f z)) (z : ℂ) :
    HasSum (fun n : ℕ ↦ a n * z ^ n) (f z) := by
  have hc := iteratedDeriv_div_factorial_eq_of_hasSum (hf.analyticAt 0) hs
  convert hasSum_taylorSeries_of_entire hf 0 z using 1
  funext n
  rw [← hc n]
  simp only [sub_zero, smul_eq_mul, div_eq_mul_inv]
  ring

/-- An entire function represented near zero by real scalar coefficients
commutes with conjugation on the whole plane. -/
theorem conj_of_real_hasSum_germ {f : ℂ → ℂ} {a : ℕ → ℝ}
    (hf : Differentiable ℂ f)
    (hs : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun n : ℕ ↦ (a n : ℂ) * z ^ n) (f z))
    (z : ℂ) : f (conj z) = conj (f z) := by
  have hleft := hasSum_of_entire_of_hasSum_germ hf hs (conj z)
  have hright := Complex.hasSum_conj'.mpr (hasSum_of_entire_of_hasSum_germ hf hs z)
  apply hleft.unique
  simpa only [map_mul, map_pow, conj_ofReal] using hright

end Complex
