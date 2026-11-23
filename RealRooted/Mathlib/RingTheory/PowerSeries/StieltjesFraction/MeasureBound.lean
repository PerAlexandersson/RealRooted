/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.CatalanBound
import RealRooted.Mathlib.MeasureTheory.Measure.MomentDeterminacy

/-!
# Bounded support from bounded Stieltjes data

The Catalan coefficient estimate confines every genuine representing measure
to a bounded interval. Integrability of all natural powers is explicit; this
does not infer a measure from nonnegative coefficients alone.
-/

public section

namespace MeasureTheory

/-- Bounded nonnegative Stieltjes data exclude mass beyond every larger
absolute radius, for any genuine representing measure. -/
theorem measure_abs_ge_eq_zero_of_stieltjes_bound {mu : Measure ℝ}
    {a : ℕ → ℝ} {mass L T : ℝ} (hmass : 0 ≤ mass) (hL : 0 ≤ L) (hT : 4 * L < T)
    (ha : ∀ k, 0 ≤ a k) (haL : ∀ k, a k ≤ L)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu)
    (hmom : ∀ n, (∫ x : ℝ, x ^ n ∂mu) =
      mass * PowerSeries.coeff n (PowerSeries.stieltjesTail a 0)) :
    mu {x : ℝ | T ≤ |x|} = 0 := by
  apply measure_abs_ge_eq_zero_of_even_moment_bound (C := mass)
    (mul_nonneg (Nat.cast_nonneg 4) hL) hT (fun n => hint (2 * n))
  intro n
  rw [hmom]
  exact mul_le_mul_of_nonneg_left
    (PowerSeries.coeff_stieltjesTail_le_pow hL ha haL (2 * n) 0) hmass

/-- Every genuine representing measure of bounded nonnegative Stieltjes data
has bounded support; the deliberately loose radius also covers `L=0`. -/
theorem ae_abs_le_of_stieltjes_bound {mu : Measure ℝ}
    {a : ℕ → ℝ} {mass L : ℝ} (hmass : 0 ≤ mass) (hL : 0 ≤ L)
    (ha : ∀ k, 0 ≤ a k) (haL : ∀ k, a k ≤ L)
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) mu)
    (hmom : ∀ n, (∫ x : ℝ, x ^ n ∂mu) =
      mass * PowerSeries.coeff n (PowerSeries.stieltjesTail a 0)) :
    ∀ᵐ x ∂mu, |x| ≤ 4 * L + 1 := by
  have ht := measure_abs_ge_eq_zero_of_stieltjes_bound hmass hL
    (lt_add_one (4 * L)) ha haL hint hmom
  apply ae_iff.mpr
  apply measure_mono_null _ ht
  intro x hx
  exact (lt_of_not_ge hx).le

end MeasureTheory
