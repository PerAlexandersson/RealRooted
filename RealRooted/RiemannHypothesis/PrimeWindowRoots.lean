/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta

public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi

public import RealRooted.Mathlib.NumberTheory.Chebyshev.PrimeWindowOrthogonal

import Mathlib.Algebra.Polynomial.Splits
import RealRooted.RiemannHypothesis.PrimeWindowJacobiRoots

/-!
# Prime-window roots approaching shifted Legendre roots under RH

For every fixed degree, RH gives eventually simple real prime-window roots.
Their increasing enumeration approaches the increasing shifted Legendre roots
with error `O(1 / log X)`. The nodes are produced by coefficient perturbation;
their real-rootedness is not an input assumption.
-/

public section

open Filter Topology Polynomial

namespace RiemannHypothesis

/-- Every fixed-degree prime-window polynomial has eventually simple real roots
whose ordered errors from the shifted Legendre roots are `O(1 / log X)`. -/
theorem exists_primeWindowPolynomial_roots_sub_le (hRH : RiemannHypothesis) (n : ℕ) :
    ∃ r : Fin n → ℝ, StrictMono r ∧
      (∀ i, (shiftedJacobiMonic n 0 0).IsRoot (r i)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
        (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).Splits ∧
        (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).roots.Nodup ∧
        ∃ s : Fin n → ℝ, StrictMono s ∧
          (∀ i, (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).IsRoot
            (s i)) ∧
          ∀ i, |s i - r i| ≤ C / Real.log X := by
  simpa only [RealRooted.shiftedJacobiWeight_zero_zero,
    Chebyshev.primeWindowWeightedPolynomial_one] using
      hRH.exists_primeWindowWeightedPolynomial_roots_sub_le
        (α := 0) (β := 0) (by norm_num) (by norm_num) n

/-- The ordered prime roots can be chosen as one family converging coordinatewise
to the actual ordered shifted Legendre roots, retaining the quantitative rate.
All root properties are eventual; the degree-zero enumeration is empty. -/
theorem exists_primeWindowPolynomial_roots_tendsto (hRH : RiemannHypothesis) (n : ℕ) :
    ∃ (r : Fin n → ℝ) (s : ℝ → Fin n → ℝ) (C : ℝ), 0 < C ∧ StrictMono r ∧
      (∀ i, (shiftedJacobiMonic n 0 0).IsRoot (r i)) ∧
      (∀ᶠ X : ℝ in atTop,
        (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).Splits ∧
        (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).roots.Nodup ∧
        StrictMono (s X) ∧
        (∀ i, (Chebyshev.primeWindowPolynomial X (Real.sqrt X * Real.log X ^ 3) n).IsRoot
          (s X i)) ∧
        ∀ i, |s X i - r i| ≤ C / Real.log X) ∧
      ∀ i, Tendsto (fun X : ℝ ↦ s X i) atTop (𝓝 (r i)) := by
  simpa only [RealRooted.shiftedJacobiWeight_zero_zero,
    Chebyshev.primeWindowWeightedPolynomial_one] using
      hRH.exists_primeWindowWeightedPolynomial_roots_tendsto
        (α := 0) (β := 0) (by norm_num) (by norm_num) n

end RiemannHypothesis
