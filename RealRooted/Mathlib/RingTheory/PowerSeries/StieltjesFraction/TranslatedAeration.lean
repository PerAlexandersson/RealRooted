/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.ChainParameters
public import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialTransform
import RealRooted.Mathlib.RingTheory.PowerSeries.JacobiFraction.Aeration
import RealRooted.Mathlib.RingTheory.PowerSeries.JacobiFraction.ActiveCoefficients

/-!
# Chain extraction from a nonnegative translated aeration

A positive Stieltjes representation of the translated square-variable series
produces the bounded chain parameters. The proof compares Jacobi coefficients
only on their active prefix, so terminating series are included.
-/

public section

namespace PowerSeries

/-- A nonnegative Stieltjes representation after positive translated aeration
gives a Wall chain representation of the original fraction. -/
theorem exists_chainStieltjes_of_translated_aeration {kappa : ℝ} (hk : 0 < kappa)
    {a b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (heq : binomialTransform kappa ((stieltjesTail a 0).subst (X ^ 2 : ℝ⟦X⟧)) =
      stieltjesTail b 0) :
    ∃ g : ℕ → ℝ, g 0 = 0 ∧ (∀ n, g n ∈ Set.Icc 0 1) ∧
      stieltjesTail a 0 = stieltjesTail (chainStieltjesNumerators (kappa ^ 2) g) 0 := by
  have hcoeff (n : ℕ) (hact : ∀ i < n, a i ≠ 0) :
      kappa = stieltjesJacobiDiagonal b n ∧ a n = stieltjesJacobiNumerator b n :=
    jacobiCoefficients_eq_of_prefix_ne_zero
      (binomialTransform_subst_X_sq_stieltjesTail_eq_step kappa a)
      (stieltjesJacobiTail_eq_step b) heq n hact
  exact exists_chainStieltjes_of_constant_diagonal hk hb
    (fun n hn => (hcoeff n hn).1.symm) (fun n hn => (hcoeff n hn).2.symm)

end PowerSeries
