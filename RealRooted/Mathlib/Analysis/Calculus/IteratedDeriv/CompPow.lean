/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import TauCeti.Analysis.Analytic.OfScalars

/-!
# Taylor coefficients after a power substitution

Substitution of `z ^ m` multiplies Taylor exponents by `m`. This gives the factorial
normalization of the iterated derivatives of the composite at zero.
-/

public section

/-- The Taylor coefficient of degree `m * k` after substituting `z ^ m` is the
original coefficient of degree `k`. -/
theorem iteratedDeriv_comp_pow_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f 0)
    {m : ℕ} (hm : 0 < m) (k : ℕ) :
    iteratedDeriv (m * k) (fun z => f (z ^ m)) 0 =
      ((m * k).factorial : 𝕜) * (iteratedDeriv k f 0 / k.factorial) := by
  obtain ⟨r, hr⟩ := hf.hasFPowerSeriesAt
  have hc := (hr.mono (lt_min hr.r_pos zero_lt_one) (min_le_left r 1)).comp_pow_ofScalars
    (min_le_right r 1) hm
  have h := hc.factorial_smul (1 : 𝕜) (m * k)
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, one_pow, one_smul,
    FormalMultilinearSeries.coeff_ofScalars, dvd_mul_right, ite_eq_left,
    Nat.mul_div_cancel_left _ hm, nsmul_eq_mul] at h
  rw [← iteratedDeriv_eq_iteratedFDeriv] at h
  exact h.symm
