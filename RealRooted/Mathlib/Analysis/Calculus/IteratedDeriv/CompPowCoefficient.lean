/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import TauCeti.Analysis.Analytic.OfScalars

/-!
# All Taylor coefficients after a power substitution

Substitution of `z ^ m` inserts zero coefficients outside the multiples of `m`.
-/

public section

/-- The complete Taylor coefficient formula for substitution of a positive power,
including the coefficients whose indices are not divisible by that power. -/
theorem iteratedDeriv_comp_pow_zero_eq {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f 0)
    {m : ℕ} (hm : 0 < m) (n : ℕ) :
    iteratedDeriv n (fun z => f (z ^ m)) 0 =
      if m ∣ n then (n.factorial : 𝕜) *
        (iteratedDeriv (n / m) f 0 / (n / m).factorial) else 0 := by
  obtain ⟨r, hr⟩ := hf.hasFPowerSeriesAt
  have hc := (hr.mono (lt_min hr.r_pos zero_lt_one) (min_le_left r 1)).comp_pow_ofScalars
    (min_le_right r 1) hm
  have h := hc.factorial_smul (1 : 𝕜) n
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, one_pow, one_smul,
    FormalMultilinearSeries.coeff_ofScalars, nsmul_eq_mul] at h
  rw [← iteratedDeriv_eq_iteratedFDeriv] at h
  rw [← h]
  split_ifs <;> simp
