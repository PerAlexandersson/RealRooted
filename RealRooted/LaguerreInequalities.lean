/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import RealRooted.LaguerreInequalities.CriticalPoint
public import RealRooted.LaguerreInequalities.Forms
import RealRooted.LaguerreInequalities.SignAlternation

/-!
# Two Laguerre inequalities and derivative descent

For a real polynomial `f` let `L₁ f = f' ^ 2 - f * f''` and
`L₂ f = (3 * f'' ^ 2 - 4 * f' * f''' + f * f⁽⁴⁾) / 12`
(`RealRooted.laguerreForm`, `RealRooted.secondLaguerreForm`).  We prove, for every nonzero `f`,

`f` splits over `ℝ` if and only if `f'` splits and `L₁ f t ≥ 0`, `L₂ f t ≥ 0` for all real `t`

(`RealRooted.splits_iff_splits_derivative_and_forms_nonneg`).  Constants and linear polynomials
are the base cases; repeated roots are allowed.

The forward direction is `RealRooted.Forms`: Rolle's theorem and the product formula for
`f (t + i y) * f (t - i y)`.  For the converse write `d = gcd (f, f')`, `f = d * F`, `f' = d * G`.
Then `G` splits and its roots are exactly the critical points of `f` that are not roots of `f`
(`RealRooted.LaguerreInequalities.CriticalPoint`: both forms force `f * f'' < 0` there, so these
critical points are simple).  The sign condition `F * G' < 0` at the roots of `G` makes `F`
alternate in sign, so `F` splits (`RealRooted.splits_of_eval_mul_derivative_neg`), and so does
`f = d * F`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- **Converse direction.** If `f ≠ 0`, `f'` splits and both Laguerre forms of `f` are
nonnegative on `ℝ`, then `f` splits. -/
theorem splits_of_splits_derivative_of_forms_nonneg {f : ℝ[X]} (hf : f ≠ 0)
    (hd : (derivative f).Splits) (h₁ : ∀ t : ℝ, 0 ≤ (laguerreForm f).eval t)
    (h₂ : ∀ t : ℝ, 0 ≤ (secondLaguerreForm f).eval t) : f.Splits := by
  rcases Nat.lt_or_ge f.natDegree 2 with hn | hn
  · exact Splits.of_natDegree_le_one (by lia)
  have hf' : derivative f ≠ 0 := derivative_ne_zero.mpr (by lia)
  obtain ⟨d, hdf, hdf', a, b, hab, hd0⟩ : ∃ d : ℝ[X], d ∣ f ∧ d ∣ derivative f ∧
      ∃ a b : ℝ[X], d = f * a + derivative f * b ∧ d ≠ 0 :=
    ⟨EuclideanDomain.gcd f (derivative f), EuclideanDomain.gcd_dvd_left _ _,
      EuclideanDomain.gcd_dvd_right _ _, _, _, EuclideanDomain.gcd_eq_gcd_ab _ _,
      fun h => hf (EuclideanDomain.gcd_eq_zero_iff.mp h).1⟩
  obtain ⟨F, hF⟩ := hdf
  obtain ⟨G, hG⟩ := hdf'
  have hF0 : F ≠ 0 := by
    rintro rfl
    exact hf (by simpa using hF)
  have hG0 : G ≠ 0 := by
    rintro rfl
    exact hf' (by simpa using hG)
  have hbez : F * a + G * b = 1 := by
    apply mul_left_cancel₀ hd0
    calc d * (F * a + G * b) = (d * F) * a + (d * G) * b := by ring
      _ = f * a + derivative f * b := by rw [← hF, ← hG]
      _ = d * 1 := by rw [← hab, mul_one]
  -- the roots of `G` are not roots of `F` or of `d`
  have hFG : ∀ ρ, G.eval ρ = 0 → F.eval ρ ≠ 0 := fun ρ hGρ hFρ => by
    have := congrArg (eval ρ) hbez
    simp [hFρ, hGρ] at this
  have hdG : ∀ ρ, G.eval ρ = 0 → d.eval ρ ≠ 0 := fun ρ hGρ hdρ => by
    have hmF : rootMultiplicity ρ F = 0 := rootMultiplicity_eq_zero (hFG ρ hGρ)
    have hmf : rootMultiplicity ρ f = rootMultiplicity ρ d := by
      conv_lhs => rw [hF]
      rw [rootMultiplicity_mul (mul_ne_zero hd0 hF0), hmF, add_zero]
    have hfroot : f.IsRoot ρ := by
      rw [hF]
      simp [IsRoot, hdρ]
    have hder := derivative_rootMultiplicity_of_root hfroot
    have hm' : rootMultiplicity ρ (derivative f) =
        rootMultiplicity ρ d + rootMultiplicity ρ G := by
      conv_lhs => rw [hG]
      rw [rootMultiplicity_mul (mul_ne_zero hd0 hG0)]
    have hgpos : 0 < rootMultiplicity ρ G := (rootMultiplicity_pos hG0).mpr hGρ
    have hdpos : 0 < rootMultiplicity ρ d := (rootMultiplicity_pos hd0).mpr hdρ
    lia
  have hGs : G.Splits := hd.of_dvd hf' (Dvd.intro_left d hG.symm)
  have hds : d.Splits := hd.of_dvd hf' (Dvd.intro G hG.symm)
  -- degrees and leading coefficients
  have hdeg : F.natDegree = G.natDegree + 1 := by
    have h1 := natDegree_mul hd0 hF0
    have h2 := natDegree_mul hd0 hG0
    rw [← hF] at h1
    rw [← hG] at h2
    have h3 := natDegree_derivative f
    lia
  have hlc : 0 < F.leadingCoeff * G.leadingCoeff := by
    have e1 : f.leadingCoeff = d.leadingCoeff * F.leadingCoeff := by
      rw [← leadingCoeff_mul, ← hF]
    have e2 : (derivative f).leadingCoeff = d.leadingCoeff * G.leadingCoeff := by
      rw [← leadingCoeff_mul, ← hG]
    have hld : d.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hd0
    have hlF : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF0
    have hGF : G.leadingCoeff = F.leadingCoeff * f.natDegree := by
      apply mul_left_cancel₀ hld
      rw [← e2, leadingCoeff_derivative, e1]
      ring
    rw [hGF]
    have hnpos : (0 : ℝ) < f.natDegree := by exact_mod_cast (by lia : 0 < f.natDegree)
    have := sq_pos_of_ne_zero hlF
    nlinarith
  -- the sign condition at the roots of `G`
  have hsign : ∀ ρ, G.IsRoot ρ → F.eval ρ * (derivative G).eval ρ < 0 := by
    intro ρ hρ
    have hGρ : G.eval ρ = 0 := hρ
    have hdρ := hdG ρ hGρ
    have hFρ := hFG ρ hGρ
    have hfρ' : (derivative f).eval ρ = 0 := by
      rw [hG]
      simp [hGρ]
    have hfe : f.eval ρ = d.eval ρ * F.eval ρ := by
      conv_lhs => rw [hF]
      simp
    have hff : (derivative (derivative f)).eval ρ = d.eval ρ * (derivative G).eval ρ := by
      rw [hG]
      simp [derivative_mul, hGρ]
    have key := eval_mul_eval_derivative_derivative_neg_of_forms_nonneg hf' h₁ h₂ hfρ'
      (by rw [hfe]; exact mul_ne_zero hdρ hFρ)
    rw [hff, hfe] at key
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (sq_nonneg (d.eval ρ)) hc]
  rw [hF]
  exact hds.mul (splits_of_eval_mul_derivative_neg hGs hdeg hlc hsign)

/-- **Two Laguerre inequalities and derivative descent.**  A real polynomial `f` splits over
`ℝ` if and only if `f'` splits and both Laguerre forms `L₁ f = f' ^ 2 - f * f''` and
`L₂ f = (3 * f'' ^ 2 - 4 * f' * f''' + f * f⁽⁴⁾) / 12` are nonnegative on `ℝ`.
Repeated roots are allowed, and constants and linear polynomials are included. -/
theorem splits_iff_splits_derivative_and_forms_nonneg (f : ℝ[X]) :
    f.Splits ↔ (derivative f).Splits ∧ ∀ t : ℝ,
      0 ≤ (laguerreForm f).eval t ∧ 0 ≤ (secondLaguerreForm f).eval t := by
  refine ⟨splits_derivative_and_forms_nonneg_of_splits, fun ⟨hd, h⟩ => ?_⟩
  rcases eq_or_ne f 0 with rfl | hf
  · exact Splits.zero
  exact splits_of_splits_derivative_of_forms_nonneg hf hd (fun t => (h t).1) fun t => (h t).2

/-- The second inequality cannot be dropped: `X ^ 4 - 1` has a split derivative and a
nonnegative first Laguerre form `4 t ^ 6 + 12 t ^ 2`, but `L₂ (X ^ 4 - 1) 0 = -2`, so it does
not split. -/
theorem exists_splits_derivative_laguerreForm_nonneg_not_splits :
    ∃ f : ℝ[X], (derivative f).Splits ∧ (∀ t : ℝ, 0 ≤ (laguerreForm f).eval t) ∧ ¬ f.Splits := by
  have h1 : derivative (X ^ 4 - 1 : ℝ[X]) = C 4 * X ^ 3 := by
    rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero]
    norm_num
  refine ⟨X ^ 4 - 1, ?_, ?_, ?_⟩
  · rw [h1]
    exact (Splits.C 4).mul (Splits.pow Splits.X 3)
  · intro t
    simp only [eval_laguerreForm, h1, derivative_mul, derivative_C, derivative_X_pow]
    simp
    nlinarith [sq_nonneg t, pow_two_nonneg (t ^ 2), sq_nonneg (t ^ 3)]
  · intro h
    have := ((splits_iff_splits_derivative_and_forms_nonneg _).mp h).2 0
    simp only [eval_secondLaguerreForm, h1, derivative_mul, derivative_C, derivative_X_pow] at this
    norm_num at this

end RealRooted
