/-
Copyright (c) 2026 Matteo Cipollina, The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The entire Riemann xi function

The pole-subtracted completion defines the classical xi function also at `0` and `1`.
Its zeros are exactly the nontrivial zeros in Mathlib's `RiemannHypothesis`.

The definition and elementary identities are adapted from Tau Ceti's
`NumberTheory/LFunctions/Zeros/Completion/RiemannXi.lean` and
`NumberTheory/LSeries/CompletedRiemannZeta.lean`, revision
`b608709b45f23ccda55703d572b0adb1fdec30fd`. The proofs here use Mathlib directly,
and the zero-set characterization is stated without meromorphic divisors.
-/

@[expose] public section

open Complex

/-- The entire Riemann xi function, including the removable singularities at `0` and `1`. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

@[simp]
theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by
  simp [riemannXi]

@[simp]
theorem riemannXi_one : riemannXi 1 = 1 / 2 := by
  simp [riemannXi]

/-- The regularized xi function is entire. -/
theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  have := differentiable_completedZeta₀
  unfold riemannXi
  fun_prop

/-- The functional equation of the xi function. -/
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  simp only [riemannXi, completedRiemannZeta₀_one_sub]
  ring

/-- Away from the poles, the regularized definition agrees with the usual completion. -/
theorem riemannXi_eq_mul_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  rw [riemannXi, completedRiemannZeta_eq]
  field_simp
  ring

/-- The entire part of the completed zeta function respects conjugation. -/
theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (starRingEnd ℂ s) = starRingEnd ℂ (completedRiemannZeta₀ s) := by
  have h := completedRiemannZeta_conj s
  simp only [completedRiemannZeta_eq, map_sub, map_div₀, map_one] at h
  linear_combination h

/-- The xi function respects complex conjugation. -/
theorem riemannXi_conj (s : ℂ) :
    riemannXi (starRingEnd ℂ s) = starRingEnd ℂ (riemannXi s) := by
  simp [riemannXi, completedRiemannZeta₀_conj, map_ofNat]

private theorem completedRiemannZeta_ne_zero_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  intro h
  apply riemannZeta_ne_zero_of_one_lt_re hs
  rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]

private theorem completedRiemannZeta_neg_even_ne_zero (n : ℕ) :
    completedRiemannZeta (-2 * (n + 1)) ≠ 0 := by
  rw [← completedRiemannZeta_one_sub]
  apply completedRiemannZeta_ne_zero_of_one_lt
  simp only [sub_re, one_re, mul_re, neg_re, re_ofNat, add_re, natCast_re, neg_im,
    im_ofNat, add_im, natCast_im, one_im]
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The zeros of xi are exactly the nontrivial zeta zeros used in Mathlib's RH statement. -/
theorem riemannXi_eq_zero_iff (s : ℂ) :
    riemannXi s = 0 ↔
      riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1 := by
  rcases eq_or_ne s 0 with rfl | hs0
  · norm_num [riemannXi_zero, riemannZeta_zero]
  rcases eq_or_ne s 1 with rfl | hs1
  · simp
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1]
  have hsm : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  simp only [div_eq_zero_iff, mul_eq_zero, hs0, hsm, false_or,
    OfNat.ofNat_ne_zero, or_false]
  constructor
  · intro h
    refine ⟨?_, ?_, hs1⟩
    · rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
    · rintro ⟨n, rfl⟩
      exact completedRiemannZeta_neg_even_ne_zero n h
  · rintro ⟨h, htriv, -⟩
    rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at h
    rcases h with h | h
    · exact h
    · obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp h
      cases n with
      | zero =>
          simp only [Nat.cast_zero, mul_zero, neg_zero] at hn
          exact (hs0 hn).elim
      | succ n =>
          apply (htriv ⟨n, ?_⟩).elim
          rw [hn]
          push_cast
          ring

/-- Mathlib's Riemann hypothesis is equivalent to the critical-line statement for xi. -/
theorem riemannHypothesis_iff_riemannXi_zeros :
    RiemannHypothesis ↔ ∀ s : ℂ, riemannXi s = 0 → s.re = 1 / 2 := by
  constructor
  · intro h s hs
    obtain ⟨hz, htriv, hs1⟩ := (riemannXi_eq_zero_iff s).mp hs
    exact h s hz htriv hs1
  · intro h s hz htriv hs1
    exact h s ((riemannXi_eq_zero_iff s).mpr ⟨hz, htriv, hs1⟩)
