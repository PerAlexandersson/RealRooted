/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Basic formal power series: sine, cosine, secant, and `sec + tan`

We work in `ℝ⟦X⟧`. Adapted from Aristotle's centered-disk proof,
`RequestProject/SeriesBasic.lean` (2026-10-23).
-/

@[expose] public section

open PowerSeries

namespace RealRooted.CenteredEulerian

/-- Formal sine. -/
noncomputable def sinS : ℝ⟦X⟧ := PowerSeries.sin ℝ
/-- Formal cosine. -/
noncomputable def cosS : ℝ⟦X⟧ := PowerSeries.cos ℝ
/-- Formal secant. -/
noncomputable def secS : ℝ⟦X⟧ := cosS⁻¹
/-- Formal `sec + tan`. -/
noncomputable def eulerS : ℝ⟦X⟧ := secS * (1 + sinS)
/-- `e k = E_k / k!`, the coefficients of `sec + tan`. -/
noncomputable def eulerCoeff (k : ℕ) : ℝ := coeff k eulerS

lemma coeff_sinS (n : ℕ) : coeff n sinS =
    if Even n then 0 else (-1 : ℝ) ^ (n / 2) / (n.factorial : ℝ) := by
  simp only [sinS, PowerSeries.sin, coeff_mk]
  split_ifs <;> simp

lemma coeff_cosS (n : ℕ) : coeff n cosS =
    if Even n then (-1 : ℝ) ^ (n / 2) / (n.factorial : ℝ) else 0 := by
  simp only [cosS, PowerSeries.cos, coeff_mk]
  split_ifs <;> simp

lemma constantCoeff_cosS : constantCoeff cosS = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_cosS]; simp

lemma constantCoeff_sinS : constantCoeff sinS = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_sinS]; simp

lemma cosS_mul_secS : cosS * secS = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_cosS]; norm_num)

lemma eulerS_mul_cosS : eulerS * cosS = 1 + sinS := by
  rw [eulerS, mul_right_comm, mul_comm secS, cosS_mul_secS, one_mul]

/-- The cosine series evaluated at a real point. -/
lemma hasSum_coeff_cosS (z : ℝ) :
    HasSum (fun n => coeff n cosS * z ^ n) (Real.cos z) := by
  have h := Real.hasSum_cos z
  have hinj : Function.Injective (fun n : ℕ => 2 * n) := fun a b h => by simpa using h
  rw [← hinj.hasSum_iff]
  · convert h using 1
    funext n
    simp only [Function.comp, coeff_cosS]
    rw [ite_eq_left (by simp)]
    simp [Nat.mul_div_cancel_left n two_pos]
    ring
  · intro m hm
    rw [coeff_cosS, ite_eq_right]
    · simp
    · rintro ⟨r, rfl⟩; exact hm ⟨r, by ring⟩

/-- The sine series evaluated at a real point. -/
lemma hasSum_coeff_sinS (z : ℝ) :
    HasSum (fun n => coeff n sinS * z ^ n) (Real.sin z) := by
  have h := Real.hasSum_sin z
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := fun a b h => by simpa using h
  rw [← hinj.hasSum_iff]
  · convert h using 1
    funext n
    simp only [Function.comp, coeff_sinS]
    rw [ite_eq_right (by simp)]
    have : (2 * n + 1) / 2 = n := by lia
    rw [this]
    ring
  · intro m hm
    rw [coeff_sinS, ite_eq_left]
    · simp
    · by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      obtain ⟨r, rfl⟩ := hodd
      exact hm ⟨r, rfl⟩

lemma abs_coeff_cosS_le (n : ℕ) : |coeff n cosS| ≤ 1 / (n.factorial : ℝ) := by
  rw [coeff_cosS]
  split_ifs
  · rw [abs_div, abs_pow]; simp
  · simp

lemma abs_coeff_sinS_le (n : ℕ) : |coeff n sinS| ≤ 1 / (n.factorial : ℝ) := by
  rw [coeff_sinS]
  split_ifs
  · simp
  · rw [abs_div, abs_pow]; simp

end RealRooted.CenteredEulerian
