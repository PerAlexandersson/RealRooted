/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Analysis.Complex.Hurwitz
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Necessary conditions for limits of zeros

We prove the elementary reverse direction of the Beraha--Kahane--Weiss theorem for finite
exponential sums. A unique nonzero dominant base with a nonvanishing coefficient excludes zeros
from a fixed ball for all sufficiently large indices. Consequently, a limit of zeros must have
two dominant bases, a vanishing coefficient at its unique dominant base, or only zero bases.

The results are the reverse implication in Sokal, *Combinatorics, Probability and Computing* 13
(2004), Theorem 1.5.
-/

public section

open Filter Topology Metric

noncomputable section

namespace Complex

/-- A nonzero unique dominant base with a nonvanishing coefficient excludes zeros from a fixed
ball for every sufficiently large index. This is the reverse direction of Sokal,
*Combinatorics, Probability and Computing* 13 (2004), Theorem 1.5. -/
theorem eventually_forall_ne_zero_of_unique_dominant {κ : Type*}
    (s : Finset κ) (α β : κ → ℂ → ℂ) (i : κ) {z₀ : ℂ} (hi : i ∈ s)
    (hα : ∀ k ∈ s, ContinuousAt (α k) z₀)
    (hβ : ∀ k ∈ s, ContinuousAt (β k) z₀)
    (hβi0 : β i z₀ ≠ 0)
    (hsmall : ∀ k ∈ s, k ≠ i → ‖β k z₀‖ < ‖β i z₀‖)
    (hαi0 : α i z₀ ≠ 0) :
    ∃ r > 0, ∀ᶠ n in atTop, ∀ z ∈ ball z₀ r,
      (∑ k ∈ s, α k z * β k z ^ n) ≠ 0 := by
  classical
  let t := s.erase i
  obtain ⟨r₁, hr₁, htail⟩ :=
    exists_ball_tendstoUniformlyOn_sum_mul_pow_zero t α
      (fun k z => β k z / β i z)
      (fun k hk => hα k (Finset.mem_of_mem_erase hk))
      (fun k hk => (hβ k (Finset.mem_of_mem_erase hk)).div (hβ i hi) hβi0)
      (fun k hk => by
        rw [norm_div]
        exact (div_lt_one (norm_pos_iff.mpr hβi0)).mpr
          (hsmall k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)))
  have hαnorm : 0 < ‖α i z₀‖ := norm_pos_iff.mpr hαi0
  have hquarter : 0 < ‖α i z₀‖ / 4 := by positivity
  have hnear : ∀ᶠ z in 𝓝 z₀,
      β i z ≠ 0 ∧ ‖α i z - α i z₀‖ < ‖α i z₀‖ / 4 := by
    refine ((hβ i hi).eventually_ne hβi0).and ?_
    have hzero : ‖α i z₀ - α i z₀‖ < ‖α i z₀‖ / 4 := by
      simpa using hquarter
    simpa using (((hα i hi).sub continuousAt_const).norm.eventually
      (eventually_lt_nhds hzero))
  obtain ⟨r₂, hr₂, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have htail' := Metric.tendstoUniformlyOn_iff.mp
    (htail.mono (ball_subset_ball (min_le_left r₁ r₂)))
      (‖α i z₀‖ / 4) hquarter
  refine ⟨r, hr, ?_⟩
  filter_upwards [htail'] with n hn z hz
  have hz₂ : z ∈ ball z₀ r₂ := ball_subset_ball (min_le_right r₁ r₂) hz
  have hβiz : β i z ≠ 0 := (hball hz₂).1
  have hclose : ‖α i z - α i z₀‖ < ‖α i z₀‖ / 4 := (hball hz₂).2
  have htailsmall : ‖∑ k ∈ t, α k z * (β k z / β i z) ^ n‖ <
      ‖α i z₀‖ / 4 := by
    simpa [dist_zero_right] using hn z hz
  have hfac : ∑ k ∈ s, α k z * β k z ^ n = β i z ^ n *
      (α i z + ∑ k ∈ t, α k z * (β k z / β i z) ^ n) := by
    have h0 := Finset.sum_erase_add s (fun k => α k z * β k z ^ n) hi
    have h1 : β i z ^ n * ∑ k ∈ t, α k z * (β k z / β i z) ^ n =
        ∑ k ∈ t, α k z * β k z ^ n := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [div_pow]
      field_simp
    dsimp [t] at h1 ⊢
    rw [mul_add, h1]
    linear_combination (-1 : ℂ) * h0
  rw [hfac]
  refine mul_ne_zero (pow_ne_zero n hβiz) ?_
  intro hzero
  have hαeq : α i z = -(∑ k ∈ t, α k z * (β k z / β i z) ^ n) := by
    linear_combination hzero
  have hle : ‖α i z₀‖ ≤ ‖α i z₀ - α i z‖ + ‖α i z‖ := by
    calc
      ‖α i z₀‖ = ‖(α i z₀ - α i z) + α i z‖ := by ring_nf
      _ ≤ ‖α i z₀ - α i z‖ + ‖α i z‖ := norm_add_le _ _
  have hclose' : ‖α i z₀ - α i z‖ < ‖α i z₀‖ / 4 := by
    rwa [norm_sub_rev]
  have hαnormz : ‖α i z‖ = ‖∑ k ∈ t, α k z * (β k z / β i z) ^ n‖ := by
    rw [hαeq, norm_neg]
  rw [hαnormz] at hle
  linarith

/-- Under unique dominance and nonvanishing of the dominant base and coefficient, the center is
not a liminf limit of zeros. This is the reverse direction of Sokal, *Combinatorics, Probability
and Computing* 13 (2004), Theorem 1.5. -/
theorem not_isLimitOfZeros_of_unique_dominant {κ : Type*}
    (s : Finset κ) (α β : κ → ℂ → ℂ) (i : κ) {z₀ : ℂ} (hi : i ∈ s)
    (hα : ∀ k ∈ s, ContinuousAt (α k) z₀)
    (hβ : ∀ k ∈ s, ContinuousAt (β k) z₀)
    (hβi0 : β i z₀ ≠ 0)
    (hsmall : ∀ k ∈ s, k ≠ i → ‖β k z₀‖ < ‖β i z₀‖)
    (hαi0 : α i z₀ ≠ 0) :
    ¬IsLimitOfZeros (fun n z => ∑ k ∈ s, α k z * β k z ^ n) z₀ := by
  intro hlim
  obtain ⟨r, hr, hne⟩ := eventually_forall_ne_zero_of_unique_dominant
    s α β i hi hα hβ hβi0 hsmall hαi0
  obtain ⟨n, hn, z, hz, hzero⟩ := (hne.and (hlim r hr)).exists
  exact hn z hz hzero

/-- **BKW only-if direction.** A liminf limit of zeros of a finite exponential sum has two
dominant bases, has a vanishing coefficient at its unique dominant base, or has all bases zero.
This is the reverse direction of Sokal, *Combinatorics, Probability and Computing* 13 (2004),
Theorem 1.5, with its zero-base degeneracy stated explicitly. -/
theorem isLimitOfZeros_imp_dominant_or_coeff_zero {κ : Type*}
    (s : Finset κ) (α β : κ → ℂ → ℂ) {z₀ : ℂ}
    (hα : ∀ k ∈ s, ContinuousAt (α k) z₀)
    (hβ : ∀ k ∈ s, ContinuousAt (β k) z₀)
    (hlim : IsLimitOfZeros (fun n z => ∑ k ∈ s, α k z * β k z ^ n) z₀) :
    (∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ ‖β i z₀‖ = ‖β j z₀‖ ∧
      ∀ k ∈ s, ‖β k z₀‖ ≤ ‖β i z₀‖) ∨
    (∃ i ∈ s, α i z₀ = 0 ∧
      ∀ k ∈ s, k ≠ i → ‖β k z₀‖ < ‖β i z₀‖) ∨
    (∀ k ∈ s, β k z₀ = 0) := by
  classical
  by_cases hall : ∀ k ∈ s, β k z₀ = 0
  · exact Or.inr (Or.inr hall)
  push Not at hall
  obtain ⟨k, hk, hβk0⟩ := hall
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun j => ‖β j z₀‖) ⟨k, hk⟩
  have hposi : 0 < ‖β i z₀‖ := (norm_pos_iff.mpr hβk0).trans_le (hmax k hk)
  have hβi0 : β i z₀ ≠ 0 := norm_pos_iff.mp hposi
  by_cases hunique : ∀ j ∈ s, j ≠ i → ‖β j z₀‖ < ‖β i z₀‖
  · right
    left
    refine ⟨i, hi, ?_, hunique⟩
    by_contra hαi0
    exact not_isLimitOfZeros_of_unique_dominant
      s α β i hi hα hβ hβi0 hunique hαi0 hlim
  · left
    push Not at hunique
    obtain ⟨j, hj, hji, hle⟩ := hunique
    exact ⟨i, hi, j, hj, hji.symm, le_antisymm hle (hmax j hj), hmax⟩

end Complex

namespace RealRooted

private theorem two_step_closed_form (w : ℕ → ℂ) (A B u v : ℂ)
    (hrec : ∀ n, w (n + 2) = A * w (n + 1) + B * w n)
    (hsum : u + v = A) (hprod : u * v = -B) (huv : u ≠ v) :
    ∀ n, w n = (w 1 - v * w 0) / (u - v) * u ^ n +
      (u * w 0 - w 1) / (u - v) * v ^ n := by
  have hden : u - v ≠ 0 := sub_ne_zero.mpr huv
  have hrootu : u ^ 2 = A * u + B := by
    rw [← hsum, ← neg_eq_iff_eq_neg.mpr hprod]
    ring
  have hrootv : v ^ 2 = A * v + B := by
    rw [← hsum, ← neg_eq_iff_eq_neg.mpr hprod]
    ring
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      simp only [pow_zero, mul_one]
      field_simp [hden]
      ring
  | one =>
      simp only [pow_one]
      field_simp [hden]
      ring
  | more n ih0 ih1 =>
      rw [hrec, ih0, ih1]
      simp only [pow_succ]
      linear_combination
        -((w 1 - v * w 0) / (u - v) * u ^ n) * hrootu -
        ((u * w 0 - w 1) / (u - v) * v ^ n) * hrootv

/-- An analytic order-two recurrence is not a liminf limit of zeros at a point where its
distinct characteristic roots have unequal norms and the dominant interpolation coefficient is
nonzero. This is the order-two reverse direction of Sokal, *Combinatorics, Probability and
Computing* 13 (2004), Theorem 1.5. -/
theorem not_isLimitOfZeros_two_step_of_roots {A B U V u v : ℂ → ℂ}
    {W : ℕ → ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h0 : W 0 = U) (h1 : W 1 = V)
    (hrec : ∀ n z, W (n + 2) z = A z * W (n + 1) z + B z * W n z)
    (hroots : ∀ z ∈ ball z₀ ρ, u z + v z = A z ∧ u z * v z = -B z ∧ u z ≠ v z)
    (hU : AnalyticAt ℂ U z₀) (hV : AnalyticAt ℂ V z₀)
    (hu : AnalyticAt ℂ u z₀) (hv : AnalyticAt ℂ v z₀)
    (hunu : u z₀ ≠ v z₀) (hnorm : ‖u z₀‖ ≠ ‖v z₀‖)
    (hcoeffu : ‖v z₀‖ < ‖u z₀‖ → V z₀ - v z₀ * U z₀ ≠ 0)
    (hcoeffv : ‖u z₀‖ < ‖v z₀‖ → u z₀ * U z₀ - V z₀ ≠ 0) :
    ¬Complex.IsLimitOfZeros W z₀ := by
  classical
  let αu : ℂ → ℂ := fun z => (V z - v z * U z) / (u z - v z)
  let αv : ℂ → ℂ := fun z => (u z * U z - V z) / (u z - v z)
  let α : Bool → ℂ → ℂ := fun k => if k then αu else αv
  let β : Bool → ℂ → ℂ := fun k => if k then u else v
  have hden : u z₀ - v z₀ ≠ 0 := sub_ne_zero.mpr hunu
  have hαu : AnalyticAt ℂ αu z₀ :=
    (hV.sub (hv.mul hU)).div (hu.sub hv) hden
  have hαv : AnalyticAt ℂ αv z₀ :=
    ((hu.mul hU).sub hV).div (hu.sub hv) hden
  have hα : ∀ k ∈ (Finset.univ : Finset Bool), ContinuousAt (α k) z₀ := by
    intro k _
    cases k with
    | false => simpa [α] using hαv.continuousAt
    | true => simpa [α] using hαu.continuousAt
  have hβ : ∀ k ∈ (Finset.univ : Finset Bool), ContinuousAt (β k) z₀ := by
    intro k _
    cases k with
    | false => simpa [β] using hv.continuousAt
    | true => simpa [β] using hu.continuousAt
  have hform (n : ℕ) (z : ℂ) (hz : z ∈ ball z₀ ρ) :
      W n z = αu z * u z ^ n + αv z * v z ^ n := by
    have hrz := hroots z hz
    simpa [αu, αv, ← h0, ← h1] using two_step_closed_form
      (fun m => W m z) (A z) (B z) (u z) (v z)
        (fun m => hrec m z) hrz.1 hrz.2.1 hrz.2.2 n
  rcases lt_or_gt_of_ne hnorm with huv | hvu
  · have hv0 : v z₀ ≠ 0 := norm_pos_iff.mp ((norm_nonneg (u z₀)).trans_lt huv)
    have hαv0 : αv z₀ ≠ 0 := div_ne_zero (hcoeffv huv) hden
    obtain ⟨r₁, hr₁, hne⟩ :=
      Complex.eventually_forall_ne_zero_of_unique_dominant
        (Finset.univ : Finset Bool) α β false (by simp) hα hβ
        (by simpa [β] using hv0)
        (by
          intro k _ hki
          cases k <;> simp_all [β])
        (by simpa [α] using hαv0)
    let r := min ρ r₁
    have hr : 0 < r := lt_min hρ hr₁
    intro hlim
    obtain ⟨n, hn, z, hz, hzero⟩ :=
      (hne.and (hlim r hr)).exists
    have hzρ : z ∈ ball z₀ ρ := ball_subset_ball (min_le_left ρ r₁) hz
    have hzr₁ : z ∈ ball z₀ r₁ := ball_subset_ball (min_le_right ρ r₁) hz
    apply hn z hzr₁
    simpa [α, β, Fintype.sum_bool, add_comm] using hform n z hzρ ▸ hzero
  · have hu0 : u z₀ ≠ 0 := norm_pos_iff.mp ((norm_nonneg (v z₀)).trans_lt hvu)
    have hαu0 : αu z₀ ≠ 0 := div_ne_zero (hcoeffu hvu) hden
    obtain ⟨r₁, hr₁, hne⟩ :=
      Complex.eventually_forall_ne_zero_of_unique_dominant
        (Finset.univ : Finset Bool) α β true (by simp) hα hβ
        (by simpa [β] using hu0)
        (by
          intro k _ hki
          cases k <;> simp_all [β])
        (by simpa [α] using hαu0)
    let r := min ρ r₁
    have hr : 0 < r := lt_min hρ hr₁
    intro hlim
    obtain ⟨n, hn, z, hz, hzero⟩ :=
      (hne.and (hlim r hr)).exists
    have hzρ : z ∈ ball z₀ ρ := ball_subset_ball (min_le_left ρ r₁) hz
    have hzr₁ : z ∈ ball z₀ r₁ := ball_subset_ball (min_le_right ρ r₁) hz
    apply hn z hzr₁
    simpa [α, β, Fintype.sum_bool, add_comm] using hform n z hzρ ▸ hzero

end RealRooted
