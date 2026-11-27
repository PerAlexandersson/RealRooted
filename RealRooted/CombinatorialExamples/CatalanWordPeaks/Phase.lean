/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Angular phase bounds and monotonicity

We merge the explicit checkpoint phase with its derivative estimate. The phase
is strictly increasing already for lengths greater than five; the quantitative
interior sine and cosine bounds retain the analytic cutoff 150.

Source: ProgramComputer, *Strict peaks in Catalan words*, analytic proof,
ISC license. Copyright 2026 ProgramComputer

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
-/

@[expose] public noncomputable section

namespace RealRooted.CatalanWordPeaks.CutGeometry

open Real

/-- The phase correction coming from the three near amplitude factors. -/
def phaseCorrection (θ : ℝ) : ℝ :=
  θ / 2 - π / 4 + (1 / 2) * arctan (sin θ / (1 + 2 * cos θ)) +
    2 * arctan (cos θ * sin θ / (1 + cos θ - cos θ ^ 2))

/-- The phase of the leading near-ray contribution, with its sign reversed. -/
def checkpointPhase (n : ℕ) (θ : ℝ) : ℝ :=
  (n : ℝ) * θ - phaseCorrection θ

private theorem phaseCorrection_den_pos {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2)) :
    0 < 1 + 2 * cos θ ∧ 1 ≤ 1 + cos θ - cos θ ^ 2 := by
  have hcos : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2⟩
  exact ⟨by positivity, by nlinarith [mul_nonneg hcos (sub_nonneg.mpr (cos_le_one θ))]⟩

private theorem phaseCorrection_arguments {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2)) :
    sin θ / (1 + 2 * cos θ) ∈ Set.Icc (0 : ℝ) 1 ∧
      cos θ * sin θ / (1 + cos θ - cos θ ^ 2) ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  have hsin : 0 ≤ sin θ := sin_nonneg_of_mem_Icc ⟨hθ.1, hθ.2.trans (by linarith [pi_pos])⟩
  have hcos : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2⟩
  obtain ⟨hA, hB⟩ := phaseCorrection_den_pos hθ
  have hB0 : 0 < 1 + cos θ - cos θ ^ 2 := zero_lt_one.trans_le hB
  refine ⟨⟨div_nonneg hsin hA.le, (div_le_one hA).2 ?_⟩,
    ⟨div_nonneg (mul_nonneg hcos hsin) hB0.le, (div_le_iff₀ hB0).2 ?_⟩⟩
  · linarith [sin_le_one θ]
  · have hprod : cos θ * sin θ ≤ 1 / 2 := by
      nlinarith [sin_sq_add_cos_sq θ, sq_nonneg (sin θ - cos θ)]
    linarith

/-- The phase correction satisfies the lower and upper bounds of the paper. -/
theorem phaseCorrection_bounds {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2)) :
    -(π / 4) ≤ phaseCorrection θ ∧ phaseCorrection θ ≤ π / 8 + 1 := by
  obtain ⟨hA, hB⟩ := phaseCorrection_arguments hθ
  have hA0 := arctan_strictMono.monotone hA.1
  have hA1 := arctan_strictMono.monotone hA.2
  have hB0 := arctan_strictMono.monotone hB.1
  have hB1 := arctan_strictMono.monotone hB.2
  have hhalf : arctan (1 / 2) ≤ 1 / 2 := arctan_le_self (by norm_num)
  rw [arctan_zero] at hA0 hB0
  rw [arctan_one] at hA1
  unfold phaseCorrection
  exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

/-- The correction starts at minus one quarter of pi. -/
theorem phaseCorrection_zero : phaseCorrection 0 = -(π / 4) := by
  simp [phaseCorrection, arctan_zero]

/-- The correction ends at one eighth of pi. -/
theorem phaseCorrection_pi_div_two : phaseCorrection (π / 2) = π / 8 := by
  simp only [phaseCorrection, sin_pi_div_two, cos_pi_div_two, mul_zero, zero_mul,
    add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, div_one,
    arctan_one, arctan_zero]
  ring

private theorem radial_sine_bound {n : ℕ} {x a : ℝ} (hn : 150 ≤ n)
    (ha : a ∈ Set.Ioc (0 : ℝ) 4) (hx : x ≤ π / 2) (hangle : a ≤ (n : ℝ) * x) :
    (399 / 400 : ℝ) * a < (n : ℝ) * sin x := by
  have hnR : (150 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnP : 0 < (n : ℝ) := by linarith
  let t := a / (n : ℝ)
  have ht : 0 < t := div_pos ha.1 hnP
  have ht' : t ≤ 1 / 10 := by
    exact (div_le_iff₀ hnP).2 (by linarith [ha.2])
  have htx : t ≤ x := by
    exact (div_le_iff₀ hnP).2 (by simpa only [mul_comm] using hangle)
  have hsin := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hx htx
  have hTaylor := sin_gt_sub_cube ht
  have hpow : t ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := (sq_le_sq₀ ht.le (by norm_num)).2 ht'
  have hlin : (399 / 400 : ℝ) * t ≤ t - t ^ 3 / 6 := by
    nlinarith [mul_le_mul_of_nonneg_left hpow ht.le]
  have hm := mul_lt_mul_of_pos_left (hlin.trans_lt (hTaylor.trans_le hsin)) hnP
  have hta : (n : ℝ) * t = a := by dsimp [t]; field_simp
  nlinarith

/-- At every point between the first and last interior phase levels, the
cosine and sine satisfy the quantitative radial premises. -/
theorem checkpointPhase_interior {n : ℕ} {θ : ℝ} (hn : 150 ≤ n)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (π / 2))
    (hfirst : π ≤ checkpointPhase n θ)
    (hlast : checkpointPhase n θ ≤ ((((n - 1) / 2 : ℕ) : ℝ) - 1) * π) :
    (29 / 10 : ℝ) ≤ (n : ℝ) * cos θ ∧ (2 : ℝ) ≤ (n : ℝ) * sin θ := by
  obtain ⟨hγlo, hγhi⟩ := phaseCorrection_bounds hθ
  unfold checkpointPhase at hfirst hlast
  have hθn : (9 / 4 : ℝ) ≤ (n : ℝ) * θ := by linarith [pi_gt_three]
  have hm : 2 * ((n - 1) / 2) + 1 ≤ n := by lia
  have hmR : 2 * ((((n - 1) / 2 : ℕ) : ℝ)) + 1 ≤ (n : ℝ) := by exact_mod_cast hm
  have hlast' : (n : ℝ) * θ - phaseCorrection θ ≤ ((n : ℝ) / 2 - 3 / 2) * π :=
    hlast.trans (mul_le_mul_of_nonneg_right (by linarith) pi_pos.le)
  have hΔn : (25 / 8 : ℝ) ≤ (n : ℝ) * (π / 2 - θ) := by
    nlinarith [pi_gt_three]
  have hc := radial_sine_bound hn (a := 25 / 8) (by constructor <;> norm_num)
    (by linarith [hθ.1]) hΔn
  have hs := radial_sine_bound hn (a := 9 / 4) (by constructor <;> norm_num) hθ.2 hθn
  rw [sin_pi_div_two_sub] at hc
  constructor <;> linarith

/-- The explicit correction is continuous up to both phase endpoints. -/
theorem continuousOn_phaseCorrection : ContinuousOn phaseCorrection (Set.Icc (0 : ℝ) (π / 2)) := by
  have hcos : ContinuousOn cos (Set.Icc (0 : ℝ) (π / 2)) := continuous_cos.continuousOn
  have hsin : ContinuousOn sin (Set.Icc (0 : ℝ) (π / 2)) := continuous_sin.continuousOn
  have hA : ContinuousOn (fun θ : ℝ => 1 + 2 * cos θ) (Set.Icc (0 : ℝ) (π / 2)) :=
    continuousOn_const.add (continuousOn_const.mul hcos)
  have hB : ContinuousOn (fun θ : ℝ => 1 + cos θ - cos θ ^ 2) (Set.Icc (0 : ℝ) (π / 2)) :=
    (continuousOn_const.add hcos).sub (hcos.pow 2)
  have hA' := continuous_arctan.comp_continuousOn
    (hsin.div hA (fun _ hθ => (phaseCorrection_den_pos hθ).1.ne'))
  have hB' := continuous_arctan.comp_continuousOn
    ((hcos.mul hsin).div hB (fun _ hθ => (zero_lt_one.trans_le (phaseCorrection_den_pos hθ).2).ne'))
  unfold phaseCorrection
  exact (((continuousOn_id.div_const 2).sub continuousOn_const).add
    (continuousOn_const.mul hA')).add (continuousOn_const.mul hB')

/-- The checkpoint phase is continuous on the closed angular interval. -/
theorem continuousOn_checkpointPhase (n : ℕ) :
    ContinuousOn (checkpointPhase n) (Set.Icc (0 : ℝ) (π / 2)) :=
  (continuousOn_const.mul continuousOn_id).sub continuousOn_phaseCorrection

end RealRooted.CatalanWordPeaks.CutGeometry

namespace RealRooted.CatalanWordPeaks.CutGeometry

open Real Set

private theorem phaseCorrection_hasDerivAt_le {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) (π / 2)) :
    ∃ v : ℝ, v ≤ 5 ∧ HasDerivAt phaseCorrection v θ := by
  let c := cos θ
  let s := sin θ
  let A := 1 + 2 * c
  let B := 1 + c - c ^ 2
  let f := s / A
  let g := c * s / B
  let f' := (c + 2) / A ^ 2
  let g' := ((c ^ 2 - s ^ 2) * B + (c * s) * (s * (1 - 2 * c))) / B ^ 2
  have hc : 0 ≤ c := cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2⟩
  have hc1 : c ≤ 1 := cos_le_one θ
  have hs : 0 ≤ s := sin_nonneg_of_mem_Icc ⟨hθ.1, hθ.2.trans (by linarith [pi_pos])⟩
  have hs1 : s ≤ 1 := sin_le_one θ
  have htrig : s ^ 2 + c ^ 2 = 1 := sin_sq_add_cos_sq θ
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hB : 1 ≤ B := by
    dsimp only [B]
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hc1)]
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hf : HasDerivAt (fun x => sin x / (1 + 2 * cos x)) f' θ := by
    convert (hasDerivAt_sin θ).div
      (((hasDerivAt_cos θ).const_mul 2).const_add 1) hApos.ne' using 1
    change (c + 2) / A ^ 2 = (c * A - s * (2 * -s)) / A ^ 2
    congr 1
    dsimp only [A]
    linear_combination -2 * htrig
  have hg : HasDerivAt (fun x => cos x * sin x / (1 + cos x - cos x ^ 2)) g' θ := by
    convert ((hasDerivAt_cos θ).mul (hasDerivAt_sin θ)).div
      (((hasDerivAt_cos θ).const_add 1).sub ((hasDerivAt_cos θ).pow 2)) hBpos.ne' using 1
    change ((c ^ 2 - s ^ 2) * B + (c * s) * (s * (1 - 2 * c))) / B ^ 2 =
      ((-s * s + c * c) * B - c * s * (-s - 2 * c ^ (2 - 1) * -s)) / B ^ 2
    norm_num only [Nat.reduceSub, pow_one]
    ring
  have hf' : f' ≤ 3 := by
    apply (div_le_iff₀ (pow_pos hApos 2)).2
    have hA2 : 1 ≤ A ^ 2 := by simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hA 2
    linarith
  have hg' : g' ≤ 3 / 2 := by
    apply (div_le_iff₀ (pow_pos hBpos 2)).2
    have h₁ : (c ^ 2 - s ^ 2) * B ≤ 1 * B :=
      mul_le_mul_of_nonneg_right (by linarith [sq_nonneg s]) hBpos.le
    have hslope : s * (1 - 2 * c) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left (show 1 - 2 * c ≤ 1 by linarith) hs
      rw [mul_one] at h
      exact h.trans hs1
    have hprod : c * s ≤ 1 / 2 := by nlinarith [sq_nonneg (s - c)]
    have h₂ : (c * s) * (s * (1 - 2 * c)) ≤ 1 / 2 := by
      have h := mul_le_mul_of_nonneg_left hslope (mul_nonneg hc hs)
      rw [mul_one] at h
      exact h.trans hprod
    have hB2 : 1 ≤ B ^ 2 := by simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hB 2
    have hB3 : B ≤ B ^ 2 := by
      rw [pow_two]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hB hBpos.le
    calc
      _ ≤ 1 * B + 1 / 2 := add_le_add h₁ h₂
      _ ≤ B ^ 2 + (1 / 2 : ℝ) * B ^ 2 := by
        simpa only [one_mul, mul_one] using
          add_le_add hB3 (mul_le_mul_of_nonneg_left hB2 (by norm_num : 0 ≤ (1 / 2 : ℝ)))
      _ = _ := by ring
  have hAatan : (1 / (1 + f ^ 2)) * f' ≤ 3 := by
    have hu : 1 / (1 + f ^ 2) ≤ 1 :=
      (div_le_one (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg _))
    exact (mul_le_mul_of_nonneg_left hf' (by positivity)).trans (by linarith)
  have hBatan : (1 / (1 + g ^ 2)) * g' ≤ 3 / 2 := by
    have hu : 1 / (1 + g ^ 2) ≤ 1 :=
      (div_le_one (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg _))
    exact (mul_le_mul_of_nonneg_left hg' (by positivity)).trans (by linarith)
  refine ⟨1 / 2 + (1 / 2) * ((1 / (1 + f ^ 2)) * f') +
    2 * ((1 / (1 + g ^ 2)) * g'), by linarith, ?_⟩
  unfold phaseCorrection
  simpa only [div_eq_mul_inv, one_mul, id_eq, f, g, A, B, c, s] using
    ((((hasDerivAt_id θ).div_const 2).sub_const (π / 4)).fun_add
      (hf.arctan.const_mul ((2 : ℝ)⁻¹))).fun_add (hg.arctan.const_mul 2)

/-- The phase strictly increases across the checkpoint interval for every
row at or above the analytic threshold. -/
theorem checkpointPhase_strictMonoOn {n : ℕ} (hn : 5 < n) :
    StrictMonoOn (checkpointPhase n) (Icc (0 : ℝ) (π / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuousOn_checkpointPhase n)
  intro θ hθ
  rw [interior_Icc] at hθ
  obtain ⟨v, hv, hderiv⟩ := phaseCorrection_hasDerivAt_le ⟨hθ.1.le, hθ.2.le⟩
  have h : HasDerivAt (checkpointPhase n) ((n : ℝ) - v) θ := by
    change HasDerivAt (fun x : ℝ ↦ (n : ℝ) * x - phaseCorrection x) _ θ
    simpa only [mul_one, id_eq] using!
      ((hasDerivAt_id θ).const_mul (n : ℝ)).fun_sub hderiv
  rw [h.deriv]
  have hnR : (5 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  linarith

end RealRooted.CatalanWordPeaks.CutGeometry
