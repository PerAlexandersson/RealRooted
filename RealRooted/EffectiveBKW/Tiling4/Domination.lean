module

public import RealRooted.EffectiveBKW.Tiling4.Branch
import RealRooted.EffectiveBKW.Domination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!+# Domination on the entire tiling pair ray

The scaled real root `u = r/t` lies between `-1` and `1`. The characteristic
equation expresses `t` rationally in `u`, and the gap and amplitude conditions
then factor into polynomials with elementary signs on this interval.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.Tiling4

open Set Filter
open scoped Topology

/-- The scaled real characteristic root. -/
noncomputable def scaledRoot (t : ℝ) : ℝ := realRoot t / t

/-- The scale lies in the fixed bounded interval `(-1,1)`. -/
theorem scaledRoot_mem {t : ℝ} (ht : t < 0) : scaledRoot t ∈ Ioo (-1 : ℝ) 1 := by
  obtain ⟨hlo, hhi⟩ := realRoot_mem ht
  constructor
  · apply (lt_div_iff_of_neg ht).mpr
    linarith
  · apply (div_lt_iff_of_neg ht).mpr
    linarith

/-- The rational expression for the original parameter in terms of the scaled root. -/
noncomputable def parameter (u : ℝ) : ℝ := (u ^ 2 + 2 * u - 1) / ((u - 1) ^ 2 * (u + 1))

/-- Scaling by `t` recovers the real root. -/
theorem mul_scaledRoot {t : ℝ} (ht : t ≠ 0) : t * scaledRoot t = realRoot t := by
  dsimp [scaledRoot]
  field_simp

/-- The characteristic equation is linear in `t` after scaling its real root. -/
theorem parameter_scaledRoot {t : ℝ} (ht : t < 0) : parameter (scaledRoot t) = t := by
  let u := scaledRoot t
  have hu := scaledRoot_mem ht
  have hden : (u - 1) ^ 2 * (u + 1) ≠ 0 := by
    have h₁ : u - 1 ≠ 0 := by dsimp [u]; linarith [hu.2]
    have h₂ : u + 1 ≠ 0 := by dsimp [u]; linarith [hu.1]
    exact mul_ne_zero (pow_ne_zero _ h₁) h₂
  have hroot := characteristic_realRoot ht
  rw [← mul_scaledRoot ht.ne] at hroot
  have hid : characteristic t (t * u) =
      t ^ 2 * (t * ((u - 1) ^ 2 * (u + 1)) - (u ^ 2 + 2 * u - 1)) := by
    dsimp [characteristic]
    ring
  change characteristic t (t * u) = 0 at hroot
  rw [hid] at hroot
  have heq := (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero 2 ht.ne)
  apply (div_eq_iff hden).mpr
  linarith

private theorem parameter_numerator_neg {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1)
    (ht : parameter u < 0) : u ^ 2 + 2 * u - 1 < 0 := by
  have hd : 0 < (u - 1) ^ 2 * (u + 1) := by
    have hne : u - 1 ≠ 0 := by linarith [hu.2]
    exact mul_pos (sq_pos_of_ne_zero hne) (by linarith [hu.1])
  change (u ^ 2 + 2 * u - 1) / ((u - 1) ^ 2 * (u + 1)) < 0 at ht
  simpa only [zero_mul] using (div_lt_iff₀ hd).mp ht

private theorem parameter_lower_bound {a u : ℝ} (ha : -1 < a) (hau : a ≤ u)
    (hu : u < 1 / 2) : -8 / (a + 1) ≤ parameter u := by
  have ha1 : 0 < a + 1 := by linarith
  have hu1 : 0 < u + 1 := by linarith
  have hs : (1 / 4 : ℝ) ≤ (u - 1) ^ 2 := by
    nlinarith [sq_nonneg (u - 1 / 2)]
  have hd : 0 < (u - 1) ^ 2 * (u + 1) := by
    exact mul_pos (by linarith) hu1
  have hdb : (a + 1) / 4 ≤ (u - 1) ^ 2 * (u + 1) := by
    have hm := mul_le_mul hs (show a + 1 ≤ u + 1 by linarith)
      (by linarith : 0 ≤ a + 1) (by linarith : (0 : ℝ) ≤ (u - 1) ^ 2)
    nlinarith
  have hn : -2 ≤ u ^ 2 + 2 * u - 1 := by nlinarith [sq_nonneg (u + 1)]
  apply (div_le_div_iff₀ ha1 hd).mpr
  have hp := mul_nonneg (show 0 ≤ u ^ 2 + 2 * u - 1 + 2 by linarith) ha1.le
  nlinarith

/-- At the unbounded left edge the scaled real mode tends to `-1`, without a series expansion. -/
theorem tendsto_scaledRoot_atBot : Tendsto scaledRoot atBot (𝓝 (-1 : ℝ)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
    exact ha.trans (scaledRoot_mem ht).1
  · intro b hb
    filter_upwards [eventually_lt_atBot (min (0 : ℝ) (-8 / (b + 1)))] with t ht
    have ht0 : t < 0 := ht.trans_le (min_le_left _ _)
    have hu := scaledRoot_mem ht0
    have hn := parameter_numerator_neg hu (by rwa [parameter_scaledRoot ht0])
    have hhalf : scaledRoot t < 1 / 2 := by nlinarith [sq_nonneg (scaledRoot t)]
    by_contra h
    have hl := parameter_lower_bound hb (le_of_not_gt h) hhalf
    rw [parameter_scaledRoot ht0] at hl
    linarith [ht.trans_le (min_le_right (0 : ℝ) (-8 / (b + 1)))]

private theorem gap_factor {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    gapCondition (parameter u) (parameter u * u) =
      (u ^ 2 + 2 * u - 1) * (u ^ 3 + u ^ 2 - u + 1) /
        ((u - 1) ^ 4 * (u + 1)) := by
  have hminus : u - 1 ≠ 0 := by linarith [hu.2]
  have hplus : u + 1 ≠ 0 := by linarith [hu.1]
  dsimp [gapCondition, parameter]
  field_simp
  ring

private theorem real_factor {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    realCondition (parameter u) (parameter u * u) =
      (u ^ 2 + 2 * u - 1) * (3 * u ^ 2 + 2 * u + 1) /
        ((u - 1) ^ 3 * (u + 1) ^ 2) := by
  have hminus : u - 1 ≠ 0 := by linarith [hu.2]
  have hplus : u + 1 ≠ 0 := by linarith [hu.1]
  dsimp [realCondition, characteristicDeriv, parameter]
  field_simp
  ring

private theorem domination_factor {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    dominationCondition (parameter u) (parameter u * u) =
      4 * (u ^ 2 + 2 * u - 1) ^ 3 *
        (2 * u ^ 6 - 5 * u ^ 4 + 2 * u ^ 3 - 11 * u ^ 2 - 2) /
          ((u - 1) ^ 10 * (u + 1) ^ 4) := by
  have hminus : u - 1 ≠ 0 := by linarith [hu.2]
  have hplus : u + 1 ≠ 0 := by linarith [hu.1]
  dsimp [dominationCondition, imagCondition, realCondition, characteristicDeriv,
    pairImagSq, pairNormSq, pairReal, parameter]
  field_simp
  ring

private theorem imag_factor {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    imagCondition (parameter u) (parameter u * u) =
      2 * (u ^ 2 + 2 * u - 1) * (4 * u ^ 3 - 3 * u ^ 2 + 2 * u - 1) /
        ((u - 1) ^ 5 * (u + 1) ^ 2) := by
  have hminus : u - 1 ≠ 0 := by linarith [hu.2]
  have hplus : u + 1 ≠ 0 := by linarith [hu.1]
  dsimp [imagCondition, realCondition, characteristicDeriv, parameter]
  field_simp
  ring

private theorem imag_negative_factor {u : ℝ} (hn : u ^ 2 + 2 * u - 1 < 0) :
    4 * u ^ 3 - 3 * u ^ 2 + 2 * u - 1 < 0 := by
  have hhalf : u < 1 / 2 := by nlinarith [sq_nonneg u]
  by_cases hu : 0 ≤ u
  · have hp : 0 ≤ u ^ 2 * (1 / 2 - u) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith [sq_nonneg u]
  · have h₃ : u ^ 3 < 0 :=
      (show Odd (3 : ℕ) by decide).pow_neg_iff.mpr (lt_of_not_ge hu)
    nlinarith [sq_nonneg u]

private theorem gap_positive_factor {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    0 < u ^ 3 + u ^ 2 - u + 1 := by
  have hp : 0 ≤ u ^ 2 * (u + 1) := mul_nonneg (sq_nonneg _) (by linarith [hu.1])
  nlinarith [hu.2]

private theorem domination_negative_factor {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    2 * u ^ 6 - 5 * u ^ 4 + 2 * u ^ 3 - 11 * u ^ 2 - 2 < 0 := by
  have hs : u ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ u + 1 by linarith [hu.1])
      (show 0 ≤ 1 - u by linarith [hu.2])]
  have h₆ : 0 ≤ u ^ 4 * (1 - u ^ 2) := mul_nonneg (by positivity)
    (sub_nonneg.mpr hs)
  have h₃ : 0 ≤ u ^ 2 * (1 - u) := mul_nonneg (sq_nonneg _) (by linarith [hu.2])
  nlinarith [sq_nonneg (u ^ 2)]

/-- The real mode is strictly smaller in modulus at every negative parameter. -/
theorem gapCondition_realRoot_neg {t : ℝ} (ht : t < 0) :
    gapCondition t (realRoot t) < 0 := by
  have hu := scaledRoot_mem ht
  have hn := parameter_numerator_neg hu (by rwa [parameter_scaledRoot ht])
  suffices h : gapCondition (parameter (scaledRoot t))
      (parameter (scaledRoot t) * scaledRoot t) < 0 by
    simpa only [parameter_scaledRoot ht, mul_scaledRoot ht.ne] using h
  rw [gap_factor hu]
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos hn (gap_positive_factor hu)
  · have hne : scaledRoot t - 1 ≠ 0 := by linarith [hu.2]
    exact mul_pos (by positivity) (by linarith [hu.1])

/-- The real part of the dominant amplitude is positive on the entire negative ray. -/
theorem realCondition_realRoot_pos {t : ℝ} (ht : t < 0) :
    0 < realCondition t (realRoot t) := by
  have hu := scaledRoot_mem ht
  have hn := parameter_numerator_neg hu (by rwa [parameter_scaledRoot ht])
  suffices h : 0 < realCondition (parameter (scaledRoot t))
      (parameter (scaledRoot t) * scaledRoot t) by
    simpa only [parameter_scaledRoot ht, mul_scaledRoot ht.ne] using h
  rw [real_factor hu]
  have hq : 0 < 3 * scaledRoot t ^ 2 + 2 * scaledRoot t + 1 := by
    nlinarith [sq_nonneg (3 * scaledRoot t + 1)]
  apply div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hn hq)
  exact mul_neg_of_neg_of_pos ((show Odd (3 : ℕ) by decide).pow_neg_iff.mpr
    (sub_neg.mpr hu.2))
    (sq_pos_of_ne_zero (by linarith [hu.1]))

/-- Strict amplitude domination holds on the entire negative parameter ray. -/
theorem dominationCondition_realRoot_pos {t : ℝ} (ht : t < 0) :
    0 < dominationCondition t (realRoot t) := by
  have hu := scaledRoot_mem ht
  have hn := parameter_numerator_neg hu (by rwa [parameter_scaledRoot ht])
  suffices h : 0 < dominationCondition (parameter (scaledRoot t))
      (parameter (scaledRoot t) * scaledRoot t) by
    simpa only [parameter_scaledRoot ht, mul_scaledRoot ht.ne] using h
  rw [domination_factor hu]
  apply div_pos
  · exact mul_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg (by norm_num) ((show Odd (3 : ℕ) by decide).pow_neg_iff.mpr hn))
      (domination_negative_factor hu)
  · have hne : scaledRoot t - 1 ≠ 0 := by linarith [hu.2]
    exact mul_pos (by positivity)
      (pow_pos (by linarith [hu.1]) 4)

/-- The imaginary-amplitude numerator is negative throughout the negative parameter ray. -/
theorem imagCondition_realRoot_neg {t : ℝ} (ht : t < 0) :
    imagCondition t (realRoot t) < 0 := by
  have hu := scaledRoot_mem ht
  have hn := parameter_numerator_neg hu (by rwa [parameter_scaledRoot ht])
  suffices h : imagCondition (parameter (scaledRoot t))
      (parameter (scaledRoot t) * scaledRoot t) < 0 by
    simpa only [parameter_scaledRoot ht, mul_scaledRoot ht.ne] using h
  rw [imag_factor hu]
  apply div_neg_of_pos_of_neg
  · exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by norm_num) hn)
      (imag_negative_factor hn)
  · exact mul_neg_of_neg_of_pos ((show Odd (5 : ℕ) by decide).pow_neg_iff.mpr
      (sub_neg.mpr hu.2)) (sq_pos_of_ne_zero (by linarith [hu.1]))

private theorem imagCondition_eq {t r : ℝ} (hy : 0 < pairImagSq t r) :
    imagCondition t r =
      4 * characteristicDeriv t r * pairImag t r * (amplitude t r).im := by
  have hd := (characteristicDeriv_pos hy).ne'
  have hi := (pairImag_pos hy).ne'
  dsimp [imagCondition, realCondition, amplitude, thirdAmplitude, pairReal]
  field_simp
  ring

/-- The dominant amplitude lies in the open lower half-plane on the pair ray. -/
theorem amplitude_im_neg {t : ℝ} (ht : t < rightEdge) :
    (amplitude t (realRoot t)).im < 0 := by
  have hy := pairImagSq_realRoot_pos ht
  have hI := imagCondition_realRoot_neg (ht.trans rightEdge_neg)
  rw [imagCondition_eq hy] at hI
  have hpos : 0 < 4 * characteristicDeriv t (realRoot t) * pairImag t (realRoot t) := by
    have := characteristicDeriv_pos hy
    have := pairImag_pos hy
    positivity
  nlinarith

/-- The exact pair dominates the single real remainder at every positive index. -/
theorem expansion_dom : expansion.Dom (Iio rightEdge) 1 := by
  apply pairExpansion_dom
  · intro t ht
    exact gapCondition_realRoot_neg (ht.trans rightEdge_neg)
  · intro t ht
    exact dominationCondition_realRoot_pos (ht.trans rightEdge_neg)

end RealRooted.EffectiveBKW.Tiling4
