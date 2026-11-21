module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import RealRooted.EffectiveBKW.EdgeLimits
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A cubic fractional ray

For a negative parameter `s`, the upper reciprocal root of
`(1-z)³ - s³ z³` is `1-s w`, where `w = (1+i√3)/2`. Its angle tends to `π/3`
as `s → -∞`. Thus the cubic example has a fractional limiting phase slope.
This example checks the spectral branch and phase limit, not a row-root theorem.
-/

@[expose] public section

open Filter
open scoped Topology

namespace RealRooted.EffectiveBKW.Examples.FractionalRay

/-- The cube root of `-1` in the upper right quadrant. -/
noncomputable def direction : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

/-- The upper reciprocal root at parameter `t = s³`, for `s < 0`. -/
noncomputable def lam (s : ℝ) : ℂ := 1 - (s : ℂ) * direction

/-- The angle of the reciprocal root after division by the positive scale `-s`. -/
noncomputable def angle (s : ℝ) : ℝ := (((-s)⁻¹ : ℝ) + direction : ℂ).arg

/-- The direction satisfies the exact cubic equation. -/
theorem direction_cube : direction ^ 3 = -1 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by rw [pow_succ, hs]
  apply Complex.ext <;> simp [direction, pow_succ, Complex.mul_re, Complex.mul_im]
  · nlinarith
  · nlinarith [hc]

/-- The selected branch is a reciprocal root of `(1-z)³ - s³ z³`. -/
theorem lam_cubic (s : ℝ) : (lam s - 1) ^ 3 = (s : ℂ) ^ 3 := by
  calc
    _ = -(s : ℂ) ^ 3 * direction ^ 3 := by unfold lam; ring
    _ = _ := by rw [direction_cube]; ring

/-- The selected reciprocal root lies in the upper half-plane on the negative ray. -/
theorem lam_im_pos {s : ℝ} (hs : s < 0) : 0 < (lam s).im := by
  have hroot : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  simp only [lam, direction, Complex.sub_im, Complex.one_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  nlinarith

/-- Positive rescaling preserves the chosen argument on the negative ray. -/
theorem angle_eq_arg {s : ℝ} (hs : s < 0) : angle s = (lam s).arg := by
  have he : lam s = (-s : ℝ) * (((-s)⁻¹ : ℝ) + direction : ℂ) := by
    dsimp [lam]
    push_cast
    field_simp [hs.ne]
    ring
  rw [he, Complex.arg_real_mul _ (neg_pos.mpr hs)]
  rfl

/-- The limiting direction has principal argument `π/3`. -/
theorem arg_direction : direction.arg = Real.pi / 3 := by
  have hangle : Real.pi / 3 ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have he : direction = (Real.cos (Real.pi / 3) : ℂ) +
      Real.sin (Real.pi / 3) * Complex.I := by
    rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
    apply Complex.ext <;> simp [direction]
  rw [he]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
    Complex.arg_cos_add_sin_mul_I hangle

/-- The cubic spectral angle tends to a third of `π` at the unbounded end. -/
theorem tendsto_angle : Tendsto angle atBot (𝓝 (Real.pi / 3)) := by
  have hreal : Tendsto (fun s : ℝ ↦ (-s)⁻¹) atBot (𝓝 0) := by
    simpa only [inv_neg, neg_zero] using
      (tendsto_inv_atBot_zero : Tendsto (fun s : ℝ ↦ s⁻¹) atBot (𝓝 0)).neg
  have hz : Tendsto (fun s : ℝ ↦ (((-s)⁻¹ : ℝ) + direction : ℂ)) atBot
      (𝓝 direction) := by
    simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp hreal).add_const direction
  have hslit : direction ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    norm_num [direction]
  change Tendsto (fun s : ℝ ↦ (((-s)⁻¹ : ℝ) + direction : ℂ).arg) atBot
    (𝓝 (Real.pi / 3))
  simpa only [Function.comp_def, arg_direction] using
    (Complex.continuousAt_arg hslit).tendsto.comp hz

/-- Any convergent amplitude phase gives the fractional cubic phase limit. -/
theorem tendsto_phase {δ : ℝ → ℝ} {a₀ : ℝ} (n : ℕ)
    (hδ : Tendsto δ atBot (𝓝 a₀)) :
    Tendsto (fun s ↦ (n : ℝ) * angle s + δ s) atBot
      (𝓝 ((n : ℝ) * Real.pi / 3 + a₀)) := by
  exact tendsto_phase_div_atBot n 3 tendsto_angle hδ

/-- With zero amplitude phase, the cubic phase has limit `nπ/3` without hypotheses. -/
theorem tendsto_mul_angle (n : ℕ) :
    Tendsto (fun s ↦ (n : ℝ) * angle s) atBot (𝓝 ((n : ℝ) * Real.pi / 3)) := by
  simpa only [add_zero] using
    tendsto_phase (δ := fun _ ↦ 0) n (tendsto_const_nhds : Tendsto _ atBot (𝓝 (0 : ℝ)))

end RealRooted.EffectiveBKW.Examples.FractionalRay
