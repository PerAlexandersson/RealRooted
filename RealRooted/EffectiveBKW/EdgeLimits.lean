module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.Filter

/-!
# Phase limits at unbounded edges

Only the limits of the two phase contributions are needed. No uniform gap or amplitude
lower bound at infinity occurs in these lemmas. Either contribution may be a chosen lift.
-/

public section

open Filter Set
open scoped Topology

namespace RealRooted.EffectiveBKW

/-- Any limiting angle gives the corresponding affine phase limit at `-∞`.
In particular the angle may be any rational multiple of `π`. -/
theorem tendsto_phase_atBot_of_tendsto {θ δ : ℝ → ℝ} {α a₀ : ℝ} (n : ℕ)
    (hθ : Tendsto θ atBot (𝓝 α)) (hδ : Tendsto δ atBot (𝓝 a₀)) :
    Tendsto (fun t ↦ (n : ℝ) * θ t + δ t) atBot (𝓝 ((n : ℝ) * α + a₀)) := by
  exact (hθ.const_mul (n : ℝ)).add hδ

/-- A fractional limiting ray `π/k` gives phase limit `nπ/k + a₀` at `-∞`.
Applications take `k > 0`; the limit implication itself needs no restriction on `k`. -/
theorem tendsto_phase_div_atBot {θ δ : ℝ → ℝ} {a₀ : ℝ} (n k : ℕ)
    (hθ : Tendsto θ atBot (𝓝 (Real.pi / k))) (hδ : Tendsto δ atBot (𝓝 a₀)) :
    Tendsto (fun t ↦ (n : ℝ) * θ t + δ t) atBot
      (𝓝 ((n : ℝ) * Real.pi / k + a₀)) := by
  simpa only [mul_div_assoc] using tendsto_phase_atBot_of_tendsto n hθ hδ

/-- The phase limit at the left unbounded end is `nπ + a₀`. -/
theorem tendsto_phase_atBot {θ δ : ℝ → ℝ} {a₀ : ℝ} (n : ℕ)
    (hθ : Tendsto θ atBot (𝓝 Real.pi)) (hδ : Tendsto δ atBot (𝓝 a₀)) :
    Tendsto (fun t ↦ (n : ℝ) * θ t + δ t) atBot (𝓝 ((n : ℝ) * Real.pi + a₀)) := by
  exact tendsto_phase_atBot_of_tendsto n hθ hδ

/-- Every level below an arbitrary limiting affine phase is eventually exceeded at `-∞`. -/
theorem eventually_phase_gt_atBot_of_tendsto {θ δ : ℝ → ℝ} {α a₀ u : ℝ} (n : ℕ)
    (hθ : Tendsto θ atBot (𝓝 α)) (hδ : Tendsto δ atBot (𝓝 a₀))
    (hu : u < (n : ℝ) * α + a₀) :
    ∀ᶠ t in atBot, u < (n : ℝ) * θ t + δ t := by
  exact (tendsto_order.mp (tendsto_phase_atBot_of_tendsto n hθ hδ)).1 u hu

/-- Levels below a fractional limiting phase are eventually exceeded at `-∞`. -/
theorem eventually_phase_div_gt_atBot {θ δ : ℝ → ℝ} {a₀ u : ℝ} (n k : ℕ)
    (hθ : Tendsto θ atBot (𝓝 (Real.pi / k))) (hδ : Tendsto δ atBot (𝓝 a₀))
    (hu : u < (n : ℝ) * Real.pi / k + a₀) :
    ∀ᶠ t in atBot, u < (n : ℝ) * θ t + δ t := by
  exact (tendsto_order.mp (tendsto_phase_div_atBot n k hθ hδ)).1 u hu

/-- Every level strictly below the limiting phase is eventually exceeded at `-∞`. -/
theorem eventually_phase_gt_atBot {θ δ : ℝ → ℝ} {a₀ u : ℝ} (n : ℕ)
    (hθ : Tendsto θ atBot (𝓝 Real.pi)) (hδ : Tendsto δ atBot (𝓝 a₀))
    (hu : u < (n : ℝ) * Real.pi + a₀) :
    ∀ᶠ t in atBot, u < (n : ℝ) * θ t + δ t := by
  exact eventually_phase_gt_atBot_of_tendsto n hθ hδ hu

/-- An eventual phase bound at `-∞` gives a witness to the left of any fixed point.
The eventual membership hypothesis allows any interval containing a left ray. -/
theorem exists_phase_gt_left {φ : ℝ → ℝ} {J : Set ℝ} {u b : ℝ}
    (hφ : ∀ᶠ t in atBot, u < φ t) (hJ : ∀ᶠ t in atBot, t ∈ J) :
    ∃ a ∈ J, a < b ∧ u < φ a := by
  obtain ⟨a, hphase, hmem, hab⟩ :=
    (hφ.and (hJ.and (eventually_lt_atBot b))).exists
  exact ⟨a, hmem, hab, hphase⟩

end RealRooted.EffectiveBKW
