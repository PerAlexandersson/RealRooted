module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Basic
import RealRooted.Mathlib.Analysis.Complex.HeatOperator.TimeLimit
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatOperator
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure

/-!
# Laguerre--Pólya criteria from small positive heat times

An entire input of order below two is LP if and only if its backward heat
images are LP at arbitrarily small positive times. The reverse implication is
closure under locally uniform limits; it does not pass simplicity to time zero.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- LP heat images along any complex times tending to zero imply that the
original entire function is LP. -/
theorem IsLaguerrePolya.of_heatOperator_tendsto {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2)
    {t : ℕ → ℂ} (ht : Tendsto t atTop (𝓝 0))
    (hLP : ∀ n, IsLaguerrePolya (heatOperator (t n) f)) : IsLaguerrePolya f := by
  have h := tendstoLocallyUniformly_heatOperator_of_tendsto hf horder hρ ht
  rw [heatOperator_zero] at h
  exact IsLaguerrePolya.of_tendstoLocallyUniformly hLP h

/-- An entire function of order below two is LP exactly when its heat images
are LP at arbitrarily small positive real times. -/
theorem isLaguerrePolya_iff_heatOperator_near_zero {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) :
    IsLaguerrePolya f ↔ ∀ ε : ℝ, 0 < ε →
      ∃ t : ℝ, 0 < t ∧ t < ε ∧ IsLaguerrePolya (heatOperator (t : ℂ) f) := by
  constructor
  · intro hLP ε hε
    exact ⟨ε / 2, half_pos hε, half_lt_self hε,
      hLP.heatOperator horder hρ (half_pos hε).le⟩
  · intro h
    choose t ht hbound hLP using fun n : ℕ => h (1 / ((n : ℝ) + 1)) (by positivity)
    have hlim : Tendsto t atTop (𝓝 0) :=
      squeeze_zero (fun n => (ht n).le) (fun n => (hbound n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact IsLaguerrePolya.of_heatOperator_tendsto hf horder hρ
      (by simpa only [Function.comp_def, Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto 0).comp hlim) hLP

/-- An entire function of order below two is LP exactly when all of its
positive-time heat images are LP. -/
theorem isLaguerrePolya_iff_heatOperator_pos {f : ℂ → ℂ} {ρ : ℝ}
    (hf : Differentiable ℂ f) (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) :
    IsLaguerrePolya f ↔ ∀ t : ℝ, 0 < t → IsLaguerrePolya (heatOperator (t : ℂ) f) := by
  constructor
  · exact fun hLP _ ht => hLP.heatOperator horder hρ ht.le
  · intro h
    apply (isLaguerrePolya_iff_heatOperator_near_zero hf horder hρ).mpr
    intro ε hε
    exact ⟨ε / 2, half_pos hε, half_lt_self hε, h (ε / 2) (half_pos hε)⟩

end RealRooted
