module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

/-!
# Trigonometric families and a one-variable implicit function theorem

`trigFamily` is the real or imaginary part of `b(ρ e^{iθ}) = (ρ e^{iθ})⁻¹ + ρ e^{iθ} +
∑ c_j (ρ e^{iθ})^j`; we compute its derivative along a curve `t ↦ (θ(t), ρ(t))`.  We also
wrap Mathlib's bivariate implicit function theorem for a real family `F θ ρ`.
-/

@[expose] public section

open Polynomial Filter Topology

noncomputable section

namespace RealRooted.ToeplitzPerturbation

section TrigFamily

variable (s : ℕ) (c : ℕ → ℝ) (σ : ℝ) (T T' : ℝ → ℝ)

/-- The family `(ρ + σ ρ⁻¹) T(θ) + ∑_j c_j ρ^j T(jθ)`; `σ = -1, T = sin` gives `Im b` and
`σ = 1, T = cos` gives `Re b`. -/
def trigFamily (θ ρ : ℝ) : ℝ :=
  (ρ + σ * ρ⁻¹) * T θ + ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ j * T (j * θ)

/-- Partial derivative of `trigFamily` in `θ`. -/
def trigFamilyθ (θ ρ : ℝ) : ℝ :=
  (ρ + σ * ρ⁻¹) * T' θ + ∑ j ∈ Finset.Icc 2 s, c j * ρ ^ j * (j * T' (j * θ))

/-- Partial derivative of `trigFamily` in `ρ`. -/
def trigFamilyρ (θ ρ : ℝ) : ℝ :=
  (1 - σ * (ρ ^ 2)⁻¹) * T θ + ∑ j ∈ Finset.Icc 2 s, c j * (j * ρ ^ (j - 1)) * T (j * θ)

variable {s c σ T T'}

theorem hasDerivAt_trigFamily (hT : ∀ t, HasDerivAt T (T' t) t) {θ ρ : ℝ → ℝ} {θ' ρ' t₀ : ℝ}
    (hθ : HasDerivAt θ θ' t₀) (hρ : HasDerivAt ρ ρ' t₀) (hne : ρ t₀ ≠ 0) :
    HasDerivAt (fun t => trigFamily s c σ T (θ t) (ρ t))
      (trigFamilyθ s c σ T' (θ t₀) (ρ t₀) * θ' + trigFamilyρ s c σ T (θ t₀) (ρ t₀) * ρ') t₀ := by
  have h1 : HasDerivAt (fun t => (ρ t + σ * (ρ t)⁻¹) * T (θ t))
      ((ρ' + σ * (-(ρ') / ρ t₀ ^ 2)) * T (θ t₀) + (ρ t₀ + σ * (ρ t₀)⁻¹) * (T' (θ t₀) * θ')) t₀ :=
    (hρ.add ((hρ.inv hne).const_mul σ)).mul ((hT _).comp t₀ hθ)
  have h2 : ∀ j ∈ Finset.Icc 2 s, HasDerivAt (fun t => c j * ρ t ^ j * T (j * θ t))
      (c j * (j * ρ t₀ ^ (j - 1) * ρ') * T (j * θ t₀) +
        c j * ρ t₀ ^ j * (T' (j * θ t₀) * (j * θ'))) t₀ := by
    intro j _
    exact ((hρ.pow j).const_mul (c j)).mul ((hT _).comp t₀ (hθ.const_mul (j : ℝ)))
  refine (h1.add (HasDerivAt.fun_sum h2)).congr_deriv ?_
  simp only [trigFamilyθ, trigFamilyρ, add_mul, Finset.sum_mul, Finset.sum_add_distrib]
  have e1 : ∑ x ∈ Finset.Icc 2 s, c x * (x * ρ t₀ ^ (x - 1) * ρ') * T (x * θ t₀) =
      ∑ x ∈ Finset.Icc 2 s, c x * (x * ρ t₀ ^ (x - 1)) * T (x * θ t₀) * ρ' :=
    Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ x ∈ Finset.Icc 2 s, c x * ρ t₀ ^ x * (T' (x * θ t₀) * (x * θ')) =
      ∑ x ∈ Finset.Icc 2 s, c x * ρ t₀ ^ x * (x * T' (x * θ t₀)) * θ' :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  ring


section Partials

variable {s : ℕ} {c : ℕ → ℝ} {σ : ℝ} {T T' : ℝ → ℝ}

theorem hasDerivAt_trigFamily_left (hT : ∀ t, HasDerivAt T (T' t) t) {ρ : ℝ} (hρ : ρ ≠ 0)
    (θ : ℝ) : HasDerivAt (fun θ => trigFamily s c σ T θ ρ) (trigFamilyθ s c σ T' θ ρ) θ := by
  simpa using hasDerivAt_trigFamily (s := s) (c := c) (σ := σ) hT (hasDerivAt_id θ)
    (hasDerivAt_const θ ρ) hρ

theorem hasDerivAt_trigFamily_right (hT : ∀ t, HasDerivAt T (T' t) t) (θ : ℝ) {ρ : ℝ}
    (hρ : ρ ≠ 0) : HasDerivAt (fun ρ => trigFamily s c σ T θ ρ) (trigFamilyρ s c σ T θ ρ) ρ := by
  simpa using hasDerivAt_trigFamily (s := s) (c := c) (σ := σ) hT (hasDerivAt_const ρ θ)
    (hasDerivAt_id ρ) hρ

theorem continuousAt_trigFamilyθ (hT' : Continuous T') {θ₀ ρ₀ : ℝ} (hρ : ρ₀ ≠ 0) :
    ContinuousAt (Function.uncurry (trigFamilyθ s c σ T')) (θ₀, ρ₀) := by
  have hinv : ContinuousAt (fun p : ℝ × ℝ => p.2⁻¹) (θ₀, ρ₀) := continuousAt_snd.inv₀ hρ
  unfold trigFamilyθ Function.uncurry
  fun_prop

theorem continuousAt_trigFamilyρ (hT : Continuous T) {θ₀ ρ₀ : ℝ} (hρ : ρ₀ ≠ 0) :
    ContinuousAt (Function.uncurry (trigFamilyρ s c σ T)) (θ₀, ρ₀) := by
  have hinv : ContinuousAt (fun p : ℝ × ℝ => (p.2 ^ 2)⁻¹) (θ₀, ρ₀) :=
    (continuousAt_snd.pow 2).inv₀ (pow_ne_zero 2 hρ)
  unfold trigFamilyρ Function.uncurry
  fun_prop

end Partials

end TrigFamily

/-- One-variable implicit function theorem: a smooth family `F θ ρ` with `F_ρ ≠ 0` has a
differentiable branch `ψ` of solutions near the point. -/
theorem exists_differentiableAt_implicit {F Fθ Fρ : ℝ → ℝ → ℝ} {θ₀ ρ₀ : ℝ}
    (h1 : ∀ᶠ v in 𝓝 (θ₀, ρ₀), HasDerivAt (fun θ => F θ v.2) (Fθ v.1 v.2) v.1)
    (h2 : ∀ᶠ v in 𝓝 (θ₀, ρ₀), HasDerivAt (fun ρ => F v.1 ρ) (Fρ v.1 v.2) v.2)
    (c1 : ContinuousAt (Function.uncurry Fθ) (θ₀, ρ₀))
    (c2 : ContinuousAt (Function.uncurry Fρ) (θ₀, ρ₀)) (hne : Fρ θ₀ ρ₀ ≠ 0) :
    ∃ ψ : ℝ → ℝ, DifferentiableAt ℝ ψ θ₀ ∧ Tendsto ψ (𝓝 θ₀) (𝓝 ρ₀) ∧
      ∀ᶠ θ in 𝓝 θ₀, F θ (ψ θ) = F θ₀ ρ₀ := by
  let f₁ : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun θ ρ => (1 : ℝ →L[ℝ] ℝ).smulRight (Fθ θ ρ)
  let f₂ : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun θ ρ => (1 : ℝ →L[ℝ] ℝ).smulRight (Fρ θ ρ)
  have cf₁ : ContinuousAt (Function.uncurry f₁) (θ₀, ρ₀) :=
    ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.continuousAt).comp c1
  have cf₂ : ContinuousAt (Function.uncurry f₂) (θ₀, ρ₀) :=
    ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.continuousAt).comp c2
  have if₂ : (f₂ (θ₀, ρ₀).1 (θ₀, ρ₀).2).IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := (1 : ℝ →L[ℝ] ℝ).smulRight (Fρ θ₀ ρ₀)⁻¹) ?_ ?_ <;>
    · ext; simp [f₂, hne]
  have df₁ : ∀ᶠ v in 𝓝 (θ₀, ρ₀), HasFDerivAt (f := fun θ => F θ v.2) (f₁ v.1 v.2) v.1 :=
    h1.mono fun v hv => hv.hasFDerivAt
  have df₂ : ∀ᶠ v in 𝓝 (θ₀, ρ₀), HasFDerivAt (f := fun ρ => F v.1 ρ) (f₂ v.1 v.2) v.2 :=
    h2.mono fun v hv => hv.hasFDerivAt
  refine ⟨implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂, ?_, ?_, ?_⟩
  · exact (hasStrictFDerivAt_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂).differentiableAt
  · exact tendsto_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂
  · exact eventually_apply_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂


end RealRooted.ToeplitzPerturbation
