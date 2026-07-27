import RealRooted.RootCountLocalConstancy
import RealRooted.SameDegreeMultiplicityLowerCount

/-!
# Positive-parameter per-root local lower counts

This file discharges the *positive-parameter* per-root local lower-count input
for the issue #42 succ-degree route.

On a compact parameter interval `Set.Icc μ₀ μ₁` on which every member
`f + C μ * g` splits and has a constant `natDegree`, the degree does not jump,
so the same-degree multiplicity-aware continuity result
`RealRooted.exists_eps_forall_root_count_le_card_filter_near` applies at *every*
base parameter of the interval (not just at the `μ = 0` endpoint).  This is what
makes the positive-parameter route work: on the positive interval the degree is
constant, unlike across the `μ = 0` endpoint handled separately by
`RealRooted.DegreeIncreasingLocalLowerCount`.

The local-constancy consumer lives in `RealRooted.RootCountLocalConstancy` as
`RealRooted.rightFamily_card_roots_gt_eq_of_local_lower_counts`.  This file also
provides a direct positive-parameter count-equality wrapper for intervals
starting at `0`.
-/

open Polynomial Set

noncomputable section

namespace RealRooted

/-- **Positive-parameter per-root local lower counts.**

On a compact parameter interval `Set.Icc μ₀ μ₁` on which every member
`f + C μ * g` splits and has a constant `natDegree`, for every base parameter
`μ` in the interval and every `ρ > 0` there is `ε > 0` such that for all interval
parameters `ν` with `|ν - μ| < ε`, every root `a` of `f + C μ * g`, counted with
multiplicity, has at least that many roots of `f + C ν * g` inside `|q - a| < ρ`.

The degree hypothesis pins every member to the common `natDegree` of the base
`μ₀`, so the same-degree analytic core
`exists_eps_forall_root_count_le_card_filter_near` applies at each `μ` in the
interval. -/
theorem positiveParameter_local_lower_count
    {f g : ℝ[X]} {μ₀ μ₁ : ℝ}
    (hsplit : ∀ μ ∈ Set.Icc μ₀ μ₁, (f + C μ * g).Splits)
    (hdeg : ∀ μ ∈ Set.Icc μ₀ μ₁,
      (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree)
    {μ : ℝ} (hμ : μ ∈ Set.Icc μ₀ μ₁) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν ∈ Set.Icc μ₀ μ₁, |ν - μ| < ε →
      ∀ a ∈ (f + C μ * g).roots.toFinset,
        (f + C μ * g).roots.count a ≤
          ((f + C ν * g).roots.filter (fun q ↦ |q - a| < ρ)).card := by
  obtain ⟨ε, hε, hεspec⟩ :=
    exists_eps_forall_root_count_le_card_filter_near (μ0 := μ) (hsplit μ hμ) ρ hρ
  grind

/-- On a positive right-family interval starting at `0`, constant degree,
splitting, and no root at a fixed threshold force the strict-upper root count to
agree with the `μ = 0` endpoint. -/
theorem rightFamily_card_roots_gt_eq_zero_param_of_constant_degree
    {f g : ℝ[X]} {x μ : ℝ} (hμ_pos : 0 < μ)
    (hdeg : ∀ η ∈ Set.Icc (0 : ℝ) μ,
      (f + C η * g).natDegree = (f + C (0 : ℝ) * g).natDegree)
    (hsplit : ∀ η ∈ Set.Icc (0 : ℝ) μ, (f + C η * g).Splits)
    (hne : ∀ η ∈ Set.Icc (0 : ℝ) μ, ¬ (f + C η * g).IsRoot x) :
    ((f + C μ * g).roots.filter (x < ·)).card =
      (f.roots.filter (x < ·)).card := by
  have hcount := rightFamily_card_roots_gt_eq_of_local_lower_counts
    (f := f) (g := g) (μ₀ := 0) (μ₁ := μ) (x := x)
    (le_of_lt hμ_pos) hdeg hsplit hne
    (fun η hη ρ hρ => positiveParameter_local_lower_count hsplit hdeg hη hρ)
  simpa using hcount.symm

end RealRooted

end
