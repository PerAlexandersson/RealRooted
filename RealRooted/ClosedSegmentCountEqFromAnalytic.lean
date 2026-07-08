import RealRooted.CommonInterleaverTwo
import RealRooted.SmallPositiveParameterCount

/-!
# Closed-Segment Count Equality from Analytic Inputs

This file packages the issue #42 analytic route into the central
closed-segment count-equality target.  The remaining analytic hypotheses are
kept explicit: small-positive per-root lower counts and local upper-count
bounds for the two auxiliary right families.
-/

open Polynomial

namespace RealRooted

private theorem closedSegment_splits_of_compatible
    {f g : ℝ[X]} (hcomp : Compatible f g) :
    ∀ β ∈ Set.Icc (0 : ℝ) 1,
      (C (1 - β) * f + C β * g).Splits := by
  intro β hβ
  rcases hcomp (1 - β) β (by linarith [hβ.2]) hβ.1 with hzero | hrr
  · rw [hzero]
    simp
  · simpa using hrr.2

/--
The central closed-segment count-equality target follows from the analytic
inputs isolated in `SmallPositiveParameterCount`.

This is not a downstream challenge wrapper: it is the theorem-level assembly
from the actual closed-segment hypotheses to
`CompatibleSuccDegreeClosedSegmentCountEqStatement`, with the remaining
root-continuity/local-bound obligations exposed as hypotheses.
-/
theorem compatibleSuccDegreeClosedSegmentCountEq_of_local_lower_counts_and_bounds
    (hlocal : ∀ ⦃f g : ℝ[X]⦄ {x : ℝ},
      Compatible f g → HasPosLeadingCoeff f → HasPosLeadingCoeff g →
      g.natDegree = f.natDegree + 1 → f.Splits →
      ¬ f.IsRoot x → ¬ g.IsRoot x →
      (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x) →
      ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ,
        0 < μ → μ < δ →
        (f + C μ * g).Splits ∧
          ∀ a ∈ f.roots.toFinset,
            f.roots.count a ≤
              ((f + C μ * g).roots.filter (fun q => |q - a| < ρ)).card)
    (hfg_bound : ∀ ⦃f g : ℝ[X]⦄ {x : ℝ},
      Compatible f g → HasPosLeadingCoeff f → HasPosLeadingCoeff g →
      g.natDegree = f.natDegree + 1 → f.Splits →
      ¬ f.IsRoot x → ¬ g.IsRoot x →
      (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x) →
      ∀ μ₀ : ℝ, 0 < μ₀ → μ₀ ≤ 1 →
        ∀ μ ∈ Set.Icc μ₀ 1, ∃ ε > 0, ∀ ν ∈ Set.Icc μ₀ 1,
          |ν - μ| < ε →
            ((f + C ν * g).roots.filter (x < ·)).card ≤
              ((f + C μ * g).roots.filter (x < ·)).card + 1 ∧
            ((f + C μ * g).roots.filter (x < ·)).card ≤
              ((f + C ν * g).roots.filter (x < ·)).card + 1)
    (hgf_bound : ∀ ⦃f g : ℝ[X]⦄ {x : ℝ},
      Compatible f g → HasPosLeadingCoeff f → HasPosLeadingCoeff g →
      g.natDegree = f.natDegree + 1 → f.Splits →
      ¬ f.IsRoot x → ¬ g.IsRoot x →
      (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x) →
      ∀ μ ∈ Set.Icc (0 : ℝ) 1, ∃ ε > 0,
        ∀ ν ∈ Set.Icc (0 : ℝ) 1, |ν - μ| < ε →
          ((g + C ν * f).roots.filter (x < ·)).card ≤
            ((g + C μ * f).roots.filter (x < ·)).card + 1 ∧
          ((g + C μ * f).roots.filter (x < ·)).card ≤
            ((g + C ν * f).roots.filter (x < ·)).card + 1) :
    CompatibleSuccDegreeClosedSegmentCountEqStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  have hx_roots : x ∉ f.roots :=
    fun hx_mem => hxf ((Polynomial.mem_roots hf_pos.ne_zero).mp hx_mem)
  exact card_filter_gt_endpoint_eq_of_closedSegment_inputs_and_bounds
    hf_pos hg_pos hdeg hf_split hx_roots
    (hlocal hcomp hf_pos hg_pos hdeg hf_split hxf hxg hseg)
    (closedSegment_splits_of_compatible hcomp)
    (fun β hβ => hseg (β := β) hβ.1 hβ.2)
    (hfg_bound hcomp hf_pos hg_pos hdeg hf_split hxf hxg hseg)
    (hgf_bound hcomp hf_pos hg_pos hdeg hf_split hxf hxg hseg)

/--
The central closed-segment count-equality target follows from the concrete
local lower-count inputs on the two positive parameter families.

This is the same assembly as
`compatibleSuccDegreeClosedSegmentCountEq_of_local_lower_counts_and_bounds`,
but with the positive-parameter local-constancy hypotheses stated as
per-root lower counts, matching the current analytic obstruction.
-/
theorem compatibleSuccDegreeClosedSegmentCountEq_of_local_lower_counts
    (hlocal : ∀ ⦃f g : ℝ[X]⦄ {x : ℝ},
      Compatible f g → HasPosLeadingCoeff f → HasPosLeadingCoeff g →
      g.natDegree = f.natDegree + 1 → f.Splits →
      ¬ f.IsRoot x → ¬ g.IsRoot x →
      (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x) →
      ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ,
        0 < μ → μ < δ →
        (f + C μ * g).Splits ∧
          ∀ a ∈ f.roots.toFinset,
            f.roots.count a ≤
              ((f + C μ * g).roots.filter (fun q => |q - a| < ρ)).card)
    (hfg_lower : ∀ ⦃f g : ℝ[X]⦄ {x : ℝ},
      Compatible f g → HasPosLeadingCoeff f → HasPosLeadingCoeff g →
      g.natDegree = f.natDegree + 1 → f.Splits →
      ¬ f.IsRoot x → ¬ g.IsRoot x →
      (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x) →
      ∀ μ₀ : ℝ, 0 < μ₀ → μ₀ ≤ 1 →
        ∀ μ ∈ Set.Icc μ₀ 1, ∀ ρ : ℝ, 0 < ρ →
          ∃ ε : ℝ, 0 < ε ∧ ∀ ν ∈ Set.Icc μ₀ 1, |ν - μ| < ε →
            ∀ a ∈ (f + C μ * g).roots.toFinset,
              (f + C μ * g).roots.count a ≤
                ((f + C ν * g).roots.filter (fun q => |q - a| < ρ)).card)
    (hgf_lower : ∀ ⦃f g : ℝ[X]⦄ {x : ℝ},
      Compatible f g → HasPosLeadingCoeff f → HasPosLeadingCoeff g →
      g.natDegree = f.natDegree + 1 → f.Splits →
      ¬ f.IsRoot x → ¬ g.IsRoot x →
      (∀ {β : ℝ}, 0 ≤ β → β ≤ 1 →
        ¬ (C (1 - β) * f + C β * g).IsRoot x) →
      ∀ μ ∈ Set.Icc (0 : ℝ) 1, ∀ ρ : ℝ, 0 < ρ →
        ∃ ε : ℝ, 0 < ε ∧ ∀ ν ∈ Set.Icc (0 : ℝ) 1, |ν - μ| < ε →
          ∀ a ∈ (g + C μ * f).roots.toFinset,
            (g + C μ * f).roots.count a ≤
              ((g + C ν * f).roots.filter (fun q => |q - a| < ρ)).card) :
    CompatibleSuccDegreeClosedSegmentCountEqStatement := by
  intro f g hcomp hf_pos hg_pos hdeg hf_split x hxf hxg hseg
  have hx_roots : x ∉ f.roots :=
    fun hx_mem => hxf ((Polynomial.mem_roots hf_pos.ne_zero).mp hx_mem)
  exact card_filter_gt_endpoint_eq_of_closedSegment_inputs_and_local_lower_counts
    hf_pos hg_pos hdeg hf_split hx_roots
    (hlocal hcomp hf_pos hg_pos hdeg hf_split hxf hxg hseg)
    (closedSegment_splits_of_compatible hcomp)
    (fun β hβ => hseg (β := β) hβ.1 hβ.2)
    (hfg_lower hcomp hf_pos hg_pos hdeg hf_split hxf hxg hseg)
    (hgf_lower hcomp hf_pos hg_pos hdeg hf_split hxf hxg hseg)

end RealRooted
