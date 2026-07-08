import RealRooted.Mathlib.Algebra.Polynomial.Splits
import RealRooted.RootMultiplicityMatching

/-!
# Local Constancy of Root Counts

This file contains the positive-parameter local-constancy support for the
issue #42 succ-degree route.  The main point is to reduce global equality of
upper root counts on a compact positive parameter interval to a local
root-continuity statement stated as per-root local lower counts.
-/

open Polynomial

noncomputable section

namespace RealRooted

/--
Choose one separation radius around the roots of `p` so that any same-degree
split polynomial with enough roots in each such ball has the same strict-upper
root count across a threshold `x`.

This is the polynomial bridge for the local-lower-count part of issue #42:
after an analytic continuity argument supplies the per-root lower counts near a
fixed positive parameter, the threshold count equality is finite bookkeeping.
-/
theorem exists_radius_card_roots_filter_gt_eq_of_sameDegree_local_lower_counts
    {p : ℝ[X]} {x : ℝ} (hx : x ∉ p.roots) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q : ℝ[X], p.Splits → q.Splits →
      q.natDegree = p.natDegree →
      (∀ a ∈ p.roots.toFinset,
        p.roots.count a ≤ (q.roots.filter (fun r => |r - a| < ρ)).card) →
      (q.roots.filter (x < ·)).card = (p.roots.filter (x < ·)).card := by
  obtain ⟨η, hη_pos, hη⟩ := Multiset.exists_pos_le_abs_sub_of_not_mem p.roots hx
  obtain ⟨ρ, hρ_pos, hρη, hsep_centers⟩ :=
    Multiset.exists_pos_lt_and_two_mul_le_abs_sub_toFinset p.roots hη_pos
  refine ⟨ρ, hρ_pos, fun q hp_split hq_split hdeg hcount => ?_⟩
  refine Multiset.card_filter_gt_eq_of_forall_le_count_and_card_eq
    hsep_centers ?_ hcount ?_
  · intro r hr
    exact le_trans (le_of_lt hρη) (hη r hr)
  · rw [hq_split.natDegree_eq_card_roots.symm,
      hp_split.natDegree_eq_card_roots.symm, hdeg]

/-- A natural-number-valued function that is locally constant along a closed
real interval takes equal values at the endpoints. -/
theorem eq_of_locally_constant_on_Icc {N : ℝ → ℕ} {a b : ℝ} (hab : a ≤ b)
    (hloc : ∀ t ∈ Set.Icc a b, ∃ ε > 0, ∀ u ∈ Set.Icc a b,
      |u - t| < ε → N u = N t) :
    N a = N b := by
  have hcont : ContinuousOn N (Set.Icc a b) := by
    intro t ht
    obtain ⟨ε, ε_pos, H⟩ := hloc t ht
    have hev : ∀ᶠ u in nhdsWithin t (Set.Icc a b), N u = N t := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t ε_pos)] with u hu h'u
      simpa [Real.dist_eq] using H u hu h'u
    exact tendsto_const_nhds.congr' (hev.mono fun u h => h.symm)
  exact IsPreconnected.constant isPreconnected_Icc hcont
    (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)

/--
Analytic per-root lower counts imply local constancy of the strict-upper root
count near a fixed positive parameter.

This is the #42 local-constancy consumer for a multiplicity-preserving
root-continuity theorem: once each root of `f + C μ * g` keeps at least its
multiplicity inside every sufficiently small ball for nearby parameters, the
finite radius bridge gives exact equality of the upper count near `μ`.
-/
theorem rightFamily_local_card_roots_gt_eq_of_local_lower_counts
    {f g : ℝ[X]} {μ₀ μ₁ μ x : ℝ}
    (hμ : μ ∈ Set.Icc μ₀ μ₁)
    (hdeg : ∀ ν ∈ Set.Icc μ₀ μ₁,
      (f + C ν * g).natDegree = (f + C μ * g).natDegree)
    (hrr : ∀ ν ∈ Set.Icc μ₀ μ₁, (f + C ν * g).Splits)
    (hne : ∀ ν ∈ Set.Icc μ₀ μ₁, ¬ (f + C ν * g).IsRoot x)
    (hlower : ∀ ρ > 0, ∃ ε > 0, ∀ ν ∈ Set.Icc μ₀ μ₁,
      |ν - μ| < ε →
        ∀ a ∈ (f + C μ * g).roots.toFinset,
          (f + C μ * g).roots.count a ≤
            ((f + C ν * g).roots.filter (fun r => |r - a| < ρ)).card) :
    ∃ ε > 0, ∀ ν ∈ Set.Icc μ₀ μ₁, |ν - μ| < ε →
      ((f + C ν * g).roots.filter (x < ·)).card =
        ((f + C μ * g).roots.filter (x < ·)).card := by
  have hx : x ∉ (f + C μ * g).roots :=
    fun hx => hne μ hμ (Polynomial.isRoot_of_mem_roots hx)
  obtain ⟨ρ, hρ_pos, hρ⟩ :=
    exists_radius_card_roots_filter_gt_eq_of_sameDegree_local_lower_counts hx
  obtain ⟨ε, hε_pos, hε⟩ := hlower ρ hρ_pos
  refine ⟨ε, hε_pos, fun ν hν hνμ => ?_⟩
  exact hρ (f + C ν * g) (hrr μ hμ) (hrr ν hν) (hdeg ν hν) (hε ν hν hνμ)

/--
Per-root lower counts along a root-free compact parameter interval imply
endpoint equality of strict-upper root counts.

This feeds the analytic local lower-count primitive directly into local
constancy of the root count.
-/
theorem rightFamily_card_roots_gt_eq_of_local_lower_counts
    {f g : ℝ[X]} {μ₀ μ₁ x : ℝ} (hμ₁ : μ₀ ≤ μ₁)
    (hdeg : ∀ μ ∈ Set.Icc μ₀ μ₁,
      (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree)
    (hrr : ∀ μ ∈ Set.Icc μ₀ μ₁, (f + C μ * g).Splits)
    (hne : ∀ μ ∈ Set.Icc μ₀ μ₁, ¬ (f + C μ * g).IsRoot x)
    (hlower : ∀ μ ∈ Set.Icc μ₀ μ₁, ∀ ρ > 0, ∃ ε > 0,
      ∀ ν ∈ Set.Icc μ₀ μ₁, |ν - μ| < ε →
        ∀ a ∈ (f + C μ * g).roots.toFinset,
          (f + C μ * g).roots.count a ≤
            ((f + C ν * g).roots.filter (fun r => |r - a| < ρ)).card) :
    ((f + C μ₀ * g).roots.filter (x < ·)).card =
      ((f + C μ₁ * g).roots.filter (x < ·)).card := by
  refine eq_of_locally_constant_on_Icc
    (N := fun μ => ((f + C μ * g).roots.filter (x < ·)).card) hμ₁ ?_
  intro μ hμ
  have hdegμ : ∀ ν ∈ Set.Icc μ₀ μ₁,
      (f + C ν * g).natDegree = (f + C μ * g).natDegree := fun ν hν => by
    rw [hdeg ν hν, hdeg μ hμ]
  exact rightFamily_local_card_roots_gt_eq_of_local_lower_counts
    (f := f) (g := g) (μ := μ) hμ hdegμ hrr hne (hlower μ hμ)

end RealRooted
