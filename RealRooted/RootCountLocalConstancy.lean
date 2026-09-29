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
private theorem exists_radius_card_roots_filter_gt_eq_of_sameDegree_local_lower_counts
    {p : ℝ[X]} {x : ℝ} (hx : x ∉ p.roots) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q : ℝ[X], p.Splits → q.Splits →
      q.natDegree = p.natDegree →
      (∀ a ∈ p.roots.toFinset,
        p.roots.count a ≤ (q.roots.filter (fun r => |r - a| < ρ)).card) →
      (q.roots.filter (x < ·)).card = (p.roots.filter (x < ·)).card := by
  obtain ⟨η, hη_pos, hη⟩ := Multiset.exists_pos_le_abs_sub_of_not_mem p.roots hx
  obtain ⟨ρ, hρ_pos, hρη, hsep_centers⟩ :=
    Multiset.exists_pos_lt_and_two_mul_le_abs_sub_toFinset p.roots hη_pos
  refine ⟨ρ, hρ_pos, fun q hp_split hq_split hdeg hcount ↦ ?_⟩
  refine Multiset.card_filter_gt_eq_of_forall_le_count_and_card_eq
    hsep_centers ?_ hcount ?_
  · grind
  · simpa [hq_split.natDegree_eq_card_roots.symm,
      hp_split.natDegree_eq_card_roots.symm] using hdeg

/-- A natural-number-valued function that is locally constant along a closed
real interval takes equal values at the endpoints. -/
private theorem eq_of_locally_constant_on_Icc {N : ℝ → ℕ} {a b : ℝ} (hab : a ≤ b)
    (hloc : ∀ t ∈ Set.Icc a b, ∃ ε > 0, ∀ u ∈ Set.Icc a b,
      |u - t| < ε → N u = N t) :
    N a = N b := by
  have hcont : ContinuousOn N (Set.Icc a b) := fun t ht => by
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
count for an arbitrary real-parameter polynomial family.

It separates the finite multiplicity bookkeeping from the special affine
presentation `f + C μ * g`.
-/
private theorem polynomialFamily_local_card_roots_gt_eq_of_local_lower_counts
    {p : ℝ → ℝ[X]} {μ₀ μ₁ μ x : ℝ}
    (hμ : μ ∈ Set.Icc μ₀ μ₁)
    (hdeg : ∀ ν ∈ Set.Icc μ₀ μ₁, (p ν).natDegree = (p μ).natDegree)
    (hrr : ∀ ν ∈ Set.Icc μ₀ μ₁, (p ν).Splits)
    (hne : ∀ ν ∈ Set.Icc μ₀ μ₁, ¬ (p ν).IsRoot x)
    (hlower : ∀ ρ > 0, ∃ ε > 0, ∀ ν ∈ Set.Icc μ₀ μ₁,
      |ν - μ| < ε →
        ∀ a ∈ (p μ).roots.toFinset,
          (p μ).roots.count a ≤
            ((p ν).roots.filter (fun r => |r - a| < ρ)).card) :
    ∃ ε > 0, ∀ ν ∈ Set.Icc μ₀ μ₁, |ν - μ| < ε →
      ((p ν).roots.filter (x < ·)).card =
        ((p μ).roots.filter (x < ·)).card := by
  have hx : x ∉ (p μ).roots :=
    fun hx ↦ hne μ hμ (Polynomial.isRoot_of_mem_roots hx)
  obtain ⟨ρ, hρ_pos, hρ⟩ :=
    exists_radius_card_roots_filter_gt_eq_of_sameDegree_local_lower_counts hx
  grind

/--
Per-root lower counts along a root-free compact interval imply endpoint
equality of strict-upper root counts for an arbitrary polynomial family.

No coefficient-continuity hypothesis appears here: the analytic content is
isolated in `hlower`.  This is the general finite consumer needed by nonlinear
families such as a quadratic pencil.
-/
theorem polynomialFamily_card_roots_gt_eq_of_local_lower_counts
    {p : ℝ → ℝ[X]} {μ₀ μ₁ x : ℝ} (hμ₁ : μ₀ ≤ μ₁)
    (hdeg : ∀ μ ∈ Set.Icc μ₀ μ₁, (p μ).natDegree = (p μ₀).natDegree)
    (hrr : ∀ μ ∈ Set.Icc μ₀ μ₁, (p μ).Splits)
    (hne : ∀ μ ∈ Set.Icc μ₀ μ₁, ¬ (p μ).IsRoot x)
    (hlower : ∀ μ ∈ Set.Icc μ₀ μ₁, ∀ ρ > 0, ∃ ε > 0,
      ∀ ν ∈ Set.Icc μ₀ μ₁, |ν - μ| < ε →
        ∀ a ∈ (p μ).roots.toFinset,
          (p μ).roots.count a ≤
            ((p ν).roots.filter (fun r => |r - a| < ρ)).card) :
    ((p μ₀).roots.filter (x < ·)).card =
      ((p μ₁).roots.filter (x < ·)).card := by
  refine eq_of_locally_constant_on_Icc
    (N := fun μ ↦ ((p μ).roots.filter (x < ·)).card) hμ₁ ?_
  exact fun μ hμ ↦ polynomialFamily_local_card_roots_gt_eq_of_local_lower_counts
    (p := p) (μ := μ) hμ (fun ν hν ↦ by simp_all) hrr hne (hlower μ hμ)

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
  exact polynomialFamily_card_roots_gt_eq_of_local_lower_counts
    (p := fun μ ↦ f + C μ * g) hμ₁ hdeg hrr hne hlower

end RealRooted
