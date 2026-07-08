import RealRooted.RootSumBounds
import RealRooted.RootCountFinite
import RealRooted.RootCountLocalConstancy
import RealRooted.RootMultiplicityMatching

/-!
# Small-Positive-Parameter Root Count

This file assembles the issue #42 small-positive count route for
`f + C μ * g`.  The analytic input is the per-root local lower count; this file
combines it with finite matching, left escape, and escaped-root count lemmas.
-/

open Polynomial

namespace RealRooted

/--
Per-root local lower counts imply the matching hypothesis used by the
small-positive count theorem.

This is the finite bridge needed to consume the analytic lower-count theorem:
after choosing disjoint balls around the distinct roots of `f`, the local
counts assemble into one global proximity matching.
-/
private theorem matching_hypothesis_of_eventual_local_lower_counts
    {f g : ℝ[X]}
    (hlocal : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ,
        0 < μ → μ < δ →
        (f + C μ * g).Splits ∧
          ∀ a ∈ f.roots.toFinset,
            f.roots.count a ≤
              ((f + C μ * g).roots.filter (fun q => |q - a| < ρ)).card) :
    ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ →
        μ < δ →
        (f + C μ * g).Splits ∧
          ∃ u : Multiset ℝ, u ≤ (f + C μ * g).roots ∧
            Multiset.Rel (fun r q => |q - r| < ρ) f.roots u := by
  intro ρ hρ
  obtain ⟨ε, hε_pos, hερ, hsep⟩ :=
    Multiset.exists_pos_lt_and_two_mul_le_abs_sub_toFinset f.roots hρ
  obtain ⟨δ, hδ_pos, hδ⟩ := hlocal ε hε_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro μ hμ hμδ
  obtain ⟨hp_split, hcount⟩ := hδ μ hμ hμδ
  obtain ⟨u, hu, hRel⟩ :=
    Multiset.exists_rel_le_of_forall_le_count (s := f.roots)
      (t := (f + C μ * g).roots) hsep hcount
  refine ⟨hp_split, u, hu, ?_⟩
  refine hRel.mono ?_
  intro _ _ _ _ hclose
  exact lt_trans hclose hερ

private theorem local_lower_counts_of_eventual_root_clusters
    {f g : ℝ[X]}
    (hclusters : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ,
        0 < μ → μ < δ →
        (f + C μ * g).Splits ∧
          ∀ a ∈ f.roots.toFinset, ∃ s : Multiset ℝ,
            s ≤ (f + C μ * g).roots ∧ s.card = f.roots.count a ∧
              ∀ q ∈ s, |q - a| < ρ) :
    ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ,
      0 < μ → μ < δ →
      (f + C μ * g).Splits ∧
        ∀ a ∈ f.roots.toFinset,
          f.roots.count a ≤
            ((f + C μ * g).roots.filter (fun q => |q - a| < ρ)).card := by
  intro ρ hρ
  obtain ⟨δ, hδ_pos, hδ⟩ := hclusters ρ hρ
  refine ⟨δ, hδ_pos, ?_⟩
  intro μ hμ hμδ
  obtain ⟨hp_split, hcluster⟩ := hδ μ hμ hμδ
  refine ⟨hp_split, ?_⟩
  intro a ha
  obtain ⟨s, hs_le, hs_card, hs_near⟩ := hcluster a ha
  rw [← hs_card]
  exact Polynomial.card_le_card_roots_filter_of_le_roots hs_le hs_near

private theorem closedSegment_roots_eq_add_right_of_lt_one
    {f g : ℝ[X]} {β : ℝ} (hβ : β < 1) :
    (C (1 - β) * f + C β * g).roots =
      (f + C (β / (1 - β)) * g).roots := by
  have hden : 1 - β ≠ 0 := by linarith
  have hmul : (1 - β) * (β / (1 - β)) = β := by
    field_simp [hden]
  have hpoly :
      C (1 - β) * f + C β * g =
        C (1 - β) * (f + C (β / (1 - β)) * g) := by
    rw [mul_add, ← mul_assoc, ← C_mul, hmul]
  rw [hpoly, Polynomial.roots_C_mul _ hden]

private theorem div_add_one_mem_Icc_of_nonneg {μ : ℝ} (hμ : 0 ≤ μ) :
    μ / (μ + 1) ∈ Set.Icc (0 : ℝ) 1 := by
  have hden_pos : 0 < μ + 1 := by linarith
  exact ⟨div_nonneg hμ hden_pos.le, by
    rw [div_le_one hden_pos]
    linarith⟩

private theorem one_div_add_one_mem_Icc_of_nonneg {ν : ℝ} (hν : 0 ≤ ν) :
    1 / (ν + 1) ∈ Set.Icc (0 : ℝ) 1 := by
  have hden_pos : 0 < ν + 1 := by linarith
  exact ⟨div_nonneg zero_le_one hden_pos.le, by
    rw [div_le_one hden_pos]
    linarith⟩

private theorem add_right_eq_C_mul_closedSegment_of_nonneg
    {f g : ℝ[X]} {μ : ℝ} (hμ : 0 ≤ μ) :
    f + C μ * g =
      C (μ + 1) *
        (C (1 - μ / (μ + 1)) * f + C (μ / (μ + 1)) * g) := by
  have hden : μ + 1 ≠ 0 := by linarith
  have hleft : (μ + 1) * (1 - μ / (μ + 1)) = 1 := by
    field_simp [hden]
    ring
  have hright : (μ + 1) * (μ / (μ + 1)) = μ := by
    field_simp [hden]
  rw [mul_add, ← mul_assoc, ← C_mul, ← mul_assoc, ← C_mul, hleft, hright]
  simp

private theorem add_left_eq_C_mul_closedSegment_of_nonneg
    {f g : ℝ[X]} {ν : ℝ} (hν : 0 ≤ ν) :
    g + C ν * f =
      C (ν + 1) *
        (C (1 - 1 / (ν + 1)) * f + C (1 / (ν + 1)) * g) := by
  have hden : ν + 1 ≠ 0 := by linarith
  have hleft : (ν + 1) * (1 - 1 / (ν + 1)) = ν := by
    field_simp [hden]
    ring
  have hright : (ν + 1) * (1 / (ν + 1)) = 1 := by
    field_simp [hden]
  rw [mul_add, ← mul_assoc, ← C_mul, ← mul_assoc, ← C_mul, hleft, hright]
  simp [add_comm]

private theorem add_right_splits_of_closedSegment_splits_of_nonneg
    {f g : ℝ[X]} {μ : ℝ} (hμ : 0 ≤ μ)
    (hseg : (C (1 - μ / (μ + 1)) * f + C (μ / (μ + 1)) * g).Splits) :
    (f + C μ * g).Splits := by
  rw [add_right_eq_C_mul_closedSegment_of_nonneg hμ]
  exact hseg.C_mul (μ + 1)

private theorem add_left_splits_of_closedSegment_splits_of_nonneg
    {f g : ℝ[X]} {ν : ℝ} (hν : 0 ≤ ν)
    (hseg : (C (1 - 1 / (ν + 1)) * f + C (1 / (ν + 1)) * g).Splits) :
    (g + C ν * f).Splits := by
  rw [add_left_eq_C_mul_closedSegment_of_nonneg hν]
  exact hseg.C_mul (ν + 1)

private theorem add_right_not_isRoot_of_closedSegment_not_isRoot_of_nonneg
    {f g : ℝ[X]} {μ x : ℝ} (hμ : 0 ≤ μ)
    (hseg : ¬ (C (1 - μ / (μ + 1)) * f + C (μ / (μ + 1)) * g).IsRoot x) :
    ¬ (f + C μ * g).IsRoot x := by
  have hden : μ + 1 ≠ 0 := by linarith
  intro hroot
  rw [add_right_eq_C_mul_closedSegment_of_nonneg hμ] at hroot
  exact hseg (by simpa [Polynomial.IsRoot.def, hden] using hroot)

private theorem add_left_not_isRoot_of_closedSegment_not_isRoot_of_nonneg
    {f g : ℝ[X]} {ν x : ℝ} (hν : 0 ≤ ν)
    (hseg : ¬ (C (1 - 1 / (ν + 1)) * f + C (1 / (ν + 1)) * g).IsRoot x) :
    ¬ (g + C ν * f).IsRoot x := by
  have hden : ν + 1 ≠ 0 := by linarith
  intro hroot
  rw [add_left_eq_C_mul_closedSegment_of_nonneg hν] at hroot
  exact hseg (by simpa [Polynomial.IsRoot.def, hden] using hroot)

/--
Small-positive-parameter upper root-count equality for `f + C μ * g`.

The theorem isolates the remaining analytic #42 obligation as per-root lower
counts: every root `a` of `f`, counted with multiplicity, must eventually be
accounted for by roots of `f + C μ * g` in a small ball around `a`.  The finite
matching and escaped-root assembly are handled internally.
-/
theorem card_filter_gt_add_C_mul_eventually_eq
    {f g : ℝ[X]} {x : ℝ}
    (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree + 1) (hf_split : f.Splits)
    (hx : x ∉ f.roots)
    (hlocal : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ,
        0 < μ → μ < δ →
        (f + C μ * g).Splits ∧
          ∀ a ∈ f.roots.toFinset,
            f.roots.count a ≤
              ((f + C μ * g).roots.filter (fun q => |q - a| < ρ)).card) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ → μ < δ →
      ((f + C μ * g).roots.filter (x < ·)).card =
        (f.roots.filter (x < ·)).card := by
  obtain ⟨B, ε, hBx, hε_pos, hB, hsep_x, hsep_B⟩ :=
    Multiset.exists_guard_le_and_pos_le_abs_sub f.roots hx
  obtain ⟨δesc, hδesc_pos, hδesc⟩ :=
    exists_root_lt_of_succDegree_add_right_small hf_pos hg_pos hdeg B
  obtain ⟨δmatch, hδmatch_pos, hδmatch⟩ :=
    matching_hypothesis_of_eventual_local_lower_counts hlocal ε hε_pos
  refine ⟨min δesc δmatch, lt_min hδesc_pos hδmatch_pos, ?_⟩
  intro μ hμ hμδ
  obtain ⟨hp_split, u, hu, hRel⟩ :=
    hδmatch μ hμ (lt_of_lt_of_le hμδ (min_le_right _ _))
  obtain ⟨a, ha_mem, ha_lt⟩ :=
    hδesc μ hμ (lt_of_lt_of_le hμδ (min_le_left _ _)) hp_split
  have hlt : f.natDegree < g.natDegree := by
    rw [hdeg]
    exact Nat.lt_succ_self _
  have hnat : (f + C μ * g).natDegree = g.natDegree :=
    Polynomial.natDegree_add_C_mul_of_natDegree_lt (ne_of_gt hμ) hlt
  have hcard : (f + C μ * g).roots.card = f.roots.card + 1 := by
    rw [hp_split.natDegree_eq_card_roots.symm, hnat, hdeg,
      hf_split.natDegree_eq_card_roots.symm]
  exact Multiset.card_filter_gt_eq_of_rel_with_escaped_extra hsep_x hB hsep_B
    hRel hu ha_mem ha_lt hBx hcard

/--
Small-positive upper root-count equality from selected nearby root clusters.

This is the direct consumer for the active `RootClusterSubmultiset` route: once
the analytic input produces, near every root of `f`, a root submultiset of
`f + C μ * g` with the correct multiplicity, the existing small-positive
count theorem applies.
-/
theorem card_filter_gt_add_C_mul_eventually_eq_of_root_clusters
    {f g : ℝ[X]} {x : ℝ}
    (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree + 1) (hf_split : f.Splits)
    (hx : x ∉ f.roots)
    (hclusters : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ,
        0 < μ → μ < δ →
        (f + C μ * g).Splits ∧
          ∀ a ∈ f.roots.toFinset, ∃ s : Multiset ℝ,
            s ≤ (f + C μ * g).roots ∧ s.card = f.roots.count a ∧
              ∀ q ∈ s, |q - a| < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ → μ < δ →
      ((f + C μ * g).roots.filter (x < ·)).card =
        (f.roots.filter (x < ·)).card :=
  card_filter_gt_add_C_mul_eventually_eq hf_pos hg_pos hdeg hf_split hx
    (local_lower_counts_of_eventual_root_clusters hclusters)

/--
Small-positive closed-segment upper root-count equality.

This transfers `card_filter_gt_add_C_mul_eventually_eq` to the issue #42
closed segment by the change of variables `μ = β / (1 - β)`.
-/
theorem card_filter_gt_closedSegment_eventually_eq
    {f g : ℝ[X]} {x : ℝ}
    (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree + 1) (hf_split : f.Splits)
    (hx : x ∉ f.roots)
    (hlocal : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ,
        0 < μ → μ < δ →
        (f + C μ * g).Splits ∧
          ∀ a ∈ f.roots.toFinset,
            f.roots.count a ≤
              ((f + C μ * g).roots.filter (fun q => |q - a| < ρ)).card) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ β : ℝ, 0 < β → β < δ →
      ((C (1 - β) * f + C β * g).roots.filter (x < ·)).card =
        (f.roots.filter (x < ·)).card := by
  obtain ⟨δμ, hδμ_pos, hδμ⟩ :=
    card_filter_gt_add_C_mul_eventually_eq hf_pos hg_pos hdeg hf_split hx hlocal
  refine ⟨min (1 / 2) (δμ / 2), lt_min (by norm_num) (by positivity), ?_⟩
  intro β hβ_pos hβδ
  have hβ_lt_one : β < 1 := by
    linarith [lt_of_lt_of_le hβδ (min_le_left _ _)]
  have hden_pos : 0 < 1 - β := by linarith
  have hμ_pos : 0 < β / (1 - β) := div_pos hβ_pos hden_pos
  have hμ_lt : β / (1 - β) < δμ := by
    rw [div_lt_iff₀ hden_pos]
    nlinarith [lt_of_lt_of_le hβδ (min_le_left _ _),
      lt_of_lt_of_le hβδ (min_le_right _ _)]
  rw [closedSegment_roots_eq_add_right_of_lt_one hβ_lt_one]
  exact hδμ (β / (1 - β)) hμ_pos hμ_lt

/--
Endpoint upper root-count equality from the two analytic #42 inputs.

The hypotheses are intentionally the concrete remaining obligations: local
lower counts near the roots of `f`, and one-step local upper-count bounds on
the positive `f + μg` family and on the reciprocal `g + νf` family.
-/
theorem card_filter_gt_endpoint_eq_of_local_lower_counts_and_bounds
    {f g : ℝ[X]} {x : ℝ}
    (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree + 1) (hf_split : f.Splits)
    (hx : x ∉ f.roots)
    (hlocal_lower : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ,
        0 < μ → μ < δ →
        (f + C μ * g).Splits ∧
          ∀ a ∈ f.roots.toFinset,
            f.roots.count a ≤
              ((f + C μ * g).roots.filter (fun q => |q - a| < ρ)).card)
    (hfg_split : ∀ μ : ℝ, 0 < μ → μ ≤ 1 → (f + C μ * g).Splits)
    (hfg_no : ∀ μ : ℝ, 0 < μ → μ ≤ 1 → ¬ (f + C μ * g).IsRoot x)
    (hfg_bound : ∀ μ₀ : ℝ, 0 < μ₀ → μ₀ ≤ 1 →
      ∀ μ ∈ Set.Icc μ₀ 1, ∃ ε > 0, ∀ ν ∈ Set.Icc μ₀ 1,
        |ν - μ| < ε →
          ((f + C ν * g).roots.filter (x < ·)).card ≤
            ((f + C μ * g).roots.filter (x < ·)).card + 1 ∧
          ((f + C μ * g).roots.filter (x < ·)).card ≤
            ((f + C ν * g).roots.filter (x < ·)).card + 1)
    (hgf_split : ∀ ν ∈ Set.Icc (0 : ℝ) 1, (g + C ν * f).Splits)
    (hgf_no : ∀ ν ∈ Set.Icc (0 : ℝ) 1, ¬ (g + C ν * f).IsRoot x)
    (hgf_bound : ∀ μ ∈ Set.Icc (0 : ℝ) 1, ∃ ε > 0,
      ∀ ν ∈ Set.Icc (0 : ℝ) 1, |ν - μ| < ε →
        ((g + C ν * f).roots.filter (x < ·)).card ≤
          ((g + C μ * f).roots.filter (x < ·)).card + 1 ∧
        ((g + C μ * f).roots.filter (x < ·)).card ≤
          ((g + C ν * f).roots.filter (x < ·)).card + 1) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card := by
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    card_filter_gt_add_C_mul_eventually_eq hf_pos hg_pos hdeg hf_split hx
      hlocal_lower
  let μ₀ : ℝ := min (δ / 2) (1 / 2)
  have hμ₀_pos : 0 < μ₀ := lt_min (by positivity) (by norm_num)
  have hμ₀_le_one : μ₀ ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hμ₀_ltδ : μ₀ < δ := by
    have hle : μ₀ ≤ δ / 2 := min_le_left _ _
    linarith
  have hsmall := hδ μ₀ hμ₀_pos hμ₀_ltδ
  have hlt : f.natDegree < g.natDegree := by
    rw [hdeg]
    exact Nat.lt_succ_self _
  have hdeg_fg : ∀ μ ∈ Set.Icc μ₀ 1,
      (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree := by
    intro μ hμ
    have hμ_pos : 0 < μ := lt_of_lt_of_le hμ₀_pos hμ.1
    rw [Polynomial.natDegree_add_C_mul_of_natDegree_lt (ne_of_gt hμ_pos) hlt,
      Polynomial.natDegree_add_C_mul_of_natDegree_lt (ne_of_gt hμ₀_pos) hlt]
  have hfg_eq :=
    rightFamily_card_roots_gt_eq_of_local_count_bound (f := f) (g := g)
      (μ₀ := μ₀) (μ₁ := 1) (x := x) hμ₀_le_one hdeg_fg
      (fun μ hμ => hfg_split μ (lt_of_lt_of_le hμ₀_pos hμ.1) hμ.2)
      (fun μ hμ => hfg_no μ (lt_of_lt_of_le hμ₀_pos hμ.1) hμ.2)
      (hfg_bound μ₀ hμ₀_pos hμ₀_le_one)
  have hdeg_gf : ∀ ν ∈ Set.Icc (0 : ℝ) 1,
      (g + C ν * f).natDegree = (g + C (0 : ℝ) * f).natDegree := by
    intro ν _
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt
      ((Polynomial.natDegree_C_mul_le ν f).trans_lt hlt)]
    simp
  have hgf_eq :=
    rightFamily_card_roots_gt_eq_of_local_count_bound (f := g) (g := f)
      (μ₀ := 0) (μ₁ := 1) (x := x) (by norm_num) hdeg_gf
      hgf_split hgf_no hgf_bound
  calc
    (f.roots.filter (x < ·)).card =
        ((f + C μ₀ * g).roots.filter (x < ·)).card := hsmall.symm
    _ = ((f + C (1 : ℝ) * g).roots.filter (x < ·)).card := hfg_eq
    _ = ((g + C (1 : ℝ) * f).roots.filter (x < ·)).card := by
      rw [show f + C (1 : ℝ) * g = g + C (1 : ℝ) * f by simp [add_comm]]
    _ = (g.roots.filter (x < ·)).card := by
      simpa using hgf_eq.symm

/--
Endpoint upper root-count equality from local lower counts on the positive
parameter families.

Compared with `card_filter_gt_endpoint_eq_of_local_lower_counts_and_bounds`,
this consumes the concrete multiplicity-preserving local lower-count primitive
on `f + C μ * g` and `g + C ν * f`, rather than a separate two-sided
`≤ + 1` local count-bound hypothesis.
-/
theorem card_filter_gt_endpoint_eq_of_local_lower_counts
    {f g : ℝ[X]} {x : ℝ}
    (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree + 1) (hf_split : f.Splits)
    (hx : x ∉ f.roots)
    (hlocal_lower : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ,
        0 < μ → μ < δ →
        (f + C μ * g).Splits ∧
          ∀ a ∈ f.roots.toFinset,
            f.roots.count a ≤
              ((f + C μ * g).roots.filter (fun q => |q - a| < ρ)).card)
    (hfg_split : ∀ μ : ℝ, 0 < μ → μ ≤ 1 → (f + C μ * g).Splits)
    (hfg_no : ∀ μ : ℝ, 0 < μ → μ ≤ 1 → ¬ (f + C μ * g).IsRoot x)
    (hfg_lower : ∀ μ₀ : ℝ, 0 < μ₀ → μ₀ ≤ 1 →
      ∀ μ ∈ Set.Icc μ₀ 1, ∀ ρ : ℝ, 0 < ρ → ∃ ε : ℝ, 0 < ε ∧
        ∀ ν ∈ Set.Icc μ₀ 1, |ν - μ| < ε →
          ∀ a ∈ (f + C μ * g).roots.toFinset,
            (f + C μ * g).roots.count a ≤
              ((f + C ν * g).roots.filter (fun q => |q - a| < ρ)).card)
    (hgf_split : ∀ ν ∈ Set.Icc (0 : ℝ) 1, (g + C ν * f).Splits)
    (hgf_no : ∀ ν ∈ Set.Icc (0 : ℝ) 1, ¬ (g + C ν * f).IsRoot x)
    (hgf_lower : ∀ μ ∈ Set.Icc (0 : ℝ) 1, ∀ ρ : ℝ, 0 < ρ →
      ∃ ε : ℝ, 0 < ε ∧ ∀ ν ∈ Set.Icc (0 : ℝ) 1, |ν - μ| < ε →
        ∀ a ∈ (g + C μ * f).roots.toFinset,
          (g + C μ * f).roots.count a ≤
            ((g + C ν * f).roots.filter (fun q => |q - a| < ρ)).card) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card := by
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    card_filter_gt_add_C_mul_eventually_eq hf_pos hg_pos hdeg hf_split hx
      hlocal_lower
  let μ₀ : ℝ := min (δ / 2) (1 / 2)
  have hμ₀_pos : 0 < μ₀ := lt_min (by positivity) (by norm_num)
  have hμ₀_le_one : μ₀ ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hμ₀_ltδ : μ₀ < δ := by
    have hle : μ₀ ≤ δ / 2 := min_le_left _ _
    linarith
  have hsmall := hδ μ₀ hμ₀_pos hμ₀_ltδ
  have hlt : f.natDegree < g.natDegree := by
    rw [hdeg]
    exact Nat.lt_succ_self _
  have hdeg_fg : ∀ μ ∈ Set.Icc μ₀ 1,
      (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree := by
    intro μ hμ
    have hμ_pos : 0 < μ := lt_of_lt_of_le hμ₀_pos hμ.1
    rw [Polynomial.natDegree_add_C_mul_of_natDegree_lt (ne_of_gt hμ_pos) hlt,
      Polynomial.natDegree_add_C_mul_of_natDegree_lt (ne_of_gt hμ₀_pos) hlt]
  have hfg_eq :=
    rightFamily_card_roots_gt_eq_of_local_lower_counts (f := f) (g := g)
      (μ₀ := μ₀) (μ₁ := 1) (x := x) hμ₀_le_one hdeg_fg
      (fun μ hμ => hfg_split μ (lt_of_lt_of_le hμ₀_pos hμ.1) hμ.2)
      (fun μ hμ => hfg_no μ (lt_of_lt_of_le hμ₀_pos hμ.1) hμ.2)
      (hfg_lower μ₀ hμ₀_pos hμ₀_le_one)
  have hdeg_gf : ∀ ν ∈ Set.Icc (0 : ℝ) 1,
      (g + C ν * f).natDegree = (g + C (0 : ℝ) * f).natDegree := by
    intro ν _
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt
      ((Polynomial.natDegree_C_mul_le ν f).trans_lt hlt)]
    simp
  have hgf_eq :=
    rightFamily_card_roots_gt_eq_of_local_lower_counts (f := g) (g := f)
      (μ₀ := 0) (μ₁ := 1) (x := x) (by norm_num) hdeg_gf
      hgf_split hgf_no hgf_lower
  calc
    (f.roots.filter (x < ·)).card =
        ((f + C μ₀ * g).roots.filter (x < ·)).card := hsmall.symm
    _ = ((f + C (1 : ℝ) * g).roots.filter (x < ·)).card := hfg_eq
    _ = ((g + C (1 : ℝ) * f).roots.filter (x < ·)).card := by
      rw [show f + C (1 : ℝ) * g = g + C (1 : ℝ) * f by simp [add_comm]]
    _ = (g.roots.filter (x < ·)).card := by
      simpa using hgf_eq.symm

/--
Endpoint upper root-count equality from actual closed-segment split/no-crossing
inputs plus the two local count-bound inputs.

This is the next assembly step toward
`CompatibleSuccDegreeClosedSegmentCountEqStatement`: it replaces the
right-family and reciprocal-family split/no-root hypotheses in
`card_filter_gt_endpoint_eq_of_local_lower_counts_and_bounds` by the natural
closed-segment hypotheses.
-/
theorem card_filter_gt_endpoint_eq_of_closedSegment_inputs_and_bounds
    {f g : ℝ[X]} {x : ℝ}
    (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree + 1) (hf_split : f.Splits)
    (hx : x ∉ f.roots)
    (hlocal_lower : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ,
        0 < μ → μ < δ →
        (f + C μ * g).Splits ∧
          ∀ a ∈ f.roots.toFinset,
            f.roots.count a ≤
              ((f + C μ * g).roots.filter (fun q => |q - a| < ρ)).card)
    (hseg_split : ∀ β ∈ Set.Icc (0 : ℝ) 1,
      (C (1 - β) * f + C β * g).Splits)
    (hseg_no : ∀ β ∈ Set.Icc (0 : ℝ) 1,
      ¬ (C (1 - β) * f + C β * g).IsRoot x)
    (hfg_bound : ∀ μ₀ : ℝ, 0 < μ₀ → μ₀ ≤ 1 →
      ∀ μ ∈ Set.Icc μ₀ 1, ∃ ε > 0, ∀ ν ∈ Set.Icc μ₀ 1,
        |ν - μ| < ε →
          ((f + C ν * g).roots.filter (x < ·)).card ≤
            ((f + C μ * g).roots.filter (x < ·)).card + 1 ∧
          ((f + C μ * g).roots.filter (x < ·)).card ≤
            ((f + C ν * g).roots.filter (x < ·)).card + 1)
    (hgf_bound : ∀ μ ∈ Set.Icc (0 : ℝ) 1, ∃ ε > 0,
      ∀ ν ∈ Set.Icc (0 : ℝ) 1, |ν - μ| < ε →
        ((g + C ν * f).roots.filter (x < ·)).card ≤
          ((g + C μ * f).roots.filter (x < ·)).card + 1 ∧
        ((g + C μ * f).roots.filter (x < ·)).card ≤
          ((g + C ν * f).roots.filter (x < ·)).card + 1) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card := by
  refine card_filter_gt_endpoint_eq_of_local_lower_counts_and_bounds
    hf_pos hg_pos hdeg hf_split hx hlocal_lower ?_ ?_ hfg_bound ?_ ?_
    hgf_bound
  · intro μ hμ _
    exact add_right_splits_of_closedSegment_splits_of_nonneg hμ.le
      (hseg_split _ (div_add_one_mem_Icc_of_nonneg hμ.le))
  · intro μ hμ _
    exact add_right_not_isRoot_of_closedSegment_not_isRoot_of_nonneg hμ.le
      (hseg_no _ (div_add_one_mem_Icc_of_nonneg hμ.le))
  · intro ν hν
    exact add_left_splits_of_closedSegment_splits_of_nonneg hν.1
      (hseg_split _ (one_div_add_one_mem_Icc_of_nonneg hν.1))
  · intro ν hν
    exact add_left_not_isRoot_of_closedSegment_not_isRoot_of_nonneg hν.1
      (hseg_no _ (one_div_add_one_mem_Icc_of_nonneg hν.1))

/--
Endpoint upper root-count equality from closed-segment split/no-crossing inputs
and local lower counts on the two positive parameter families.

This is the closed-segment version of
`card_filter_gt_endpoint_eq_of_local_lower_counts`: it replaces the auxiliary
family split/no-root hypotheses by the natural closed-segment hypotheses using
the scalar changes already proved above.
-/
theorem card_filter_gt_endpoint_eq_of_closedSegment_inputs_and_local_lower_counts
    {f g : ℝ[X]} {x : ℝ}
    (hf_pos : 0 < f.leadingCoeff) (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree + 1) (hf_split : f.Splits)
    (hx : x ∉ f.roots)
    (hlocal_lower : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ,
        0 < μ → μ < δ →
        (f + C μ * g).Splits ∧
          ∀ a ∈ f.roots.toFinset,
            f.roots.count a ≤
              ((f + C μ * g).roots.filter (fun q => |q - a| < ρ)).card)
    (hseg_split : ∀ β ∈ Set.Icc (0 : ℝ) 1,
      (C (1 - β) * f + C β * g).Splits)
    (hseg_no : ∀ β ∈ Set.Icc (0 : ℝ) 1,
      ¬ (C (1 - β) * f + C β * g).IsRoot x)
    (hfg_lower : ∀ μ₀ : ℝ, 0 < μ₀ → μ₀ ≤ 1 →
      ∀ μ ∈ Set.Icc μ₀ 1, ∀ ρ : ℝ, 0 < ρ → ∃ ε : ℝ, 0 < ε ∧
        ∀ ν ∈ Set.Icc μ₀ 1, |ν - μ| < ε →
          ∀ a ∈ (f + C μ * g).roots.toFinset,
            (f + C μ * g).roots.count a ≤
              ((f + C ν * g).roots.filter (fun q => |q - a| < ρ)).card)
    (hgf_lower : ∀ μ ∈ Set.Icc (0 : ℝ) 1, ∀ ρ : ℝ, 0 < ρ →
      ∃ ε : ℝ, 0 < ε ∧ ∀ ν ∈ Set.Icc (0 : ℝ) 1, |ν - μ| < ε →
        ∀ a ∈ (g + C μ * f).roots.toFinset,
          (g + C μ * f).roots.count a ≤
            ((g + C ν * f).roots.filter (fun q => |q - a| < ρ)).card) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card := by
  refine card_filter_gt_endpoint_eq_of_local_lower_counts
    hf_pos hg_pos hdeg hf_split hx hlocal_lower ?_ ?_ hfg_lower ?_ ?_
    hgf_lower
  · intro μ hμ _
    exact add_right_splits_of_closedSegment_splits_of_nonneg hμ.le
      (hseg_split _ (div_add_one_mem_Icc_of_nonneg hμ.le))
  · intro μ hμ _
    exact add_right_not_isRoot_of_closedSegment_not_isRoot_of_nonneg hμ.le
      (hseg_no _ (div_add_one_mem_Icc_of_nonneg hμ.le))
  · intro ν hν
    exact add_left_splits_of_closedSegment_splits_of_nonneg hν.1
      (hseg_split _ (one_div_add_one_mem_Icc_of_nonneg hν.1))
  · intro ν hν
    exact add_left_not_isRoot_of_closedSegment_not_isRoot_of_nonneg hν.1
      (hseg_no _ (one_div_add_one_mem_Icc_of_nonneg hν.1))

end RealRooted
