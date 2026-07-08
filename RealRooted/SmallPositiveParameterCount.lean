import RealRooted.RootSumBounds
import RealRooted.RootCountLocalConstancy
import RealRooted.PositiveParameterLocalLowerCount

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
  exact hRel.mono fun _ _ _ _ hclose => lt_trans hclose hερ

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
    simp [hdeg]
  have hnat : (f + C μ * g).natDegree = g.natDegree :=
    Polynomial.natDegree_add_C_mul_of_natDegree_lt (ne_of_gt hμ) hlt
  have hcard : (f + C μ * g).roots.card = f.roots.card + 1 := by
    rw [hp_split.natDegree_eq_card_roots.symm, hnat, hdeg,
      hf_split.natDegree_eq_card_roots.symm]
  exact Multiset.card_filter_gt_eq_of_rel_with_escaped_extra hsep_x hB hsep_B
    hRel hu ha_mem ha_lt hBx hcard

/--
Endpoint upper root-count equality from local lower counts on the small-positive
family.

The small-positive input near `μ = 0` is supplied explicitly.  On the positive
parameter intervals, the degree is constant, so
`positiveParameter_local_lower_count` supplies the local lower-count hypotheses
needed by `rightFamily_card_roots_gt_eq_of_local_lower_counts`.
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
    (hgf_split : ∀ ν ∈ Set.Icc (0 : ℝ) 1, (g + C ν * f).Splits)
    (hgf_no : ∀ ν ∈ Set.Icc (0 : ℝ) 1, ¬ (g + C ν * f).IsRoot x) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card := by
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    card_filter_gt_add_C_mul_eventually_eq hf_pos hg_pos hdeg hf_split hx
      hlocal_lower
  let μ₀ : ℝ := min (δ / 2) (1 / 2)
  have hμ₀_pos : 0 < μ₀ := lt_min (by positivity) (by norm_num)
  have hμ₀_le_one : μ₀ ≤ 1 := by linarith [min_le_right (δ / 2) (1 / 2)]
  have hμ₀_ltδ : μ₀ < δ := by linarith [min_le_left (δ / 2) (1 / 2), hδ_pos]
  have hsmall := hδ μ₀ hμ₀_pos hμ₀_ltδ
  have hlt : f.natDegree < g.natDegree := by
    simp [hdeg]
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
      (fun μ hμ ρ hρ => positiveParameter_local_lower_count
        (fun ν hν => hfg_split ν (lt_of_lt_of_le hμ₀_pos hν.1) hν.2)
        hdeg_fg hμ hρ)
  have hdeg_gf : ∀ ν ∈ Set.Icc (0 : ℝ) 1,
      (g + C ν * f).natDegree = (g + C (0 : ℝ) * f).natDegree := by
    intro ν _
    simpa using Polynomial.natDegree_add_eq_left_of_natDegree_lt
      ((Polynomial.natDegree_C_mul_le ν f).trans_lt hlt)
  have hgf_eq :=
    rightFamily_card_roots_gt_eq_of_local_lower_counts (f := g) (g := f)
      (μ₀ := 0) (μ₁ := 1) (x := x) zero_le_one hdeg_gf
      hgf_split hgf_no
      (fun μ hμ ρ hρ => positiveParameter_local_lower_count hgf_split hdeg_gf hμ hρ)
  calc
    (f.roots.filter (x < ·)).card =
        ((f + C μ₀ * g).roots.filter (x < ·)).card := hsmall.symm
    _ = ((g + C (1 : ℝ) * f).roots.filter (x < ·)).card := by
      simpa [add_comm] using hfg_eq
    _ = (g.roots.filter (x < ·)).card := by
      simpa using hgf_eq.symm

end RealRooted
