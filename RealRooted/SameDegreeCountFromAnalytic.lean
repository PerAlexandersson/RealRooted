import RealRooted.CommonInterleaverTwo
import RealRooted.PositiveParameterLocalLowerCount
import RealRooted.RootCountLocalConstancy

/-!
# Same-Degree Count Equality from Analytic Inputs

This file starts the issue #41 reuse of the issue #42 count route.  The main
point is that in the same-degree case there is no escaping root at the endpoint:
the right pencil has constant degree, so the local-lower-count/local-constancy
machinery from #42 can be used directly.
-/

open Polynomial

namespace RealRooted

/-- Near a simple root at the threshold, same-degree perturbations can change
the strict-upper root count by at most one, and only upward from the source
side.

This is the crossing analogue of the non-root local-constancy bridge from
`RootCountLocalConstancy`: the analytic input is still the #42 multiplicity
lower-count theorem, but the finite count conclusion allows the single root at
`x` to move across the threshold. -/
theorem exists_eps_card_roots_gt_bounds_near_simple_root
    {f g : ℝ[X]} {μ x : ℝ}
    (hp_split : (f + C μ * g).Splits)
    (hsimple : HasSimpleRoots (f + C μ * g))
    (hroot : (f + C μ * g).IsRoot x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν : ℝ, |ν - μ| < ε →
      (f + C ν * g).Splits →
      (f + C ν * g).natDegree = (f + C μ * g).natDegree →
      (((f + C μ * g).roots.filter (x < ·)).card ≤
          ((f + C ν * g).roots.filter (x < ·)).card ∧
        ((f + C ν * g).roots.filter (x < ·)).card ≤
          ((f + C μ * g).roots.filter (x < ·)).card + 1) := by
  classical
  set p : ℝ[X] := f + C μ * g
  have hp_def : p = f + C μ * g := rfl
  have hx_count : p.roots.count x = 1 := by
    rw [count_roots]
    exact hsimple x (by simpa [hp_def] using hroot)
  have hx_not_erase : x ∉ p.roots.erase x := by
    rw [← Multiset.count_eq_zero, Multiset.count_erase_self, hx_count]
  obtain ⟨η, hη_pos, hη⟩ :=
    Multiset.exists_pos_le_abs_sub_of_not_mem (p.roots.erase x) hx_not_erase
  obtain ⟨ρ, hρ_pos, hρ_lt_η, hsep_centers⟩ :=
    Multiset.exists_pos_lt_and_two_mul_le_abs_sub_toFinset p.roots hη_pos
  obtain ⟨ε, hε_pos, hε⟩ :=
    exists_eps_forall_root_count_le_card_filter_near (f := f) (g := g)
      (μ0 := μ) hp_split ρ hρ_pos
  refine ⟨ε, hε_pos, ?_⟩
  intro ν hν hν_split hν_deg
  have hcount := hε ν hν hν_split hν_deg
  have hcount_local : ∀ a ∈ p.roots.toFinset,
      p.roots.count a ≤
        ((f + C ν * g).roots.filter (fun q => |q - a| < ρ)).card := by
    intro a ha
    simpa [p, hp_def] using hcount a (by simpa [p, hp_def] using ha)
  obtain ⟨u, hu, hrel⟩ :=
    Multiset.exists_rel_le_of_forall_le_count (s := p.roots)
      (t := (f + C ν * g).roots) hsep_centers hcount_local
  have hcard : (f + C ν * g).roots.card = p.roots.card := by
    rw [hν_split.natDegree_eq_card_roots.symm,
      hp_split.natDegree_eq_card_roots.symm, hν_deg]
  have hu_card : u.card = (f + C ν * g).roots.card := by
    rw [hcard, Multiset.card_eq_card_of_rel hrel]
  have hu_eq : u = (f + C ν * g).roots :=
    Multiset.eq_of_le_of_card_le hu hu_card.ge
  rw [hu_eq] at hrel
  have hsep_gt : ∀ r ∈ p.roots, x < r → ρ ≤ |r - x| := by
    intro r hr hxr
    have hr_ne : r ≠ x := ne_of_gt hxr
    exact le_trans (le_of_lt hρ_lt_η)
      (hη r ((Multiset.mem_erase_of_ne hr_ne).2 hr))
  have hsep_ne : ∀ r ∈ p.roots, r ≠ x → ρ ≤ |r - x| := by
    intro r hr hrx
    exact le_trans (le_of_lt hρ_lt_η)
      (hη r ((Multiset.mem_erase_of_ne hrx).2 hr))
  constructor
  · simpa [p, hp_def] using
      Multiset.card_filter_gt_le_of_rel_abs_sub_lt_of_gt_sep hsep_gt hrel
  · simpa [p, hp_def] using
      Multiset.card_filter_gt_le_add_one_of_rel_abs_sub_lt_of_count_eq_one
        hsep_ne hx_count hrel

/-- Local lower counts from the #42 multiplicity-continuity theorem give
strict-upper root-count equality on the unit interval. -/
theorem rightFamily_card_roots_gt_eq_zero_one_of_constant_degree
    {f g : ℝ[X]} {x : ℝ}
    (hdeg : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      (f + C μ * g).natDegree = (f + C (0 : ℝ) * g).natDegree)
    (hrr : ∀ μ ∈ Set.Icc (0 : ℝ) 1, (f + C μ * g).Splits)
    (hne : ∀ μ ∈ Set.Icc (0 : ℝ) 1, ¬ (f + C μ * g).IsRoot x) :
    ((f + C (0 : ℝ) * g).roots.filter (x < ·)).card =
      ((f + C (1 : ℝ) * g).roots.filter (x < ·)).card :=
  rightFamily_card_roots_gt_eq_of_local_lower_counts zero_le_one hdeg hrr hne
    (fun _ hμ _ hρ => positiveParameter_local_lower_count hrr hdeg hμ hρ)

/-- If an equal-degree positive-combination pair has no root at `x` anywhere in
the nonnegative right pencil, then `f` and `g` have the same number of roots
strictly above `x`.

This is the same-degree endpoint analogue of the #42 closed-segment count
assembly, but it uses only constant-degree local constancy; no escaping-root
argument is involved. -/
theorem sameDegree_card_roots_gt_eq_of_no_rightFamily_isRoot
    {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card := by
  have hf_split : f.Splits :=
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
  have hsplit_fg : ∀ μ ∈ Set.Icc (0 : ℝ) 1, (f + C μ * g).Splits := by
    intro μ hμ
    by_cases hμ0 : μ = 0
    · simpa [hμ0] using hf_split
    · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ.1 (fun h => hμ0 h.symm)
      simpa using (hfg (lam := 1) (μ := μ) zero_lt_one hμ_pos).2
  have hdeg_fg : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      (f + C μ * g).natDegree = (f + C (0 : ℝ) * g).natDegree := by
    intro μ hμ
    by_cases hμ0 : μ = 0
    · simp [hμ0]
    · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ.1 (fun h => hμ0 h.symm)
      have hle : f.natDegree ≤ g.natDegree := by rw [hdeg]
      simpa [hdeg] using
        (PosComboRealRooted.family_natDegree_right
          (f := f) (g := g) hle hf_pos hg_pos hμ_pos)
  have hne_fg : ∀ μ ∈ Set.Icc (0 : ℝ) 1, ¬ (f + C μ * g).IsRoot x := by
    intro μ hμ
    exact hno hμ.1
  have hfg_count :=
    rightFamily_card_roots_gt_eq_zero_one_of_constant_degree
      (f := f) (g := g) (x := x) hdeg_fg hsplit_fg hne_fg
  have hsplit_gf : ∀ μ ∈ Set.Icc (0 : ℝ) 1, (g + C μ * f).Splits := by
    intro μ hμ
    by_cases hμ0 : μ = 0
    · simpa [hμ0] using hg_split
    · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ.1 (fun h => hμ0 h.symm)
      simpa [add_comm] using
        (hfg (lam := μ) (μ := 1) hμ_pos zero_lt_one).2
  have hdeg_gf : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      (g + C μ * f).natDegree = (g + C (0 : ℝ) * f).natDegree := by
    intro μ hμ
    by_cases hμ0 : μ = 0
    · simp [hμ0]
    · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ.1 (fun h => hμ0 h.symm)
      have hle : g.natDegree ≤ f.natDegree := by rw [hdeg]
      simpa [hdeg] using
        (PosComboRealRooted.family_natDegree_right
          (f := g) (g := f) hle hg_pos hf_pos hμ_pos)
  have hne_gf : ∀ μ ∈ Set.Icc (0 : ℝ) 1, ¬ (g + C μ * f).IsRoot x := by
    intro μ hμ
    by_cases hμ0 : μ = 0
    · simpa [hμ0] using hxg
    · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ.1 (fun h => hμ0 h.symm)
      exact rightFamily_not_isRoot_add_left_of_pos hμ_pos hno
  have hgf_count :=
    rightFamily_card_roots_gt_eq_zero_one_of_constant_degree
      (f := g) (g := f) (x := x) hdeg_gf hsplit_gf hne_gf
  calc
    (f.roots.filter (x < ·)).card =
        ((f + C (0 : ℝ) * g).roots.filter (x < ·)).card := by simp
    _ = ((f + C (1 : ℝ) * g).roots.filter (x < ·)).card := hfg_count
    _ = ((g + C (1 : ℝ) * f).roots.filter (x < ·)).card := by
      simp [add_comm]
    _ = ((g + C (0 : ℝ) * f).roots.filter (x < ·)).card := hgf_count.symm
    _ = (g.roots.filter (x < ·)).card := by simp

/-- Pointwise same-degree upper root-count bound in the no-crossing case. -/
theorem sameDegree_rootCountAbove_pointwise_of_no_rightFamily_isRoot
    {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  have hcard :=
    sameDegree_card_roots_gt_eq_of_no_rightFamily_isRoot
      hf_pos hg_pos hfg hdeg hxg hno
  have hcard_int :
      ((f.roots.filter (x < ·)).card : ℤ) =
        (g.roots.filter (x < ·)).card := by
    exact_mod_cast hcard
  constructor <;> lia

/-- Pointwise same-degree upper root-count bound when the positive right
pencil never hits the threshold. -/
theorem sameDegree_rootCountAbove_pointwise_of_not_exists_pos_isRoot
    {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hno_pos : ¬ ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) :
    ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  refine
    sameDegree_rootCountAbove_pointwise_of_no_rightFamily_isRoot
      hf_pos hg_pos hfg hdeg hxg ?_
  intro μ hμ hroot
  by_cases hμ0 : μ = 0
  · exact hxf (by simpa [hμ0] using hroot)
  · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ (fun h => hμ0 h.symm)
    exact hno_pos ⟨μ, hμ_pos, hroot⟩

end RealRooted
