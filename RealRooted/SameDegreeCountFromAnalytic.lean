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
  have hx_count : p.roots.count x = 1 :=
    hsimple.roots_count_eq_one (by simpa [hp_def] using hroot)
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
        ((f + C ν * g).roots.filter (fun q ↦ |q - a| < ρ)).card :=
    fun a ha ↦ by
    simp_all
  obtain ⟨u, hu, hrel⟩ :=
    Multiset.exists_rel_le_of_forall_le_count (s := p.roots)
      (t := (f + C ν * g).roots) hsep_centers hcount_local
  have hcard : (f + C ν * g).roots.card = p.roots.card := by
    simpa [hν_split.natDegree_eq_card_roots.symm,
      hp_split.natDegree_eq_card_roots.symm] using hν_deg
  have hu_card : u.card = (f + C ν * g).roots.card := by
    simpa [hcard] using (Multiset.card_eq_card_of_rel hrel).symm
  have hu_eq : u = (f + C ν * g).roots :=
    Multiset.eq_of_le_of_card_le hu hu_card.ge
  rw [hu_eq] at hrel
  have hsep_gt : ∀ r ∈ p.roots, x < r → ρ ≤ |r - x| := fun r hr hxr => by
    have hr_ne : r ≠ x := ne_of_gt hxr
    exact le_trans (le_of_lt hρ_lt_η)
      (hη r ((Multiset.mem_erase_of_ne hr_ne).2 hr))
  have hsep_ne : ∀ r ∈ p.roots, r ≠ x → ρ ≤ |r - x| := fun r hr hrx => by
    exact le_trans (le_of_lt hρ_lt_η)
      (hη r ((Multiset.mem_erase_of_ne hrx).2 hr))
  constructor
  · simpa [p, hp_def] using
      Multiset.card_filter_gt_le_of_rel_abs_sub_lt_of_gt_sep hsep_gt hrel
  · simpa [p, hp_def] using
      Multiset.card_filter_gt_le_add_one_of_rel_abs_sub_lt_of_count_eq_one
        hsep_ne hx_count hrel

/-- On a nonnegative same-degree right-family interval with no root at the
threshold, the strict-upper root count is constant. -/
theorem rightFamily_card_roots_gt_eq_of_no_isRoot_interval_sameDegree
    {f g : ℝ[X]} {μ₀ μ₁ x : ℝ}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hμ₀_nonneg : 0 ≤ μ₀) (hμ₀μ₁ : μ₀ ≤ μ₁)
    (hne : ∀ μ ∈ Set.Icc μ₀ μ₁, ¬ (f + C μ * g).IsRoot x) :
    ((f + C μ₀ * g).roots.filter (x < ·)).card =
      ((f + C μ₁ * g).roots.filter (x < ·)).card := by
  have hf_split : f.Splits :=
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
  have hsplit_nonneg : ∀ μ : ℝ, 0 ≤ μ → (f + C μ * g).Splits := fun μ hμ ↦ by
    by_cases hμ0 : μ = 0
    · simp_all
    · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ (fun h ↦ hμ0 h.symm)
      simpa using (hfg (lam := 1) (μ := μ) zero_lt_one hμ_pos).2
  have hdeg_nonneg :
      ∀ μ : ℝ, 0 ≤ μ → (f + C μ * g).natDegree = f.natDegree :=
    fun μ hμ => by
    by_cases hμ0 : μ = 0
    · simp [hμ0]
    · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ (fun h => hμ0 h.symm)
      have hle : f.natDegree ≤ g.natDegree := by simp [hdeg]
      simpa [hdeg] using
        (PosComboRealRooted.family_natDegree_right
          (f := f) (g := g) hle hf_pos hg_pos hμ_pos)
  refine
    rightFamily_card_roots_gt_eq_of_local_lower_counts hμ₀μ₁ ?_ ?_ hne ?_
  · grind
  · grind
  · intro μ hμ ρ hρ
    exact positiveParameter_local_lower_count
      (fun ν hν ↦ hsplit_nonneg ν (le_trans hμ₀_nonneg hν.1))
      (fun ν hν ↦ by
        grind)
      hμ hρ

/-- Local lower counts from the #42 multiplicity-continuity theorem give
strict-upper root-count equality on the unit interval. -/
theorem rightFamily_card_roots_gt_eq_zero_one_of_constant_degree
    {f g : ℝ[X]} {x : ℝ}
    (hdeg : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      (f + C μ * g).natDegree = (f + C (0 : ℝ) * g).natDegree)
    (hrr : ∀ μ ∈ Set.Icc (0 : ℝ) 1, (f + C μ * g).Splits)
    (hne : ∀ μ ∈ Set.Icc (0 : ℝ) 1, ¬ (f + C μ * g).IsRoot x) :
    ((f + C (0 : ℝ) * g).roots.filter (x < ·)).card =
      ((f + C (1 : ℝ) * g).roots.filter (x < ·)).card := by
  simpa using
    (rightFamily_card_roots_gt_eq_zero_param_of_constant_degree
      (f := f) (g := g) (x := x) (μ := 1) zero_lt_one hdeg hrr hne).symm

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
  have hsplit_fg : ∀ μ ∈ Set.Icc (0 : ℝ) 1, (f + C μ * g).Splits :=
    fun μ hμ ↦ by
    by_cases hμ0 : μ = 0
    · simp_all
    · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ.1 (fun h ↦ hμ0 h.symm)
      simpa using (hfg (lam := 1) (μ := μ) zero_lt_one hμ_pos).2
  have hdeg_fg : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      (f + C μ * g).natDegree = (f + C (0 : ℝ) * g).natDegree :=
    fun μ hμ => by
    by_cases hμ0 : μ = 0
    · simp [hμ0]
    · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ.1 (fun h => hμ0 h.symm)
      have hle : f.natDegree ≤ g.natDegree := by simp [hdeg]
      simpa [hdeg] using
        (PosComboRealRooted.family_natDegree_right
          (f := f) (g := g) hle hf_pos hg_pos hμ_pos)
  have hne_fg : ∀ μ ∈ Set.Icc (0 : ℝ) 1, ¬ (f + C μ * g).IsRoot x :=
    fun μ hμ => hno hμ.1
  have hfg_count :=
    rightFamily_card_roots_gt_eq_zero_one_of_constant_degree
      (f := f) (g := g) (x := x) hdeg_fg hsplit_fg hne_fg
  have hsplit_gf : ∀ μ ∈ Set.Icc (0 : ℝ) 1, (g + C μ * f).Splits :=
    fun μ hμ ↦ by
    by_cases hμ0 : μ = 0
    · simp_all
    · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ.1 (fun h ↦ hμ0 h.symm)
      simpa [add_comm] using
        (hfg (lam := μ) (μ := 1) hμ_pos zero_lt_one).2
  have hdeg_gf : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      (g + C μ * f).natDegree = (g + C (0 : ℝ) * f).natDegree :=
    fun μ hμ => by
    by_cases hμ0 : μ = 0
    · simp [hμ0]
    · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ.1 (fun h => hμ0 h.symm)
      have hle : g.natDegree ≤ f.natDegree := by simp [hdeg]
      simpa [hdeg] using
        (PosComboRealRooted.family_natDegree_right
          (f := g) (g := f) hle hg_pos hf_pos hμ_pos)
  have hne_gf : ∀ μ ∈ Set.Icc (0 : ℝ) 1, ¬ (g + C μ * f).IsRoot x :=
    fun μ hμ ↦ by
    by_cases hμ0 : μ = 0
    · simp_all
    · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ.1 (fun h ↦ hμ0 h.symm)
      exact rightFamily_not_isRoot_add_left_of_pos hμ_pos hno
  have hgf_count :=
    rightFamily_card_roots_gt_eq_zero_one_of_constant_degree
      (f := g) (g := f) (x := x) hdeg_gf hsplit_gf hne_gf
  grind

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
  simp_all

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
  grind

/-- Pointwise same-degree upper root-count bound in the single-crossing case. -/
theorem sameDegree_rootCountAbove_pointwise_of_exists_pos_isRoot
    {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hxf : ¬ f.IsRoot x) (hxg : ¬ g.IsRoot x)
    (hcross : ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) :
    ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  obtain ⟨μ, hμ, hroot⟩ := hcross
  obtain ⟨_, _, _, _, huniq⟩ :=
    hfg.root_crossing_data_unique_add_right hno hμ hroot
  have hsimple : HasSimpleRoots (f + C μ * g) :=
    hfg.hasSimpleRoots_add_right hno hμ
  obtain ⟨ε, hε_pos, hε⟩ :=
    exists_eps_card_roots_gt_bounds_near_simple_root
      (f := f) (g := g) (μ := μ) (x := x)
      (by simpa using (hfg (lam := 1) (μ := μ) zero_lt_one hμ).2)
      hsimple hroot
  let δ : ℝ := min (μ / 2) (ε / 2)
  have hδ_pos : 0 < δ := by
    grind
  have hδ_lt_μ : δ < μ := by
    grind
  have hδ_lt_ε : δ < ε := by grind
  let μL : ℝ := μ - δ
  let μR : ℝ := μ + δ
  have hμL_pos : 0 < μL := by grind
  have hμL_lt_μ : μL < μ := by grind
  have hμR_pos : 0 < μR := by
    grind
  have hμ_lt_μR : μ < μR := by grind
  have hdistL : |μL - μ| < ε := by
    grind
  have hdistR : |μR - μ| < ε := by grind
  have hsplit_pos : ∀ τ : ℝ, 0 < τ → (f + C τ * g).Splits := fun τ hτ ↦ by
    simpa using (hfg (lam := 1) (μ := τ) zero_lt_one hτ).2
  have hdeg_pos :
      ∀ τ : ℝ, 0 < τ → (f + C τ * g).natDegree = f.natDegree :=
    fun τ hτ => by
    have hle : f.natDegree ≤ g.natDegree := by simp [hdeg]
    simpa [hdeg] using
      (PosComboRealRooted.family_natDegree_right
        (f := f) (g := g) hle hf_pos hg_pos hτ)
  have hμL_deg : (f + C μL * g).natDegree = (f + C μ * g).natDegree := by
    simp [hdeg_pos μL hμL_pos, hdeg_pos μ hμ]
  have hμR_deg : (f + C μR * g).natDegree = (f + C μ * g).natDegree := by
    simp [hdeg_pos μR hμR_pos, hdeg_pos μ hμ]
  obtain ⟨hP_le_L, hL_le_P⟩ :=
    hε μL hdistL (hsplit_pos μL hμL_pos) hμL_deg
  obtain ⟨hP_le_R, hR_le_P⟩ :=
    hε μR hdistR (hsplit_pos μR hμR_pos) hμR_deg
  have hL_le_R_add_one :
      ((f + C μL * g).roots.filter (x < ·)).card ≤
        ((f + C μR * g).roots.filter (x < ·)).card + 1 :=
    le_trans hL_le_P (Nat.succ_le_succ hP_le_R)
  have hR_le_L_add_one :
      ((f + C μR * g).roots.filter (x < ·)).card ≤
        ((f + C μL * g).roots.filter (x < ·)).card + 1 :=
    le_trans hR_le_P (Nat.succ_le_succ hP_le_L)
  have hne_left_interval :
      ∀ τ ∈ Set.Icc (0 : ℝ) μL, ¬ (f + C τ * g).IsRoot x :=
    fun τ hτ hrootτ => by
    grind
  have hF_eq_L :
      (f.roots.filter (x < ·)).card =
        ((f + C μL * g).roots.filter (x < ·)).card := by
    simpa using
      rightFamily_card_roots_gt_eq_of_no_isRoot_interval_sameDegree
        (f := f) (g := g) (μ₀ := 0) (μ₁ := μL) (x := x)
        hf_pos hg_pos hfg hdeg (by norm_num) (le_of_lt hμL_pos)
        hne_left_interval
  have hne_right_interval :
      ∀ η ∈ Set.Icc (0 : ℝ) μR⁻¹, ¬ (g + C η * f).IsRoot x :=
    fun η hη hrootη ↦ by
    by_cases hη0 : η = 0
    · grind
    · have hη_pos : 0 < η := lt_of_le_of_ne hη.1 (fun h ↦ hη0 h.symm)
      have hη_ne : η ≠ 0 := ne_of_gt hη_pos
      have hroot_right : (f + C η⁻¹ * g).IsRoot x := by
        have hiff :=
          add_right_isRoot_iff_add_left_inv
            (f := f) (g := g) (μ := η⁻¹) (x := x) (inv_ne_zero hη_ne)
        grind
      have hη_inv_eq : η⁻¹ = μ :=
        huniq η⁻¹ (inv_pos.mpr hη_pos) hroot_right
      have hη_eq : η = μ⁻¹ := by grind
      have hμR_inv_lt_μ_inv : μR⁻¹ < μ⁻¹ := by
        simpa [one_div] using one_div_lt_one_div_of_lt hμ hμ_lt_μR
      grind
  have hG_eq_Rinv :
      (g.roots.filter (x < ·)).card =
        ((g + C μR⁻¹ * f).roots.filter (x < ·)).card := by
    have hμR_inv_pos : 0 < μR⁻¹ := inv_pos.mpr hμR_pos
    simpa using
      rightFamily_card_roots_gt_eq_of_no_isRoot_interval_sameDegree
        (f := g) (g := f) (μ₀ := 0) (μ₁ := μR⁻¹) (x := x)
        hg_pos hf_pos (PosComboRealRooted.comm hfg) hdeg.symm
        (by norm_num) (le_of_lt hμR_inv_pos) hne_right_interval
  have hR_eq_Rinv :
      ((f + C μR * g).roots.filter (x < ·)).card =
        ((g + C μR⁻¹ * f).roots.filter (x < ·)).card :=
    add_right_roots_gt_card_eq_add_left_inv
      (f := f) (g := g) (μ := μR) (x := x) (ne_of_gt hμR_pos)
  grind

/-- Same-degree strict-upper root-count bounds from positive-combination
real-rootedness and no common roots.

This is the nonnegative-coefficient-free analytic count spine used by the
same-degree Liu bridge. -/
theorem sameDegree_rootCountAbove_bounds_of_posCombo_noCommon
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  intro x hxf hxg
  by_cases hcross : ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x
  · exact
      sameDegree_rootCountAbove_pointwise_of_exists_pos_isRoot
        hf_pos hg_pos hfg hdeg hno hxf hxg hcross
  · exact
      sameDegree_rootCountAbove_pointwise_of_not_exists_pos_isRoot
        hf_pos hg_pos hfg hdeg hxf hxg hcross

/-- The #41 common-non-root upper root-count target follows from the #42
analytic count spine. -/
theorem posComboNoCommonSameDegreeRootCountAboveNonRootNonneg_from_analytic :
    PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement :=
  fun _ _ hf_pos hg_pos _hfnn _hgnn hfg hdeg hno =>
    sameDegree_rootCountAbove_bounds_of_posCombo_noCommon
      hf_pos hg_pos hfg hdeg hno

/-- The repaired #41 same-degree pair-interleaver endpoint follows from the
#42 analytic count spine. -/
theorem posComboNoCommonSameDegreePairHasCommonInterleaverNonneg_from_analytic :
    (∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    ∃ h : ℝ[X], Prec f h ∧ Prec g h) :=
  sameDegreePairHasCommonInterleaver_nonneg_of_rootCountAboveNonRoot
    posComboNoCommonSameDegreeRootCountAboveNonRootNonneg_from_analytic

end RealRooted
