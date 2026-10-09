import RealRooted.Interlacing.ResidueCriterion

open Polynomial BigOperators

noncomputable section

namespace RealRooted

private theorem exists_affine_root_deletion_remainder
    {f g : ℝ[X]} {d : ℕ} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfd : f.natDegree = d) (hgd : g.natDegree = d + 1)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff) :
    ∃ (α β : ℝ) (r : ℝ[X]),
      0 < α ∧ α = g.leadingCoeff / f.leadingCoeff ∧
      r.degree < (d : WithBot ℕ) ∧
      g = C α * X * f + C β * f + r := by
  let α : ℝ := g.leadingCoeff / f.leadingCoeff
  let u : ℝ[X] := g - C α * (X * f)
  have hxf : X * f ≠ 0 := mul_ne_zero X_ne_zero hf
  have hxfdeg : (X * f).natDegree = d + 1 := by
    rw [natDegree_X_mul hf, hfd]
  have hxfpos : 0 < (X * f).leadingCoeff := by
    simpa [leadingCoeff_mul] using hflc
  have hu_deg : u.degree < ((d + 1 : ℕ) : WithBot ℕ) := by
    have h := degree_sub_c₀_mul_lt hxf hg (hgd.trans hxfdeg.symm) hxfpos
    simpa [u, α, hxfdeg, leadingCoeff_mul] using h
  have hα : 0 < α := by
    dsimp [α]
    exact div_pos hglc hflc
  have hα_eq : α = g.leadingCoeff / f.leadingCoeff := rfl
  by_cases hu : u = 0
  · refine ⟨α, 0, 0, hα, hα_eq, ?_, ?_⟩
    · exact WithBot.bot_lt_coe d
    · have hu' : g = C α * (X * f) := sub_eq_zero.mp hu
      calc
        g = C α * (X * f) := hu'
        _ = C α * X * f + C 0 * f + 0 := by simp; ring
  · have hu_nat_lt : u.natDegree < d + 1 := by
      have h := hu_deg
      rw [degree_eq_natDegree hu] at h
      exact_mod_cast h
    by_cases hud : u.natDegree < d
    · refine ⟨α, 0, u, hα, hα_eq, ?_, ?_⟩
      · rw [degree_eq_natDegree hu]
        exact_mod_cast hud
      · dsimp [u]
        simp only [C_0, zero_mul, add_zero]
        ring
    · have hud_eq : u.natDegree = d := by lia
      let β : ℝ := u.leadingCoeff / f.leadingCoeff
      let r : ℝ[X] := u - C β * f
      have hr_deg : r.degree < (d : WithBot ℕ) := by
        have h := degree_sub_c₀_mul_lt hf hu (hud_eq.trans hfd.symm) hflc
        simpa [r, β, hfd] using h
      refine ⟨α, β, r, hα, hα_eq, hr_deg, ?_⟩
      dsimp [u, r]
      ring

/-- A coprime positive-leading successor interlacer has a positive root-deletion
expansion. The no-common-root hypothesis is necessary because `StrictInterl`
itself permits shared roots, which would make the corresponding coefficient zero.
The deletion is monic division by `X - C s`. -/
theorem StrictInterl.root_deletion_expansion
    {f g : ℝ[X]} {d : ℕ}
    (hinterl : StrictInterl f g)
    (hfd : f.natDegree = d) (hgd : g.natDegree = d + 1)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff)
    (hfnd : f.roots.Nodup)
    (hno : ∀ s, f.IsRoot s → ¬g.IsRoot s) :
    ∃ (α β : ℝ),
      0 < α ∧
      g = (C α * X + C β) * f -
        ∑ s ∈ f.roots.toFinset,
          C (-g.eval s / f.derivative.eval s) * (f /ₘ (X - C s)) ∧
      ∀ s ∈ f.roots, 0 < -g.eval s / f.derivative.eval s := by
  have hf : f ≠ 0 := hinterl.1.1
  have hg : g ≠ 0 := hinterl.2.1.1
  have hfpos : HasPosLeadingCoeff f := hflc
  have hgpos : HasPosLeadingCoeff g := hglc
  obtain ⟨α, β, r, hα, hα_eq, hrdeg, hgr⟩ :=
    exists_affine_root_deletion_remainder hf hg hfd hgd hflc hglc
  have hratio : ∀ s ∈ f.roots, 0 < -g.eval s / f.derivative.eval s := by
    intro s hs
    have hroot : f.IsRoot s := isRoot_of_mem_roots hs
    have hprod : g.eval s * f.derivative.eval s < 0 :=
      hinterl.eval_mul_derivative_neg_of_left_root_of_no_common
        hfpos hgpos hno hroot
    have hder : f.derivative.eval s ≠ 0 := by
      have hmult : f.rootMultiplicity s = 1 := by
        simpa [count_roots] using Multiset.count_eq_one_of_mem hfnd hs
      exact eval_derivative_ne_zero_of_rootMultiplicity_eq_one hroot hmult
    have hquot : g.eval s / f.derivative.eval s < 0 := by
      rcases lt_or_gt_of_ne hder with hder_neg | hder_pos
      · have hgeval : 0 < g.eval s := by nlinarith
        exact div_neg_of_pos_of_neg hgeval hder_neg
      · have hgeval : g.eval s < 0 := by nlinarith
        exact div_neg_of_neg_of_pos hgeval hder_pos
    simpa only [neg_div] using neg_pos.mpr hquot
  have hrem_eval : ∀ s ∈ f.roots, r.eval s = g.eval s := by
    intro s hs
    have hroot : f.IsRoot s := isRoot_of_mem_roots hs
    rw [hgr]
    simp only [eval_add, eval_mul, eval_C, hroot.eq_zero, mul_zero, zero_add,
      add_zero]
  have hsum_eq :
      (∑ s ∈ f.roots.toFinset,
          C (r.eval s / f.derivative.eval s) * (f /ₘ (X - C s))) = r := by
    by_cases hdpos : 1 ≤ d
    · have hfdpos : 1 ≤ f.natDegree := by simpa [hfd] using hdpos
      have hrdeg' : r.degree < (f.natDegree : WithBot ℕ) := by
        simpa [hfd] using hrdeg
      have hlag := lagInterp_eq_g hinterl.1.2 hfnd hfdpos hrdeg'
      simpa [lagInterp] using hlag
    · have hdzero : d = 0 := by lia
      have hrzero : r = 0 := by
        by_contra hrzero
        have hdegree := degree_eq_natDegree hrzero
        have hlt : r.degree < (0 : WithBot ℕ) := by simpa [hdzero] using hrdeg
        rw [hdegree] at hlt
        exact (not_lt_of_ge (by simp)) hlt
      simp [hrzero]
  have hsum_eval :
      (∑ s ∈ f.roots.toFinset,
          C (-g.eval s / f.derivative.eval s) * (f /ₘ (X - C s))) = -r := by
    calc
      (∑ s ∈ f.roots.toFinset,
          C (-g.eval s / f.derivative.eval s) * (f /ₘ (X - C s))) =
          -∑ s ∈ f.roots.toFinset,
            C (r.eval s / f.derivative.eval s) * (f /ₘ (X - C s)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro s hs
        have hsroot : s ∈ f.roots := Multiset.mem_toFinset.mp hs
        rw [hrem_eval s hsroot]
        rw [neg_div, C_neg, neg_mul]
      _ = -r := by rw [hsum_eq]
  refine ⟨α, β, hα, ?_, hratio⟩
  rw [hsum_eval, hgr]
  ring

end RealRooted
