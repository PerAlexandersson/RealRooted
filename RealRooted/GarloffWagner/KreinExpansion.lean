import RealRooted.GarloffWagner.KreinData

/-!
# Garloff--Wagner Krein expansions

Positive root-deleted expansions and their Theorem 11 proper-position
consequences.
-/

open Polynomial

noncomputable section

namespace RealRooted

theorem exists_kreinRootDeletedExpansion_right {f g : ℝ[X]}
    (hfg : Prec f g) (hgdeg : 0 < g.natDegree) :
    ∃ c : ℝ, ∃ l : List (ℝ × ℝ[X]),
      (∀ ap ∈ l, ∃ u : ℝ, g = (X - C u) * ap.2) ∧
        (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        f = C c * g + weightedSum l := by
  classical
  rcases exists_C_mul_sub_natDegree_lt_of_le hfg.2.1.1 hgdeg
      hfg.natDegree_le with ⟨c, hcdeg⟩
  let roots : List ℝ := g.roots.toFinset.toList
  have hroots_nodup : roots.Nodup := Finset.nodup_toList _
  have hroot : ∀ u ∈ roots, g.IsRoot u := by
    intro u hu
    exact (mem_roots hfg.2.1.1).mp
      (Multiset.mem_toFinset.mp (Finset.mem_toList.mp hu))
  have hdata : ∀ u ∈ roots, ∃ a : ℝ, ∃ q : ℝ[X],
      g = (X - C u) * q ∧
        IsGWKreinSummand g q ∧
        (X - C u) ^ (g.rootMultiplicity u) ∣
          f - C c * g - C a * q := by
    intro u hu
    exact exists_kreinCoefficientData_of_right_isRoot hfg hfg.2.1.2 c (hroot u hu)
  choose a q hfactor hsummand hgain using hdata
  let a' : ℝ → ℝ := fun u => if hu : u ∈ roots then a u hu else 0
  let q' : ℝ → ℝ[X] := fun u => if hu : u ∈ roots then q u hu else 0
  let l : List (ℝ × ℝ[X]) := roots.map fun u => (a' u, q' u)
  have hfactor' : ∀ u ∈ roots, g = (X - C u) * q' u := by
    intro u hu
    simp [q', hu, hfactor u hu]
  have hgain' : ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ f - C c * g - C (a' u) * q' u := by
    intro u hu
    simp [a', q', hu, hgain u hu]
  have hdiv_roots : ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ f - C c * g - weightedSum l := by
    simpa [l] using
      fullRootMultiplicity_dvd_sub_weightedSum_rootDeleted
        hfg.2.1.1 roots hroots_nodup a' q' hfactor' hgain'
  have hdiv_all_roots : ∀ u ∈ g.roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ f - C c * g - weightedSum l := by
    intro u hu
    exact hdiv_roots u (by
      rw [Finset.mem_toList, Multiset.mem_toFinset]
      exact hu)
  have hdiv : g ∣ f - C c * g - weightedSum l :=
    dvd_of_roots_fullRootMultiplicity_dvd hfg.2.1.1 hfg.2.1.2 hdiv_all_roots
  have hwsdeg : (weightedSum l).natDegree < g.natDegree := by
    simpa [l] using
      natDegree_weightedSum_deletedFactors_lt hfg.2.1.1 hgdeg roots a' q' hfactor'
  have hresdeg : (f - C c * g - weightedSum l).natDegree < g.natDegree :=
    natDegree_sub_lt_of_both_lt hgdeg hcdeg hwsdeg
  have hzero : f - C c * g - weightedSum l = 0 :=
    eq_zero_of_dvd_of_natDegree_lt hfg.2.1.1 hdiv hresdeg
  refine ⟨c, l, ?_, ?_, ?_⟩
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨u, hu, rfl⟩
    exact ⟨u, hfactor' u hu⟩
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨u, hu, rfl⟩
    simp [q', hu, hsummand u hu]
  · have hsub : f - C c * g = weightedSum l := sub_eq_zero.mp hzero
    rw [← hsub]
    ring

/-- A nonzero splitting polynomial precedes the polynomial obtained by adding
one real linear factor. -/
theorem prec_self_X_sub_C_mul {r : ℝ[X]} (hr0 : r ≠ 0) (hrs : r.Splits)
    (u : ℝ) :
    Prec r ((X - C u) * r) := by
  have hright0 : (X - C u) * r ≠ 0 := mul_ne_zero (X_sub_C_ne_zero u) hr0
  have hright_splits : ((X - C u) * r).Splits :=
    (Polynomial.Splits.X_sub_C u).mul hrs
  have hall : AllComboRealRooted r ((X - C u) * r) := by
    intro α β
    have hlin_splits : (C α + C β * (X - C u : ℝ[X])).Splits := by
      apply Polynomial.Splits.of_natDegree_le_one
      have hdegC : (C α : ℝ[X]).natDegree ≤ 1 := by simp
      have hdegmul : (C β * (X - C u : ℝ[X])).natDegree ≤ 1 := by
        exact (natDegree_C_mul_le β (X - C u : ℝ[X])).trans (by simp)
      exact natDegree_add_le_of_le hdegC hdegmul
    have hfact :
        C α * r + C β * ((X - C u) * r) =
          (C α + C β * (X - C u)) * r := by
      ring
    rw [hfact]
    exact hlin_splits.mul hrs
  have hdeg : r.natDegree + 1 = ((X - C u) * r).natDegree := by
    rw [natDegree_mul (X_sub_C_ne_zero u) hr0, natDegree_X_sub_C]
    exact (Nat.add_comm 1 r.natDegree).symm
  have hprec_or :=
    prec_of_allComboRealRooted hr0 hrs hright0 hright_splits hall (Or.inl hdeg)
  exact prec_forward_of_orientation_of_succDegree hdeg.symm hprec_or

/-- Sign input for the Krein coefficient: after stripping the common
`(X - C u)^(m - 1)` factor from `f ≪ g`, the quotient of `f` has the same sign
as the full root-deleted quotient of `g` at `u`. -/
theorem kreinCoefficient_eval_div_nonneg
    {f g s r : ℝ[X]} {u : ℝ}
    (hfg : Prec f g) (hfpos : HasPosLeadingCoeff f)
    (hgpos : HasPosLeadingCoeff g) (hu : g.IsRoot u)
    (hf_factor : f = (X - C u) ^ (g.rootMultiplicity u - 1) * s)
    (hg_factor : g = (X - C u) ^ (g.rootMultiplicity u) * r)
    (hr0 : r ≠ 0) (hrs : r.Splits) (hr_eval : r.eval u ≠ 0) :
    0 ≤ s.eval u / r.eval u := by
  let m : ℕ := g.rootMultiplicity u
  by_cases hs_eval : s.eval u = 0
  · simp [hs_eval]
  have hm : 1 ≤ m := by
    dsimp [m]
    exact Nat.succ_le_of_lt ((rootMultiplicity_pos hfg.2.1.1).2 hu)
  have hf_factor_m : f = (X - C u) ^ (m - 1) * s := by simpa [m] using hf_factor
  have hg_factor_m : g = (X - C u) ^ m * r := by simpa [m] using hg_factor
  have hg_common : g = (X - C u) ^ (m - 1) * ((X - C u) * r) := by
    rw [hg_factor_m]
    nth_rw 1 [show m = m - 1 + 1 by exact (Nat.sub_add_cancel hm).symm]
    ring_nf
  have hprec_common :
      Prec ((X - C u) ^ (m - 1) * s)
        ((X - C u) ^ (m - 1) * ((X - C u) * r)) := by
    rw [← hf_factor_m, ← hg_common]
    exact hfg
  have hsr_prec : Prec s ((X - C u) * r) :=
    prec_of_prec_mul_pow_X_sub_C_both u (m - 1) hprec_common
  have hs_pos : HasPosLeadingCoeff s := by
    have hfpos' : HasPosLeadingCoeff ((X - C u) ^ (m - 1) * s) := by
      rw [← hf_factor_m]
      exact hfpos
    exact hasPosLeadingCoeff_of_pow_X_sub_C_mul hfpos'
  have hr_pos : HasPosLeadingCoeff r := by
    have hgpos' : HasPosLeadingCoeff ((X - C u) ^ m * r) := by
      rw [← hg_factor_m]
      exact hgpos
    exact hasPosLeadingCoeff_of_pow_X_sub_C_mul hgpos'
  have hrr_prec : Prec r ((X - C u) * r) := prec_self_X_sub_C_mul hr0 hrs u
  have hroot_right : ((X - C u) * r).IsRoot u := by
    rw [Polynomial.IsRoot.def, eval_mul, eval_sub, eval_X, eval_C]
    ring
  have hprod : 0 ≤ s.eval u * r.eval u :=
    eval_mul_eval_nonneg_of_prec_right hsr_prec hrr_prec hs_pos hr_pos hroot_right
  have hsq_pos : 0 < r.eval u * r.eval u := mul_self_pos.mpr hr_eval
  have hquot : 0 ≤ (s.eval u * r.eval u) / (r.eval u * r.eval u) :=
    div_nonneg hprod hsq_pos.le
  convert hquot using 1
  field_simp [hr_eval]

/-- Residual form of `kreinCoefficient_eval_div_nonneg`, matching the quotient
`s` produced from `f - c g` in the coefficient construction.  The scalar
multiple of `g` contributes one extra factor of `X - C u`, so it does not
change the quotient evaluation at `u`. -/
theorem kreinCoefficient_residual_eval_div_nonneg
    {f g q r s : ℝ[X]} {u c : ℝ}
    (hfg : Prec f g) (hfpos : HasPosLeadingCoeff f)
    (hgpos : HasPosLeadingCoeff g) (hu : g.IsRoot u)
    (hres : f - C c * g = (X - C u) ^ (g.rootMultiplicity u - 1) * s)
    (hfactor : g = (X - C u) * q)
    (hq : q = (X - C u) ^ (g.rootMultiplicity u - 1) * r)
    (hr0 : r ≠ 0) (hrs : r.Splits) (hr_eval : r.eval u ≠ 0) :
    0 ≤ s.eval u / r.eval u := by
  let m : ℕ := g.rootMultiplicity u
  let d : ℝ[X] := (X - C u) ^ (m - 1)
  rcases exists_precLeft_factor_of_right_isRoot hfg hu with ⟨t, hf_t, _, _, _⟩
  have hf_t_m : f = d * t := by simpa [d, m] using hf_t
  have hq_m : q = d * r := by simpa [d, m] using hq
  have hg_common : g = d * ((X - C u) * r) := by
    rw [hfactor, hq_m]
    dsimp [d]
    ring
  have hres_m : f - C c * g = d * s := by simpa [d, m] using hres
  have hd0 : d ≠ 0 := by
    dsimp [d]
    exact pow_ne_zero _ (X_sub_C_ne_zero u)
  have hs_eq : s = t - C c * ((X - C u) * r) := by
    apply mul_left_cancel₀ hd0
    rw [← hres_m, hf_t_m, hg_common]
    ring
  have hs_eval : s.eval u = t.eval u := by
    rw [hs_eq, eval_sub, eval_mul, eval_C, eval_mul, eval_sub, eval_X, eval_C]
    ring
  have hm : 1 ≤ m := by
    dsimp [m]
    exact Nat.succ_le_of_lt ((rootMultiplicity_pos hfg.2.1.1).2 hu)
  have hg_full_m : g = (X - C u) ^ m * r := by
    rw [hg_common]
    dsimp [d]
    nth_rw 2 [show m = m - 1 + 1 by exact (Nat.sub_add_cancel hm).symm]
    ring_nf
  have hg_full : g = (X - C u) ^ g.rootMultiplicity u * r := by simpa [m] using hg_full_m
  have hnonneg : 0 ≤ t.eval u / r.eval u :=
    kreinCoefficient_eval_div_nonneg hfg hfpos hgpos hu hf_t hg_full hr0 hrs
      hr_eval
  rwa [hs_eval]

/-- Single-root coefficient package with the sign conclusion included. -/
theorem exists_kreinCoefficientData_nonneg_of_right_isRoot {f g : ℝ[X]}
    (hfg : Prec f g) (hfpos : HasPosLeadingCoeff f)
    (hgpos : HasPosLeadingCoeff g) (hgs : g.Splits) (c : ℝ) {u : ℝ}
    (hu : g.IsRoot u) :
    ∃ a : ℝ, ∃ q : ℝ[X],
      0 ≤ a ∧
        g = (X - C u) * q ∧
        IsGWKreinSummand g q ∧
        (X - C u) ^ (g.rootMultiplicity u) ∣
          f - C c * g - C a * q := by
  rcases exists_kreinSummand_factor_of_isRoot hfg.2.1.1 hgs hu with
    ⟨q, r, hfactor, hq, _, hr_eval, _, _, hr0, hrs, hsummand⟩
  rcases exists_precResidual_factor_of_right_rootMultiplicity hfg u c with
    ⟨s, hres⟩
  refine ⟨s.eval u / r.eval u, q, ?_, hfactor, hsummand, ?_⟩
  · exact
      kreinCoefficient_residual_eval_div_nonneg hfg hfpos hgpos hu hres hfactor hq
        hr0 hrs hr_eval
  · exact kreinCoefficient_sub_dvd_rightRootMultiplicity hfg hu hres hq hr_eval

/-- Positive-degree Garloff--Wagner Lemma 7 package: if `f ≪ g` and both
polynomials have positive leading coefficient, then `f` is a nonnegative
weighted sum of `g` and the one-root-deleted Krein summands of `g`. -/
theorem exists_kreinSummandExpansion_nonneg_right_of_pos_natDegree {f g : ℝ[X]}
    (hfg : Prec f g) (hfpos : HasPosLeadingCoeff f)
    (hgpos : HasPosLeadingCoeff g) (hgdeg : 0 < g.natDegree) :
    ∃ l : List (ℝ × ℝ[X]),
      f = weightedSum l ∧
        (∀ ap ∈ l, 0 ≤ ap.1) ∧
        (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        ∃ ap ∈ l, 0 < ap.1 := by
  classical
  rcases exists_nonneg_C_mul_sub_natDegree_lt_of_le hfpos hgpos hgdeg
      hfg.natDegree_le with ⟨c, hc_nonneg, hcdeg⟩
  let roots : List ℝ := g.roots.toFinset.toList
  have hroots_nodup : roots.Nodup := Finset.nodup_toList _
  have hroot : ∀ u ∈ roots, g.IsRoot u := by
    intro u hu
    exact (mem_roots hfg.2.1.1).mp
      (Multiset.mem_toFinset.mp (Finset.mem_toList.mp hu))
  have hdata : ∀ u ∈ roots, ∃ a : ℝ, ∃ q : ℝ[X],
      0 ≤ a ∧
        g = (X - C u) * q ∧
        IsGWKreinSummand g q ∧
        (X - C u) ^ (g.rootMultiplicity u) ∣
          f - C c * g - C a * q := by
    intro u hu
    exact exists_kreinCoefficientData_nonneg_of_right_isRoot hfg hfpos hgpos
      hfg.2.1.2 c (hroot u hu)
  choose a q ha hfactor hsummand hgain using hdata
  let a' : ℝ → ℝ := fun u => if hu : u ∈ roots then a u hu else 0
  let q' : ℝ → ℝ[X] := fun u => if hu : u ∈ roots then q u hu else 0
  let tail : List (ℝ × ℝ[X]) := roots.map fun u => (a' u, q' u)
  let l : List (ℝ × ℝ[X]) := (c, g) :: tail
  have hfactor' : ∀ u ∈ roots, g = (X - C u) * q' u := by
    intro u hu
    simp [q', hu, hfactor u hu]
  have hgain' : ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣ f - C c * g - C (a' u) * q' u := by
    intro u hu
    simp [a', q', hu, hgain u hu]
  have hdiv_roots : ∀ u ∈ roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣
        f - C c * g - weightedSum tail := by
    simpa [tail] using
      fullRootMultiplicity_dvd_sub_weightedSum_rootDeleted
        hfg.2.1.1 roots hroots_nodup a' q' hfactor' hgain'
  have hdiv_all_roots : ∀ u ∈ g.roots,
      (X - C u) ^ (g.rootMultiplicity u) ∣
        f - C c * g - weightedSum tail := by
    intro u hu
    exact hdiv_roots u (by
      rw [Finset.mem_toList, Multiset.mem_toFinset]
      exact hu)
  have hdiv : g ∣ f - C c * g - weightedSum tail :=
    dvd_of_roots_fullRootMultiplicity_dvd hfg.2.1.1 hfg.2.1.2 hdiv_all_roots
  have htail_deg : (weightedSum tail).natDegree < g.natDegree := by
    simpa [tail] using
      natDegree_weightedSum_deletedFactors_lt hfg.2.1.1 hgdeg roots a' q' hfactor'
  have hresdeg : (f - C c * g - weightedSum tail).natDegree < g.natDegree :=
    natDegree_sub_lt_of_both_lt hgdeg hcdeg htail_deg
  have hzero : f - C c * g - weightedSum tail = 0 :=
    eq_zero_of_dvd_of_natDegree_lt hfg.2.1.1 hdiv hresdeg
  have hf : f = weightedSum l := by
    have hsub : f - C c * g = weightedSum tail := sub_eq_zero.mp hzero
    change f = weightedSum ((c, g) :: tail)
    rw [weightedSum_cons, ← hsub]
    ring
  have hnonneg : ∀ ap ∈ l, 0 ≤ ap.1 := by
    intro ap hap
    change ap ∈ (c, g) :: tail at hap
    rcases List.mem_cons.mp hap with hhead | htail_mem
    · rcases hhead with rfl
      exact hc_nonneg
    · change ap ∈ roots.map (fun u => (a' u, q' u)) at htail_mem
      rcases List.mem_map.mp htail_mem with ⟨u, hu, rfl⟩
      simp [a', hu, ha u hu]
  have hsummand_all : ∀ ap ∈ l, IsGWKreinSummand g ap.2 := by
    intro ap hap
    change ap ∈ (c, g) :: tail at hap
    rcases List.mem_cons.mp hap with hhead | htail_mem
    · rcases hhead with rfl
      exact Or.inl rfl
    · change ap ∈ roots.map (fun u => (a' u, q' u)) at htail_mem
      rcases List.mem_map.mp htail_mem with ⟨u, hu, rfl⟩
      simp [q', hu, hsummand u hu]
  have hex : ∃ ap ∈ l, 0 < ap.1 := by
    by_contra hnot
    have hzero_weights : ∀ ap ∈ l, ap.1 = 0 := by
      intro ap hap
      exact le_antisymm
        (not_lt.mp fun hpos => hnot ⟨ap, hap, hpos⟩)
        (hnonneg ap hap)
    have hws0 : weightedSum l = 0 :=
      weightedSum_eq_zero_of_forall_coeff_zero l hzero_weights
    exact hfg.1.1 (by rw [hf, hws0])
  exact ⟨l, hf, hnonneg, hsummand_all, hex⟩

/-- Constant-degree Garloff--Wagner Lemma 7 package.  If `g` is constant, then
`Prec f g` forces `f` to be constant as well, so `f` is a positive scalar
multiple of the Krein summand `g`. -/
theorem exists_kreinSummandExpansion_nonneg_right_of_natDegree_eq_zero {f g : ℝ[X]}
    (hfg : Prec f g) (hfpos : HasPosLeadingCoeff f)
    (hgpos : HasPosLeadingCoeff g) (hgdeg : g.natDegree = 0) :
    ∃ l : List (ℝ × ℝ[X]),
      f = weightedSum l ∧
        (∀ ap ∈ l, 0 ≤ ap.1) ∧
        (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        ∃ ap ∈ l, 0 < ap.1 := by
  have hfdeg : f.natDegree = 0 := by
    have hfg_le := hfg.natDegree_le
    lia
  let c : ℝ := f.leadingCoeff / g.leadingCoeff
  have hc_pos : 0 < c := by
    dsimp [c]
    exact div_pos hfpos hgpos
  have hfC : f = C f.leadingCoeff := by
    have hfC0 : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hfdeg
    have hlc : f.leadingCoeff = f.coeff 0 := by rw [leadingCoeff, hfdeg]
    simpa [hlc] using hfC0
  have hgC : g = C g.leadingCoeff := by
    have hgC0 : g = C (g.coeff 0) := eq_C_of_natDegree_eq_zero hgdeg
    have hlc : g.leadingCoeff = g.coeff 0 := by rw [leadingCoeff, hgdeg]
    simpa [hlc] using hgC0
  have hscalar : C c * g = f := by
    rw [hgC, hfC, ← C_mul]
    congr 1
    dsimp [c]
    field_simp [ne_of_gt hgpos]
  refine ⟨[(c, g)], ?_, ?_, ?_, ?_⟩
  · simpa [weightedSum_cons] using hscalar.symm
  · intro ap hap
    rcases List.mem_singleton.mp hap with rfl
    exact hc_pos.le
  · intro ap hap
    rcases List.mem_singleton.mp hap with rfl
    exact Or.inl rfl
  · exact ⟨(c, g), List.mem_singleton_self _, hc_pos⟩

/-- Normalizing a nonzero polynomial by its leading coefficient makes it
standard, without changing its roots. -/
lemma hasPosLeadingCoeff_C_inv_leadingCoeff_mul {p : ℝ[X]} (hp0 : p ≠ 0) :
    HasPosLeadingCoeff (C p.leadingCoeff⁻¹ * p) := by
  apply hasPosLeadingCoeff_of_monic
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  exact inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hp0)

/-- A Lemma 7/Krein expansion in root-deleted summands supplies the weighted
common-right hypotheses needed for the checked Theorem 11(c) package. -/
theorem gwJL_prec_of_kreinSummandExpansion
    {k : ℕ} {f g : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hg0 : g ≠ 0) (hgs : g.Splits) (hgpos : HasPosLeadingCoeff g)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hsummand : ∀ ap ∈ l, IsGWKreinSummand g ap.2)
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    Prec (gwJL k f) (gwJL k g) :=
  gwJL_prec_of_rightWeightedExpansion hf hnonneg
    (fun ap hap => (hsummand ap hap).gwJL_prec hg0 hgs)
    (fun ap hap => ((hsummand ap hap).hasPosLeadingCoeff hgpos).gwJL k)
    hex

/-- The trivial one-term Krein expansion of the right polynomial itself. -/
theorem kreinSummandExpansion_self (g : ℝ[X]) :
    ∃ l : List (ℝ × ℝ[X]),
      g = weightedSum l ∧
        (∀ ap ∈ l, 0 ≤ ap.1) ∧
        (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        ∃ ap ∈ l, 0 < ap.1 := by
  refine ⟨[(1, g)], ?_, ?_, ?_, ?_⟩
  · simp [weightedSum_cons]
  · intro ap hap
    rcases List.mem_singleton.mp hap with rfl
    norm_num
  · intro ap hap
    rcases List.mem_singleton.mp hap with rfl
    exact Or.inl rfl
  · exact ⟨(1, g), List.mem_singleton_self _, by norm_num⟩

/-- Any individual Krein summand gives a one-term nonnegative expansion. -/
theorem kreinSummandExpansion_of_summand {g q : ℝ[X]}
    (h : IsGWKreinSummand g q) :
    ∃ l : List (ℝ × ℝ[X]),
      q = weightedSum l ∧
        (∀ ap ∈ l, 0 ≤ ap.1) ∧
        (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        ∃ ap ∈ l, 0 < ap.1 := by
  refine ⟨[(1, q)], ?_, ?_, ?_, ?_⟩
  · simp [weightedSum_cons]
  · intro ap hap
    rcases List.mem_singleton.mp hap with rfl
    norm_num
  · intro ap hap
    rcases List.mem_singleton.mp hap with rfl
    exact h
  · exact ⟨(1, q), List.mem_singleton_self _, by norm_num⟩

/-- Package raw list data as a Krein summand expansion.  This is the shape the
eventual coefficient proof of Lemma 7 should hand back once the coefficients
and deleted-root factors have been constructed. -/
theorem kreinSummandExpansion_of_weightedSum {f g : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hf : f = weightedSum l)
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hsummand : ∀ ap ∈ l, IsGWKreinSummand g ap.2)
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    ∃ l : List (ℝ × ℝ[X]),
      f = weightedSum l ∧
        (∀ ap ∈ l, 0 ≤ ap.1) ∧
        (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        ∃ ap ∈ l, 0 < ap.1 :=
  ⟨l, hf, hnonneg, hsummand, hex⟩

/-- Lemma 7-facing interface for Theorem 11(c).  After normalizing the right
polynomial to be standard, the left polynomial should expand as a nonnegative
weighted sum of the right polynomial and its one-root-deleted factors. -/
def gwTheorem11PrecKreinSummandExpansionStatement : Prop :=
  ∀ {f g : ℝ[X]}, Prec f g → HasPosLeadingCoeff f → HasPosLeadingCoeff g →
    ∃ l : List (ℝ × ℝ[X]),
      f = weightedSum l ∧
        (∀ ap ∈ l, 0 ≤ ap.1) ∧
        (∀ ap ∈ l, IsGWKreinSummand g ap.2) ∧
        ∃ ap ∈ l, 0 < ap.1

theorem gwTheorem11Prec_of_kreinSummandExpansion
    (h : gwTheorem11PrecKreinSummandExpansionStatement) :
    gwTheorem11PrecStatement := by
  intro f g hfg k
  let sf : ℝ := f.leadingCoeff⁻¹
  let sg : ℝ := g.leadingCoeff⁻¹
  have hf0 : f ≠ 0 := hfg.1.1
  have hg0 : g ≠ 0 := hfg.2.1.1
  have hsf : sf ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hf0)
  have hsg : sg ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hg0)
  have hfg_scaled : Prec (C sf * f) (C sg * g) :=
    prec_C_mul_right (prec_C_mul_left hfg hsf) hsg
  have hsf_pos : HasPosLeadingCoeff (C sf * f) :=
    hasPosLeadingCoeff_C_inv_leadingCoeff_mul hf0
  have hsg_pos : HasPosLeadingCoeff (C sg * g) :=
    hasPosLeadingCoeff_C_inv_leadingCoeff_mul hg0
  rcases h (f := C sf * f) (g := C sg * g) hfg_scaled hsf_pos hsg_pos with
    ⟨l, hf, hnonneg, hsummand, hex⟩
  have hscaled :
      Prec (gwJL k (C sf * f)) (gwJL k (C sg * g)) :=
    gwJL_prec_of_kreinSummandExpansion hf hfg_scaled.2.1.1 hfg_scaled.2.1.2
      hsg_pos hnonneg hsummand hex
  have hscaled' : Prec (C sf * gwJL k f) (C sg * gwJL k g) := by simpa [gwJL_C_mul] using hscaled
  have hleft :
      Prec (gwJL k f) (C sg * gwJL k g) := by
    have htmp := prec_C_mul_left hscaled' (inv_ne_zero hsf)
    have hscale : C sf⁻¹ * (C sf * gwJL k f) = gwJL k f := by
      rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hsf, C_1, one_mul]
    simpa [hscale] using htmp
  have hright := prec_C_mul_right hleft (inv_ne_zero hsg)
  have hscale : C sg⁻¹ * (C sg * gwJL k g) = gwJL k g := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hsg, C_1, one_mul]
  simpa [hscale] using hright

/-- Garloff--Wagner, Theorem 11(c), reduced to the checked Krein expansion
package. -/
theorem gwTheorem11PrecKreinSummandExpansion :
    gwTheorem11PrecKreinSummandExpansionStatement := by
  intro f g hfg hfpos hgpos
  by_cases hgdeg0 : g.natDegree = 0
  · exact exists_kreinSummandExpansion_nonneg_right_of_natDegree_eq_zero hfg hfpos
      hgpos hgdeg0
  · exact exists_kreinSummandExpansion_nonneg_right_of_pos_natDegree hfg hfpos
      hgpos (Nat.pos_of_ne_zero hgdeg0)

/-- Garloff--Wagner, Theorem 11(c), in the local `Prec` orientation. -/
theorem gwTheorem11Prec :
    gwTheorem11PrecStatement :=
  gwTheorem11Prec_of_kreinSummandExpansion gwTheorem11PrecKreinSummandExpansion

end RealRooted
