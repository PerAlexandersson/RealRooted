import RealRooted.WeightedSum
import RealRooted.MaWang
import RealRooted.ObreschkoffContinuity
import RealRooted.AissenSchoenbergWhitney

/-!
# Positive-combination real-rootedness

This file develops `PosComboRealRooted`, family and coprimeness lemmas, the
common-left interleaver forward direction, and convex-combination wrapper
theorems.
-/

open Polynomial

noncomputable section

namespace RealRooted

private lemma natDegree_eq_or_succ_of_prec {f g : ℝ[X]} (h : Prec f g) :
    g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 := by
  rcases h with ⟨hf, hg, ss, rs, _hss, _hrs, hss_eq, hrs_eq, hshape⟩
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩
  · right
    lia
  · left
    lia

private lemma exists_root_upper_bound (p : ℝ[X]) :
    ∃ c, ∀ r ∈ p.roots, r ≤ c := by
  let rs := p.roots.sort (· ≤ ·)
  by_cases hrs_nil : rs = []
  · refine ⟨0, ?_⟩
    intro r hr
    have hroots_nil : p.roots = 0 := by
      simpa [rs, hrs_nil] using (Multiset.sort_eq (s := p.roots) (r := (· ≤ ·))).symm
    have : False := by
      simp [hroots_nil] at hr
    exact this.elim
  · refine ⟨rs.getLast hrs_nil, ?_⟩
    have hrs_sorted : rs.Pairwise (· ≤ ·) := by
      simp [rs]
    intro r hr
    have hr_mem : r ∈ rs := by
      apply Multiset.mem_coe.mp
      simpa [rs] using hr
    exact hrs_sorted.rel_getLast hr_mem

private lemma exists_common_root_upper_bound (h : ℝ[X]) (l : List (ℝ × ℝ[X])) :
    ∃ c, (∀ r ∈ h.roots, r ≤ c) ∧ ∀ ap ∈ l, ∀ r ∈ ap.2.roots, r ≤ c := by
  induction l with
  | nil =>
      rcases exists_root_upper_bound h with ⟨c, hc⟩
      exact ⟨c, hc, by intro ap hap; simp at hap⟩
  | cons ap l ih =>
      rcases ih with ⟨c₁, hc₁, hl₁⟩
      rcases exists_root_upper_bound ap.2 with ⟨c₂, hc₂⟩
      refine ⟨max c₁ c₂, ?_, ?_⟩
      · intro r hr
        exact le_trans (hc₁ r hr) (le_max_left _ _)
      · intro ap' hap' r hr
        rcases List.mem_cons.mp hap' with rfl | hap'
        · exact le_trans (hc₂ r hr) (le_max_right _ _)
        · exact le_trans (hl₁ ap' hap' r hr) (le_max_left _ _)

lemma prec_sameDegree_to_prec_mul_X_sub_C_of_roots_le {f g : ℝ[X]} (r : ℝ)
    (h : Prec f g)
    (hdeg : f.natDegree = g.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r) :
    Prec g ((X - C r) * f) := by
  set f' := f.comp (X + C r)
  set g' := g.comp (X + C r)
  have hf' : (f' ≠ 0 ∧
    f'.Splits) := by simpa [f'] using isRealRooted_comp_X_add_C h.1 r
  have hg' : (g' ≠ 0 ∧
    g'.Splits) := by simpa [g'] using isRealRooted_comp_X_add_C h.2.1 r
  have hf'_pos : HasPosLeadingCoeff f' := by
    unfold HasPosLeadingCoeff f'
    rw [leadingCoeff_comp (by simp), leadingCoeff_X_add_C, one_pow, mul_one]
    exact hf_pos
  have hg'_pos : HasPosLeadingCoeff g' := by
    unfold HasPosLeadingCoeff g'
    rw [leadingCoeff_comp (by simp), leadingCoeff_X_add_C, one_pow, mul_one]
    exact hg_pos
  have hf'_nonpos : ∀ s ∈ f'.roots, s ≤ 0 := by
    intro s hs
    simp only [f', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    linarith [hf_le t ht]
  have hg'_nonpos : ∀ s ∈ g'.roots, s ≤ 0 := by
    intro s hs
    simp only [g', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    linarith [hg_le t ht]
  have hdeg' : f'.natDegree = g'.natDegree := by
    simpa [f', g', natDegree_comp] using hdeg
  have hfg' : Prec f' g' := by
    simpa [f', g'] using (prec_comp_X_add_C_iff (f := f) (g := g) r).2 h
  have hgxf' : Prec g' (X * f') :=
    prec_sameDegree_to_prec_mul_X_of_roots_nonpos hfg' hdeg' hf'_nonpos hg'_nonpos
  have htranslated : Prec g' (((X - C r) * f).comp (X + C r)) := by
    simpa [f', g', mul_comp, sub_comp, X_comp, C_comp, sub_eq_add_neg,
      comp_assoc, add_assoc, add_left_comm, add_comm] using hgxf'
  exact (prec_comp_X_add_C_iff (f := g) (g := (X - C r) * f) r).1 htranslated

lemma prec_of_prec_mul_X_sub_C_of_sameDegree_of_roots_le {f g : ℝ[X]} (r : ℝ)
    (h : Prec g ((X - C r) * f))
    (hdeg : f.natDegree = g.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r) :
    Prec f g := by
  set f' := f.comp (X + C r)
  set g' := g.comp (X + C r)
  have hXf : (((X - C r) * f) ≠ 0 ∧ ((X - C r) * f).Splits) := h.2.1
  have hf0 : f ≠ 0 := right_ne_zero_of_mul hXf.1
  have hf : (f ≠ 0 ∧ f.Splits) := by
    apply isRealRooted_of_dvd hXf hf0
    exact ⟨X - C r, by rw [mul_comm]⟩
  have hf' : (f' ≠ 0 ∧
    f'.Splits) := by simpa [f'] using isRealRooted_comp_X_add_C hf r
  have hg' : (g' ≠ 0 ∧
    g'.Splits) := by simpa [g'] using isRealRooted_comp_X_add_C h.1 r
  have hf'_pos : HasPosLeadingCoeff f' := by
    unfold HasPosLeadingCoeff f'
    rw [leadingCoeff_comp (by simp), leadingCoeff_X_add_C, one_pow, mul_one]
    exact hf_pos
  have hg'_pos : HasPosLeadingCoeff g' := by
    unfold HasPosLeadingCoeff g'
    rw [leadingCoeff_comp (by simp), leadingCoeff_X_add_C, one_pow, mul_one]
    exact hg_pos
  have hf'_nonpos : ∀ s ∈ f'.roots, s ≤ 0 := by
    intro s hs
    simp only [f', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    linarith [hf_le t ht]
  have hg'_nonpos : ∀ s ∈ g'.roots, s ≤ 0 := by
    intro s hs
    simp only [g', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    linarith [hg_le t ht]
  have hdeg' : f'.natDegree = g'.natDegree := by
    simpa [f', g', natDegree_comp] using hdeg
  have hgf' : Prec g' (((X - C r) * f).comp (X + C r)) := by
    simpa [g'] using (prec_comp_X_add_C_iff (f := g) (g := (X - C r) * f) r).2 h
  have hgxf' : Prec g' (X * f') := by
    simpa [f', g', mul_comp, sub_comp, X_comp, C_comp, sub_eq_add_neg,
      comp_assoc, add_assoc, add_left_comm, add_comm] using hgf'
  have hfg' : Prec f' g' :=
    prec_of_prec_mul_X_sameDegree_of_roots_nonpos hgxf' hdeg' hf'_nonpos hg'_nonpos
  exact (prec_comp_X_add_C_iff (f := f) (g := g) r).1 (by simpa [f', g'] using hfg')

/-- Borcea--Brändén left-cone lemma, weighted form:
if every polynomial in the family is interlaced on the left by the same `h`,
all family members have positive leading coefficient, and the weights are
nonnegative with at least one positive weight, then the weighted sum is also
interlaced on the left by `h`. -/
  theorem prec_weightedSum_left_of_common_left
    (l : List (ℝ × ℝ[X])) (h : ℝ[X])
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hprec : ∀ ap ∈ l, Prec h ap.2)
    (hpos : HasPosLeadingCoeff h)
    (hpoly_pos : ∀ ap ∈ l, HasPosLeadingCoeff ap.2)
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    Prec h (weightedSum l) := by
  rcases hex with ⟨ap0, hap0, ha0_pos⟩
  have hex0 : ∃ ap ∈ l, 0 < ap.1 := ⟨ap0, hap0, ha0_pos⟩
  have hh : (h ≠ 0 ∧ h.Splits) := (hprec ap0 hap0).1
  rcases exists_common_root_upper_bound h l with ⟨r, hh_le, hl_le⟩
  let H := (X - C r) * h
  have hH_pos : HasPosLeadingCoeff H := hasPosLeadingCoeff_X_sub_C_mul hpos
  have hprec_right : ∀ ap ∈ l, Prec ap.2 H := by
    intro ap hap
    have hp := hprec ap hap
    have hp_pos := hpoly_pos ap hap
    have hp_le : ∀ s ∈ ap.2.roots, s ≤ r := hl_le ap hap
    rcases natDegree_eq_or_succ_of_prec hp with hdeg | hdeg
    · exact prec_sameDegree_to_prec_mul_X_sub_C_of_roots_le r hp hdeg.symm hpos hp_pos hh_le hp_le
    · exact
        (prec_iff_prec_mul_X_sub_C_of_roots_le r
          hp.1 hp.2.1 hpos hp_pos hh_le hp_le hdeg.symm).mp hp
  have hweighted_right : Prec (weightedSum l) H := by
    apply prec_weightedSum_right l H hnonneg hprec_right hpoly_pos hex0
  have hweighted_pos : HasPosLeadingCoeff (weightedSum l) :=
    hasPosLeadingCoeff_weightedSum l hnonneg hpoly_pos hex0
  have hH_deg : H.natDegree = h.natDegree + 1 := by
    rw [show H = (X - C r) * h by rfl, natDegree_mul (X_sub_C_ne_zero r) hh.1, natDegree_X_sub_C]
    lia
  have hH_le : ∀ s ∈ H.roots, s ≤ r := roots_le_X_sub_C_mul hh hh_le
  have hweighted_le : ∀ s ∈ (weightedSum l).roots, s ≤ r :=
    roots_le_of_prec_right hweighted_right hH_le
  rcases natDegree_eq_or_succ_of_prec hweighted_right with hcase | hcase
  · have hdeg : h.natDegree + 1 = (weightedSum l).natDegree := by
      rw [← hH_deg]
      exact hcase
    exact
      (prec_iff_prec_mul_X_sub_C_of_roots_le r hh hweighted_right.1 hpos hweighted_pos
        hh_le hweighted_le hdeg).mpr hweighted_right
  · have hdeg : h.natDegree = (weightedSum l).natDegree := by
      lia
    exact
      prec_of_prec_mul_X_sub_C_of_sameDegree_of_roots_le r hweighted_right hdeg
        hpos hweighted_pos hh_le hweighted_le

/-- Unweighted left-cone corollary. -/
theorem prec_sum_left_of_common_left
    (l : List ℝ[X]) (h : ℝ[X])
    (hprec : ∀ p ∈ l, Prec h p)
    (hpos : HasPosLeadingCoeff h)
    (hpoly_pos : ∀ p ∈ l, HasPosLeadingCoeff p)
    (hne : l ≠ []) :
    Prec h l.sum := by
  rw [← weightedSum_map_one l]
  apply prec_weightedSum_left_of_common_left (l.map (fun p => ((1 : ℝ), p))) h
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨p, hp, rfl⟩
    norm_num
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨p, hp, rfl⟩
    exact hprec p hp
  · exact hpos
  · intro ap hap
    rcases List.mem_map.mp hap with ⟨p, hp, rfl⟩
    exact hpoly_pos p hp
  · cases l with
    | nil =>
        contradiction
    | cons p ps =>
        refine ⟨((1 : ℝ), p), by simp, by norm_num⟩

/-- Sign-normalized left-cone theorem: if all summands are interlaced on the
left by the same nonzero real-rooted polynomial `h`, and the summands have
positive leading coefficient, then their sum is interlaced on the left by `h`
without needing to assume the sign of `h.leadingCoeff` in advance. -/
theorem prec_sum_left_of_common_left_signed
    (l : List ℝ[X]) (h : ℝ[X])
    (hprec : ∀ p ∈ l, Prec h p)
    (hpoly_pos : ∀ p ∈ l, HasPosLeadingCoeff p)
    (hne : l ≠ []) :
    Prec h l.sum := by
  rcases List.exists_mem_of_ne_nil l hne with ⟨p0, hp0⟩
  have hh : (h ≠ 0 ∧ h.Splits) := (hprec p0 hp0).1
  have hlc_ne : h.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hh.1
  rcases lt_or_gt_of_ne hlc_ne with hneg | hpos
  · let h' : ℝ[X] := C (-1 : ℝ) * h
    have hprec' : ∀ p ∈ l, Prec h' p := by
      intro p hp
      exact prec_C_mul_left (hprec p hp) (by norm_num)
    have h'_pos : HasPosLeadingCoeff h' := by
      unfold h' HasPosLeadingCoeff
      rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (by norm_num : (-1 : ℝ) ≠ 0)) h]
      linarith
    have hsum' : Prec h' l.sum :=
      prec_sum_left_of_common_left l h' hprec' h'_pos hpoly_pos hne
    have hback : Prec (C (-1 : ℝ) * h') l.sum :=
      prec_C_mul_left hsum' (by norm_num)
    simpa [h'] using hback
  · exact prec_sum_left_of_common_left l h hprec hpos hpoly_pos hne

@[simp] lemma sum_filter_ne_zero (l : List ℝ[X]) :
    (l.filter (· ≠ 0)).sum = l.sum := by
  induction l with
  | nil =>
      simp
  | cons p l ih =>
      by_cases hp : p = 0
      · simpa [hp] using ih
      · simpa [hp] using congrArg (fun q => p + q) ih

/-- Borcea--Brändén left-cone lemma in the nonnegative-coefficients
specialization, zero-aware form on lists: if `h ≪₀ f_i` for every summand and
each `f_i` has nonnegative coefficients, then `h ≪₀ ∑ f_i`. -/
theorem prec0_sum_left_of_common_left_of_nonneg
    (l : List ℝ[X]) (h : ℝ[X])
    (hprec : ∀ p ∈ l, Prec0 h p)
    (hnn : ∀ p ∈ l, HasNonnegCoeffs p) :
    Prec0 h l.sum := by
  by_cases hh0 : h = 0
  · simpa [hh0] using prec0_zero_left l.sum
  let l' := l.filter (· ≠ 0)
  have hsum : l'.sum = l.sum := by
    simpa [l'] using sum_filter_ne_zero l
  by_cases hl' : l' = []
  · have hsum0 : l.sum = 0 := by
      rw [← hsum, hl']
      simp
    simpa [hsum0] using prec0_zero_right h
  · have hprec' : ∀ p ∈ l', Prec h p := by
      intro p hp
      have hp_mem : p ∈ l := (List.mem_of_mem_filter hp)
      have hp_ne : p ≠ 0 := by
        simpa using (List.mem_filter.mp hp).2
      rcases hprec p hp_mem with hh | hp0 | hpf
      · contradiction
      · exact (hp_ne hp0).elim
      · exact hpf
    have hpos' : ∀ p ∈ l', HasPosLeadingCoeff p := by
      intro p hp
      have hp_mem : p ∈ l := List.mem_of_mem_filter hp
      have hp_ne : p ≠ 0 := by
        simpa using (List.mem_filter.mp hp).2
      have hp_rr : (p ≠ 0 ∧ p.Splits) := (hprec' p hp).2.1
      exact (hnn p hp_mem).pos_leadingCoeff hp_ne
    have hstrict : Prec h l'.sum :=
      prec_sum_left_of_common_left_signed l' h hprec' hpos' hl'
    exact Or.inr <| Or.inr <| by simpa [hsum] using hstrict

/-- Right cone for `Prec0` over finite sums of nonnegative-coefficient polynomials. -/
lemma prec0_finsetSum_right_of_nonneg {ι : Type}
    (s : Finset ι) (f : ι → ℝ[X]) (h : ℝ[X])
    (hprec : ∀ i ∈ s, Prec0 (f i) h)
    (hnn : ∀ i ∈ s, HasNonnegCoeffs (f i)) :
    Prec0 (s.sum f) h := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using prec0_zero_left h
  | @insert a s ha ih =>
      have hprec_a : Prec0 (f a) h := hprec a (by simp)
      have hprec_s : ∀ i ∈ s, Prec0 (f i) h := by
        intro i hi
        exact hprec i (by simp [hi])
      have hnn_a : HasNonnegCoeffs (f a) := hnn a (by simp)
      have hnn_s : ∀ i ∈ s, HasNonnegCoeffs (f i) := by
        intro i hi
        exact hnn i (by simp [hi])
      have ih' : Prec0 (s.sum f) h := ih hprec_s hnn_s
      by_cases hfa0 : f a = 0
      · simpa [Finset.sum_insert, ha, hfa0] using ih'
      by_cases hs0 : s.sum f = 0
      · simpa [Finset.sum_insert, ha, hs0] using hprec_a
      by_cases hh0 : h = 0
      · simpa [Finset.sum_insert, ha, hh0] using prec0_zero_right ((insert a s).sum f)
      rcases hprec_a with _ | hh0' | hprec_a_strict
      · contradiction
      · exact (hh0 hh0').elim
      rcases ih' with _ | hh0' | hprec_s_strict
      · contradiction
      · exact (hh0 hh0').elim
      have hs_pos : HasPosLeadingCoeff (s.sum f) :=
        (hasNonnegCoeffs_finsetSum s f hnn_s).pos_leadingCoeff hs0
      have hfa_pos : HasPosLeadingCoeff (f a) := hnn_a.pos_leadingCoeff hfa0
      have hsum_strict : Prec (f a + s.sum f) h :=
        prec_add_of_prec_right_of_posLeadingCoeff
          hprec_a_strict hprec_s_strict hfa_pos hs_pos
      simpa [Finset.sum_insert, ha] using hsum_strict.toPrec0

/-- Left cone for `Prec0` over finite sums of nonnegative-coefficient polynomials. -/
lemma prec0_finsetSum_left_of_nonneg {ι : Type}
    (h : ℝ[X]) (s : Finset ι) (f : ι → ℝ[X])
    (hprec : ∀ i ∈ s, Prec0 h (f i))
    (hnn : ∀ i ∈ s, HasNonnegCoeffs (f i)) :
    Prec0 h (s.sum f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using prec0_zero_right h
  | @insert a s ha ih =>
      have hprec_s : ∀ i ∈ s, Prec0 h (f i) := by
        intro i hi
        exact hprec i (by simp [hi])
      have hnn_s : ∀ i ∈ s, HasNonnegCoeffs (f i) := by
        intro i hi
        exact hnn i (by simp [hi])
      have ih' : Prec0 h (s.sum f) := ih hprec_s hnn_s
      have hpair : Prec0 h ([f a, s.sum f].sum) := by
        apply prec0_sum_left_of_common_left_of_nonneg
        · intro p hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · exact hprec a (by simp)
          · exact ih'
        · intro p hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · exact hnn a (by simp)
          · exact hasNonnegCoeffs_finsetSum s f hnn_s
      simpa [Finset.sum_insert, ha] using hpair

/-- Same-degree shift on the left: if `f ≪ g`, both have positive leading
coefficient, and all roots lie at most `r`, then `g ≪ g + (X - C r) * f`. -/
theorem prec_sameDegree_shift_left_of_roots_le
    (r : ℝ) {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r) :
    Prec g (g + (X - C r) * f) := by
  let t : ℝ[X] := (X - C r) * f
  have hgt : Prec g t := by
    simpa [t] using
      prec_sameDegree_to_prec_mul_X_sub_C_of_roots_le
        (r := r) hfg hdeg hf_pos hg_pos hf_le hg_le
  have ht_pos : HasPosLeadingCoeff t := hasPosLeadingCoeff_X_sub_C_mul hf_pos
  have hsum : Prec g ([g, t].sum) := by
    apply prec_sum_left_of_common_left_signed
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact prec_refl hfg.2.1
      · exact hgt
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hg_pos
      · exact ht_pos
    · simp
  simpa [t] using hsum

/-- If `f ⊳ g` with positive leading coefficients and non-negative `λ, μ`,
    not both zero, then `λf + μg` interlaces `g` from the left:
    `Prec (λf + μg) g`. -/
theorem prec_nonneg_combo_right {f g : ℝ[X]}
    (hfg : Prec f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a ∨ 0 < b) :
    Prec (C a * f + C b * g) g := by
  have hweighted : Prec (weightedSum [(a, f), (b, g)]) g := by
    apply prec_weightedSum_right [(a, f), (b, g)] g
    · intro ap hap
      rcases List.mem_cons.mp hap with h | h
      · cases h
        exact ha
      · rcases List.mem_cons.mp h with h | h
        · cases h
          exact hb
        · simp at h
    · intro ap hap
      rcases List.mem_cons.mp hap with h | h
      · cases h
        exact hfg
      · rcases List.mem_cons.mp h with h | h
        · cases h
          exact prec_refl hfg.2.1
        · simp at h
    · intro ap hap
      rcases List.mem_cons.mp hap with h | h
      · cases h
        exact hf_pos
      · rcases List.mem_cons.mp h with h | h
        · cases h
          exact hg_pos
        · simp at h
    · rcases hab with hab | hab
      · exact ⟨(a, f), by simp, hab⟩
      · exact ⟨(b, g), by simp, hab⟩
  simpa [weightedSum, weightedSum_cons, add_assoc] using hweighted

/-- Forward Obreschkoff direction: if `f ⊳ g` with positive leading coefficients,
    then every nontrivial nonnegative linear combination `a f + b g` is real-rooted. -/
theorem isRealRooted_nonneg_combo_of_prec {f g : ℝ[X]}
    (hfg : Prec f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a ∨ 0 < b) :
    ((C a * f + C b * g) ≠ 0 ∧ (C a * f + C b * g).Splits) :=
  (prec_nonneg_combo_right hfg hf_pos hg_pos ha hb hab).1

/-- Forward Obreschkoff direction, positive-coefficient special case:
    if `f ⊳ g`, then `a f + b g` is real-rooted for all `a, b > 0`. -/
theorem isRealRooted_pos_combo_of_prec {f g : ℝ[X]}
    (hfg : Prec f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((C a * f + C b * g) ≠ 0 ∧ (C a * f + C b * g).Splits) :=
  isRealRooted_nonneg_combo_of_prec hfg hf_pos hg_pos ha.le hb.le (Or.inl ha)

/-- A packaging of the positive-combination hypothesis that appears in the
restricted Obreschkoff converse: every strictly positive linear combination of
`f` and `g` is real-rooted. -/
def PosComboRealRooted (f g : ℝ[X]) : Prop :=
  ∀ {lam μ : ℝ}, 0 < lam → 0 < μ → ((C lam * f + C μ * g) ≠ 0 ∧
    (C lam * f + C μ * g).Splits)

namespace PosComboRealRooted

private lemma toPosComboHyp {f g : ℝ[X]} (hfg : PosComboRealRooted f g) :
    RealRooted.PosComboHyp f g := by
  intro lam μ hlam hμ
  exact hfg hlam hμ

lemma comm {f g : ℝ[X]} (h : PosComboRealRooted f g) :
    PosComboRealRooted g f := by
  intro lam μ hlam hμ
  simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using h hμ hlam

lemma isRealRooted_add {f g : ℝ[X]} (h : PosComboRealRooted f g) :
    ((f + g) ≠ 0 ∧ (f + g).Splits) := by
  simpa using h zero_lt_one zero_lt_one

lemma isRealRooted_add_right {f g : ℝ[X]} (h : PosComboRealRooted f g)
    {μ : ℝ} (hμ : 0 < μ) :
    ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits) := by
  simpa [one_mul, add_comm] using h zero_lt_one hμ

lemma isRealRooted_add_left {f g : ℝ[X]} (h : PosComboRealRooted f g)
    {lam : ℝ} (hlam : 0 < lam) :
    ((C lam * f + g) ≠ 0 ∧ (C lam * f + g).Splits) := by
  simpa [one_mul] using h hlam zero_lt_one

lemma of_prec {f g : ℝ[X]} (hfg : Prec f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    PosComboRealRooted f g := by
  intro lam μ hlam hμ
  exact isRealRooted_pos_combo_of_prec hfg hf_pos hg_pos hlam hμ

lemma iff_add_right {f g : ℝ[X]} :
    PosComboRealRooted f g ↔ ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧
      (f + C μ * g).Splits) := by
  constructor
  · intro h μ hμ
    simpa [one_mul, add_comm] using h (lam := 1) (μ := μ) zero_lt_one hμ
  · intro h lam μ hlam hμ
    have hbase : ((f + C (μ / lam) * g) ≠ 0 ∧
      (f + C (μ / lam) * g).Splits) := h (μ := μ / lam) (by positivity)
    have hscaled : ((C lam * (f + C (μ / lam) * g)) ≠ 0 ∧
      (C lam * (f + C (μ / lam) * g)).Splits) :=
      isRealRooted_C_mul hbase hlam.ne'
    have hEq : C lam * (f + C (μ / lam) * g) = C lam * f + C μ * g := by
      rw [mul_add]
      congr 1
      calc
        C lam * (C (μ / lam) * g) = (C lam * C (μ / lam)) * g := by rw [mul_assoc]
        _ = C (lam * (μ / lam)) * g := by rw [C_mul]
        _ = C μ * g := by
          congr 1
          field_simp [hlam.ne']
    simpa [hEq] using hscaled

lemma iff_add_left {f g : ℝ[X]} :
    PosComboRealRooted f g ↔ ∀ {lam : ℝ}, 0 < lam → ((C lam * f + g) ≠ 0 ∧
      (C lam * f + g).Splits) := by
  constructor
  · intro h lam hlam
    simpa [one_mul] using h (lam := lam) (μ := 1) hlam zero_lt_one
  · intro h lam μ hlam hμ
    have hbase : ((C (lam / μ) * f + g) ≠ 0 ∧
      (C (lam / μ) * f + g).Splits) := h (lam := lam / μ) (by positivity)
    have hscaled : ((C μ * (C (lam / μ) * f + g)) ≠ 0 ∧
      (C μ * (C (lam / μ) * f + g)).Splits) :=
      isRealRooted_C_mul hbase hμ.ne'
    have hEq : C μ * (C (lam / μ) * f + g) = C lam * f + C μ * g := by
      rw [mul_add]
      have hleft : C μ * (C (lam / μ) * f) = C lam * f := by
        calc
          C μ * (C (lam / μ) * f) = (C μ * C (lam / μ)) * f := by rw [mul_assoc]
          _ = C (μ * (lam / μ)) * f := by rw [C_mul]
          _ = C lam * f := by
            congr 1
            field_simp [hμ.ne']
      simp [hleft]
    simpa [hEq] using hscaled

lemma of_add_right {f g : ℝ[X]}
    (h : ∀ {μ : ℝ}, 0 < μ → ((f + C μ * g) ≠ 0 ∧
      (f + C μ * g).Splits)) :
    PosComboRealRooted f g :=
  (iff_add_right (f := f) (g := g)).2 h

lemma of_add_left {f g : ℝ[X]}
    (h : ∀ {lam : ℝ}, 0 < lam → ((C lam * f + g) ≠ 0 ∧
      (C lam * f + g).Splits)) :
    PosComboRealRooted f g :=
  (iff_add_left (f := f) (g := g)).2 h

/-- A common left interleaver for `f` and `g` forces every strictly positive
linear combination of `f` and `g` to be real-rooted. This is the forward
Wagner-2 direction behind the common-interleaver formulation of the
restricted Obreschkoff theorem. -/
lemma of_commonLeftInterleaver {f g h : ℝ[X]}
    (hhf : Prec h f) (hhg : Prec h g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    PosComboRealRooted f g := by
  intro lam μ hlam hμ
  have hhf' : Prec h (C lam * f) := prec_C_mul_right hhf hlam.ne'
  have hhg' : Prec h (C μ * g) := prec_C_mul_right hhg hμ.ne'
  have hlam_pos : HasPosLeadingCoeff (C lam * f) := hasPosLeadingCoeff_C_mul hlam hf_pos
  have hμ_pos : HasPosLeadingCoeff (C μ * g) := hasPosLeadingCoeff_C_mul hμ hg_pos
  have hprec :
      Prec h ([C lam * f, C μ * g].sum) := by
    apply prec_sum_left_of_common_left_signed
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hhf'
      · exact hhg'
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hlam_pos
      · exact hμ_pos
    · simp
  simpa using hprec.2.1

/-- Equal-degree positive-combination real-rootedness forces the left summand
to be real-rooted. -/
lemma isRealRooted_left_of_sameDegree {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) :
    (f ≠ 0 ∧ f.Splits) := by
  exact
    RealRooted.PosComboHyp.isRealRooted_left_of_posComboRealRooted_sameDegree
      (hfg := toPosComboHyp hfg) hf_pos hg_pos hdeg

/-- Equal-degree positive-combination real-rootedness forces the right summand
to be real-rooted. -/
lemma isRealRooted_right_of_sameDegree {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) :
    (g ≠ 0 ∧ g.Splits) := by
  exact
    RealRooted.PosComboHyp.isRealRooted_right_of_posComboRealRooted_sameDegree
      (hfg := toPosComboHyp hfg) hf_pos hg_pos hdeg

/-- Positive-combination real-rootedness gives real-rootedness on the closed
line segment once the two endpoints are known to be real-rooted. -/
lemma isRealRooted_closed_segment {f g : ℝ[X]} (hfg : PosComboRealRooted f g)
    (hf : f ≠ 0 ∧ f.Splits) (hg : g ≠ 0 ∧ g.Splits)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ((C (1 - β) * f + C β * g) ≠ 0 ∧
      (C (1 - β) * f + C β * g).Splits) := by
  rcases lt_or_eq_of_le hβ0 with hβ_pos | hβ_zero
  · rcases lt_or_eq_of_le hβ1 with hβ_lt | hβ_one
    · exact hfg (sub_pos.mpr hβ_lt) hβ_pos
    · subst hβ_one
      simpa using hg
  · subst hβ_zero
    simpa using hf

/-- Equal-degree positive-combination pairs have real-rooted closed segments.
This packages endpoint real-rootedness from the restricted Obreschkoff converse
already available for equal degrees. -/
lemma isRealRooted_closed_segment_of_sameDegree {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ((C (1 - β) * f + C β * g) ≠ 0 ∧
      (C (1 - β) * f + C β * g).Splits) :=
  hfg.isRealRooted_closed_segment
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg)
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg)
    hβ0 hβ1

/--
ASW/PF bridge for the positive-combination endpoint target.

If every nonnegative right pencil `f + z g` is nonzero and has a
Polya-frequency coefficient sequence, then ASW gives real-rootedness of
`f + z g`; rescaling by a positive constant gives real-rootedness of every
positive combination `a f + b g`.
-/
theorem of_aissenSchoenbergWhitney_right_pencil
    {f g : ℝ[X]}
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hne : ∀ {z : ℝ}, 0 ≤ z → f + C z * g ≠ 0)
    (hnn : ∀ {z : ℝ}, 0 ≤ z → HasNonnegCoeffs (f + C z * g))
    (hpf : ∀ {z : ℝ}, 0 ≤ z →
      IsPolyaFrequencySequence (fun n => (f + C z * g).coeff n)) :
    PosComboRealRooted f g := by
  intro a b ha hb
  let z : ℝ := b / a
  have hz : 0 ≤ z := div_nonneg hb.le ha.le
  have hp_rr : ((f + C z * g) ≠ 0 ∧
    (f + C z * g).Splits) := (hASW (hne hz) (hnn hz) (hpf hz)).1
  have haz : a * z = b := by
    dsimp [z]
    exact mul_div_cancel₀ b ha.ne'
  have hterm : C a * (C z * g) = C (a * z) * g := by
    calc
      C a * (C z * g) = (C a * C z) * g := by
        exact (mul_assoc (C a) (C z) g).symm
      _ = C (a * z) * g := by rw [C_mul]
  have hscale :
      C a * (f + C z * g) = C a * f + C b * g := by
    calc
      C a * (f + C z * g) = C a * f + C a * (C z * g) := by
        rw [mul_add]
      _ = C a * f + C (a * z) * g := by rw [hterm]
      _ = C a * f + C b * g := by rw [haz]
  rw [← hscale]
  exact isRealRooted_C_mul hp_rr ha.ne'

/--
TNN-named version of `of_aissenSchoenbergWhitney_right_pencil`.

This is convenient for LGV proofs, whose output is usually Toeplitz total
nonnegativity rather than the PF alias.
-/
theorem of_aissenSchoenbergWhitney_right_pencil_tnn
    {f g : ℝ[X]}
    (hASW : aissenSchoenbergWhitneyForwardStatement)
    (hne : ∀ {z : ℝ}, 0 ≤ z → f + C z * g ≠ 0)
    (hnn : ∀ {z : ℝ}, 0 ≤ z → HasNonnegCoeffs (f + C z * g))
    (htnn : ∀ {z : ℝ}, 0 ≤ z →
      ToeplitzTotallyNonnegative (fun n => (f + C z * g).coeff n)) :
    PosComboRealRooted f g :=
  PosComboRealRooted.of_aissenSchoenbergWhitney_right_pencil hASW hne hnn
    (fun {z} hz => htnn (z := z) hz)

/-- Any two positive combinations from the same one-parameter family again form
an Obreschkoff-compatible pair. -/
lemma family_pair_right {f g : ℝ[X]} (h : PosComboRealRooted f g)
    {μ₁ μ₂ : ℝ} (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂) :
    PosComboRealRooted (f + C μ₁ * g) (f + C μ₂ * g) := by
  intro lam μ hlam hμ
  have hsum_pos : 0 < lam + μ := add_pos hlam hμ
  have hcomb_pos : 0 < lam * μ₁ + μ * μ₂ := by
    positivity
  have hbase : ((C (lam + μ) * f + C (lam * μ₁ + μ * μ₂) * g) ≠ 0 ∧
    (C (lam + μ) * f + C (lam * μ₁ + μ * μ₂) * g).Splits) :=
    h hsum_pos hcomb_pos
  have hEq :
      C lam * (f + C μ₁ * g) + C μ * (f + C μ₂ * g)
        = C (lam + μ) * f + C (lam * μ₁ + μ * μ₂) * g := by
    rw [mul_add, mul_add]
    have h1 : C lam * (C μ₁ * g) = C (lam * μ₁) * g := by
      calc
        C lam * (C μ₁ * g) = (C lam * C μ₁) * g := by rw [mul_assoc]
        _ = C (lam * μ₁) * g := by rw [C_mul]
    have h2 : C μ * (C μ₂ * g) = C (μ * μ₂) * g := by
      calc
        C μ * (C μ₂ * g) = (C μ * C μ₂) * g := by rw [mul_assoc]
        _ = C (μ * μ₂) * g := by rw [C_mul]
    rw [h1, h2]
    calc
      C lam * f + C (lam * μ₁) * g + (C μ * f + C (μ * μ₂) * g)
          = (C lam * f + C μ * f) + (C (lam * μ₁) * g + C (μ * μ₂) * g) := by
              ac_rfl
      _ = (C lam + C μ) * f + (C (lam * μ₁) + C (μ * μ₂)) * g := by
            rw [← add_mul, ← add_mul]
      _ = C (lam + μ) * f + C (lam * μ₁ + μ * μ₂) * g := by
            rw [← C_add, ← C_add]
  simpa [hEq] using hbase

/-- Symmetric version of `family_pair_right`, normalized along the left
coefficient. -/
lemma family_pair_left {f g : ℝ[X]} (h : PosComboRealRooted f g)
    {lam₁ lam₂ : ℝ} (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) :
    PosComboRealRooted (C lam₁ * f + g) (C lam₂ * f + g) := by
  intro lam μ hlam hμ
  have hcomb_pos : 0 < lam * lam₁ + μ * lam₂ := by
    positivity
  have hsum_pos : 0 < lam + μ := add_pos hlam hμ
  have hbase : ((C (lam * lam₁ + μ * lam₂) * f + C (lam + μ) * g) ≠ 0 ∧
    (C (lam * lam₁ + μ * lam₂) * f + C (lam + μ) * g).Splits) :=
    h hcomb_pos hsum_pos
  have hEq :
      C lam * (C lam₁ * f + g) + C μ * (C lam₂ * f + g)
        = C (lam * lam₁ + μ * lam₂) * f + C (lam + μ) * g := by
    rw [mul_add, mul_add]
    have h1 : C lam * (C lam₁ * f) = C (lam * lam₁) * f := by
      calc
        C lam * (C lam₁ * f) = (C lam * C lam₁) * f := by rw [mul_assoc]
        _ = C (lam * lam₁) * f := by rw [C_mul]
    have h2 : C μ * (C lam₂ * f) = C (μ * lam₂) * f := by
      calc
        C μ * (C lam₂ * f) = (C μ * C lam₂) * f := by rw [mul_assoc]
        _ = C (μ * lam₂) * f := by rw [C_mul]
    rw [h1, h2]
    calc
      C (lam * lam₁) * f + C lam * g + (C (μ * lam₂) * f + C μ * g)
          = (C (lam * lam₁) * f + C (μ * lam₂) * f) + (C lam * g + C μ * g) := by
              ac_rfl
      _ = (C (lam * lam₁) + C (μ * lam₂)) * f + (C lam + C μ) * g := by
            rw [← add_mul, ← add_mul]
      _ = C (lam * lam₁ + μ * lam₂) * f + C (lam + μ) * g := by
            rw [← C_add, ← C_add]
  simpa [hEq] using hbase

lemma family_no_common_right {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {μ₁ μ₂ : ℝ} (hμ : μ₁ ≠ μ₂) :
    ∀ r, (f + C μ₁ * g).IsRoot r → ¬ (f + C μ₂ * g).IsRoot r := by
  intro r hr₁ hr₂
  have h₁ : f.eval r + μ₁ * g.eval r = 0 := by
    simpa [Polynomial.IsRoot.def, eval_add, eval_mul] using hr₁
  have h₂ : f.eval r + μ₂ * g.eval r = 0 := by
    simpa [Polynomial.IsRoot.def, eval_add, eval_mul] using hr₂
  have hmul : (μ₁ - μ₂) * g.eval r = 0 := by
    nlinarith [h₁, h₂]
  have hg0 : g.eval r = 0 := by
    rcases mul_eq_zero.mp hmul with hfac | hg0
    · exact False.elim <| hμ (sub_eq_zero.mp hfac)
    · exact hg0
  have hf0 : f.eval r = 0 := by
    have : f.eval r + μ₁ * g.eval r = f.eval r := by simp [hg0]
    linarith [h₁, this]
  exact hno r
    (by simpa [Polynomial.IsRoot.def] using hf0)
    (by simpa [Polynomial.IsRoot.def] using hg0)

lemma family_no_common_left {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {lam₁ lam₂ : ℝ} (hlam : lam₁ ≠ lam₂) :
    ∀ r, (C lam₁ * f + g).IsRoot r → ¬ (C lam₂ * f + g).IsRoot r := by
  intro r hr₁ hr₂
  have h₁ : lam₁ * f.eval r + g.eval r = 0 := by
    simpa [Polynomial.IsRoot.def, eval_add, eval_mul] using hr₁
  have h₂ : lam₂ * f.eval r + g.eval r = 0 := by
    simpa [Polynomial.IsRoot.def, eval_add, eval_mul] using hr₂
  have hmul : (lam₁ - lam₂) * f.eval r = 0 := by
    nlinarith [h₁, h₂]
  have hf0 : f.eval r = 0 := by
    rcases mul_eq_zero.mp hmul with hfac | hf0
    · exact False.elim <| hlam (sub_eq_zero.mp hfac)
    · exact hf0
  have hg0 : g.eval r = 0 := by
    have : lam₁ * f.eval r + g.eval r = g.eval r := by simp [hf0]
    linarith [h₁, this]
  exact hno r
    (by simpa [Polynomial.IsRoot.def] using hf0)
    (by simpa [Polynomial.IsRoot.def] using hg0)

lemma family_isCoprime_right {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {μ₁ μ₂ : ℝ} (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂) (hμ : μ₁ ≠ μ₂) :
    IsCoprime (f + C μ₁ * g) (f + C μ₂ * g) := by
  apply isCoprime_of_no_common_real_root_of_isRealRooted
  · exact hfg.isRealRooted_add_right hμ₁
  · exact hfg.isRealRooted_add_right hμ₂
  · exact family_no_common_right hno hμ

lemma family_isCoprime_left {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {lam₁ lam₂ : ℝ} (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hlam : lam₁ ≠ lam₂) :
    IsCoprime (C lam₁ * f + g) (C lam₂ * f + g) := by
  apply isCoprime_of_no_common_real_root_of_isRealRooted
  · exact hfg.isRealRooted_add_left hlam₁
  · exact hfg.isRealRooted_add_left hlam₂
  · exact family_no_common_left hno hlam

/-- Positive-combination real-rootedness descends through a shared real-rooted
factor. This is the common-factor reduction step needed for converse
arguments. -/
lemma of_mul_common_factor {d f g : ℝ[X]}
    (h : PosComboRealRooted (d * f) (d * g)) :
    PosComboRealRooted f g := by
  intro lam μ hlam hμ
  have hEq :
      C lam * (d * f) + C μ * (d * g) = d * (C lam * f + C μ * g) := by
    ring
  have hrr : ((d * (C lam * f + C μ * g)) ≠ 0 ∧
    (d * (C lam * f + C μ * g)).Splits) := by
    simpa [hEq] using h hlam hμ
  have hcombo_ne : C lam * f + C μ * g ≠ 0 := right_ne_zero_of_mul hrr.1
  exact isRealRooted_of_dvd hrr hcombo_ne ⟨d, by rw [mul_comm]⟩

/-- Positive-combination real-rootedness descends through a shared linear
factor. -/
lemma of_mul_X_sub_C {f g : ℝ[X]} {r : ℝ}
    (h : PosComboRealRooted ((X - C r) * f) ((X - C r) * g)) :
    PosComboRealRooted f g :=
  of_mul_common_factor h

private lemma hasPosLeadingCoeff_of_X_sub_C_mul {q : ℝ[X]} {r : ℝ}
    (h : HasPosLeadingCoeff ((X - C r) * q)) :
    HasPosLeadingCoeff q := by
  unfold HasPosLeadingCoeff at h ⊢
  simpa [Polynomial.leadingCoeff_mul, leadingCoeff_X_sub_C] using h

private lemma common_root_reduction_data
    {f g : ℝ[X]} {r : ℝ}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hrf : f.IsRoot r) (hrg : g.IsRoot r) :
    ∃ qf qg,
      f = (X - C r) * qf ∧
      g = (X - C r) * qg ∧
      PosComboRealRooted qf qg ∧
      HasPosLeadingCoeff qf ∧
      HasPosLeadingCoeff qg ∧
      qf.natDegree ≤ qg.natDegree ∧
      qg.natDegree ≤ qf.natDegree + 1 := by
  obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hrf
  obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hrg
  refine ⟨qf, qg, hqf, hqg, ?_, ?_, ?_, ?_, ?_⟩
  · exact (of_mul_X_sub_C (f := qf) (g := qg) (r := r) (by
        intro lam μ hlam hμ
        simpa [hqf, hqg] using hfg hlam hμ))
  · exact hasPosLeadingCoeff_of_X_sub_C_mul (by simpa [hqf] using hf_pos)
  · exact hasPosLeadingCoeff_of_X_sub_C_mul (by simpa [hqg] using hg_pos)
  · have hf_ne : f ≠ 0 := by
      intro h0
      simp [HasPosLeadingCoeff, h0] at hf_pos
    have hqf_ne : qf ≠ 0 := by
      exact right_ne_zero_of_mul (by simpa [hqf] using hf_ne)
    have hg_ne : g ≠ 0 := by
      intro h0
      simp [HasPosLeadingCoeff, h0] at hg_pos
    have hqg_ne : qg ≠ 0 := by
      exact right_ne_zero_of_mul (by simpa [hqg] using hg_ne)
    rw [hqf, hqg, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
      natDegree_mul (X_sub_C_ne_zero r) hqg_ne, natDegree_X_sub_C] at hdeg_lo
    lia
  · have hf_ne : f ≠ 0 := by
      intro h0
      simp [HasPosLeadingCoeff, h0] at hf_pos
    have hqf_ne : qf ≠ 0 := by
      exact right_ne_zero_of_mul (by simpa [hqf] using hf_ne)
    have hg_ne : g ≠ 0 := by
      intro h0
      simp [HasPosLeadingCoeff, h0] at hg_pos
    have hqg_ne : qg ≠ 0 := by
      exact right_ne_zero_of_mul (by simpa [hqg] using hg_ne)
    rw [hqf, hqg, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
      natDegree_mul (X_sub_C_ne_zero r) hqg_ne, natDegree_X_sub_C] at hdeg_hi
    lia

/-- To prove the restricted Obreschkoff converse, it is enough to handle the
no-common-roots case. Shared roots can be factored out recursively.

In the same-degree case the correct conclusion is the Obreschkoff alternative
`Prec f g ∨ Prec g f`; the degree-`+1` case remains oriented. -/
theorem prec_or_revPrec_of_posComboRealRooted_of_no_common
    (hstep :
      ∀ {f g : ℝ[X]},
        PosComboRealRooted f g →
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        Prec f g ∨ Prec g f)
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    Prec f g ∨ Prec g f := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          PosComboRealRooted f g →
          HasPosLeadingCoeff f →
          HasPosLeadingCoeff g →
          f.natDegree ≤ g.natDegree →
          g.natDegree ≤ f.natDegree + 1 →
          Prec f g ∨ Prec g f)
      f.natDegree ?_ rfl hfg hf_pos hg_pos hdeg_lo hdeg_hi
  intro n ih f g hfdeg hfg hf_pos hg_pos hdeg_lo hdeg_hi
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · exact hstep hfg hf_pos hg_pos hdeg_lo hdeg_hi hno
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, qg, hqf, hqg, hqfg, hqf_pos, hqg_pos, hqdeg_lo, hqdeg_hi⟩ :=
      common_root_reduction_data hfg hf_pos hg_pos hdeg_lo hdeg_hi hrf hrg
    have hf_ne : f ≠ 0 := by
      intro h0
      simp [HasPosLeadingCoeff, h0] at hf_pos
    have hqf_ne : qf ≠ 0 := by
      exact right_ne_zero_of_mul (by simpa [hqf] using hf_ne)
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C]
      lia
    have hprec_q : Prec qf qg ∨ Prec qg qf :=
      ih qf.natDegree hqf_deg_lt rfl hqfg hqf_pos hqg_pos hqdeg_lo hqdeg_hi
    rcases hprec_q with hprec_q | hprec_q
    · left
      have hprec_mul : Prec ((X - C r) * qf) ((X - C r) * qg) :=
        prec_mul_common_factor (isRealRooted_X_sub_C r) hprec_q
      simpa [hqf, hqg] using hprec_mul
    · right
      have hprec_mul : Prec ((X - C r) * qg) ((X - C r) * qf) :=
        prec_mul_common_factor (isRealRooted_X_sub_C r) hprec_q
      simpa [hqf, hqg] using hprec_mul

end PosComboRealRooted

/-- Positive combinations keep the larger of the two degrees when the summands
have positive leading coefficients. This is the degree bookkeeping needed for
the restricted converse setup. -/
lemma natDegree_pos_combo_eq_right_of_natDegree_le {f g : ℝ[X]}
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (C a * f + C b * g).natDegree = g.natDegree := by
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · simpa [natDegree_C_mul' ha.ne', natDegree_C_mul' hb.ne'] using
      (natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
        (by simpa [natDegree_C_mul' ha.ne', natDegree_C_mul' hb.ne'] using hlt)
        (hasPosLeadingCoeff_C_mul hb hg_pos) :
          (C a * f + C b * g).natDegree = (C b * g).natDegree)
  · have hsame : (C a * f + C b * g).natDegree = f.natDegree := by
      simpa [natDegree_C_mul' ha.ne', natDegree_C_mul' hb.ne'] using
        (natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
          (by simpa [natDegree_C_mul' ha.ne', natDegree_C_mul' hb.ne'] using heq)
          (hasPosLeadingCoeff_C_mul ha hf_pos)
          (hasPosLeadingCoeff_C_mul hb hg_pos) :
            (C a * f + C b * g).natDegree = (C a * f).natDegree)
    exact hsame.trans heq

/-- Symmetric form of `natDegree_pos_combo_eq_right_of_natDegree_le`. -/
lemma natDegree_pos_combo_eq_left_of_natDegree_le {f g : ℝ[X]}
    (hdeg : g.natDegree ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (C a * f + C b * g).natDegree = f.natDegree := by
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · simpa [natDegree_C_mul' ha.ne', natDegree_C_mul' hb.ne'] using
      (natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff
        (by simpa [natDegree_C_mul' ha.ne', natDegree_C_mul' hb.ne'] using hlt)
        (hasPosLeadingCoeff_C_mul ha hf_pos) :
          (C a * f + C b * g).natDegree = (C a * f).natDegree)
  · simpa [natDegree_C_mul' ha.ne', natDegree_C_mul' hb.ne'] using
      (natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
        (by simpa [natDegree_C_mul' ha.ne', natDegree_C_mul' hb.ne'] using heq.symm)
        (hasPosLeadingCoeff_C_mul ha hf_pos)
        (hasPosLeadingCoeff_C_mul hb hg_pos) :
          (C a * f + C b * g).natDegree = (C a * f).natDegree)

/-- Positive combinations inherit a positive leading coefficient from the
summand of maximal degree. -/
lemma hasPosLeadingCoeff_pos_combo_of_natDegree_le_right {f g : ℝ[X]}
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasPosLeadingCoeff (C a * f + C b * g) := by
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact hasPosLeadingCoeff_add_of_natDegree_lt_right
      (by simpa [natDegree_C_mul' ha.ne', natDegree_C_mul' hb.ne'] using hlt)
      (hasPosLeadingCoeff_C_mul hb hg_pos)
  · exact hasPosLeadingCoeff_add_of_same_natDegree
      (by simpa [natDegree_C_mul' ha.ne', natDegree_C_mul' hb.ne'] using heq)
      (hasPosLeadingCoeff_C_mul ha hf_pos)
      (hasPosLeadingCoeff_C_mul hb hg_pos)

/-- Symmetric form of `hasPosLeadingCoeff_pos_combo_of_natDegree_le_right`. -/
lemma hasPosLeadingCoeff_pos_combo_of_natDegree_le_left {f g : ℝ[X]}
    (hdeg : g.natDegree ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasPosLeadingCoeff (C a * f + C b * g) := by
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact hasPosLeadingCoeff_add_of_natDegree_lt_left
      (by simpa [natDegree_C_mul' ha.ne', natDegree_C_mul' hb.ne'] using hlt)
      (hasPosLeadingCoeff_C_mul ha hf_pos)
  · exact hasPosLeadingCoeff_add_of_same_natDegree
      (by simpa [natDegree_C_mul' ha.ne', natDegree_C_mul' hb.ne'] using heq.symm)
      (hasPosLeadingCoeff_C_mul ha hf_pos)
      (hasPosLeadingCoeff_C_mul hb hg_pos)

namespace PosComboRealRooted

lemma family_natDegree_right {f g : ℝ[X]}
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {μ : ℝ} (hμ : 0 < μ) :
    (f + C μ * g).natDegree = g.natDegree := by
  simpa [one_mul] using
    natDegree_pos_combo_eq_right_of_natDegree_le hdeg hf_pos hg_pos zero_lt_one hμ

lemma family_natDegree_left {f g : ℝ[X]}
    (hdeg : g.natDegree ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {lam : ℝ} (hlam : 0 < lam) :
    (C lam * f + g).natDegree = f.natDegree := by
  simpa [one_mul] using
    natDegree_pos_combo_eq_left_of_natDegree_le hdeg hf_pos hg_pos hlam zero_lt_one

lemma family_hasPosLeadingCoeff_right {f g : ℝ[X]}
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {μ : ℝ} (hμ : 0 < μ) :
    HasPosLeadingCoeff (f + C μ * g) := by
  simpa [one_mul] using
    hasPosLeadingCoeff_pos_combo_of_natDegree_le_right
      hdeg hf_pos hg_pos zero_lt_one hμ

lemma family_hasPosLeadingCoeff_left {f g : ℝ[X]}
    (hdeg : g.natDegree ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {lam : ℝ} (hlam : 0 < lam) :
    HasPosLeadingCoeff (C lam * f + g) := by
  simpa [one_mul] using
    hasPosLeadingCoeff_pos_combo_of_natDegree_le_left
      hdeg hf_pos hg_pos hlam zero_lt_one

lemma family_pair_data_right {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {μ₁ μ₂ : ℝ} (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂) (hμ : μ₁ ≠ μ₂) :
    PosComboRealRooted (f + C μ₁ * g) (f + C μ₂ * g) ∧
    HasPosLeadingCoeff (f + C μ₁ * g) ∧
    HasPosLeadingCoeff (f + C μ₂ * g) ∧
    (f + C μ₁ * g).natDegree = g.natDegree ∧
    (f + C μ₂ * g).natDegree = g.natDegree ∧
    IsCoprime (f + C μ₁ * g) (f + C μ₂ * g) := by
  refine ⟨family_pair_right hfg hμ₁ hμ₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact family_hasPosLeadingCoeff_right hdeg hf_pos hg_pos hμ₁
  · exact family_hasPosLeadingCoeff_right hdeg hf_pos hg_pos hμ₂
  · exact family_natDegree_right hdeg hf_pos hg_pos hμ₁
  · exact family_natDegree_right hdeg hf_pos hg_pos hμ₂
  · exact family_isCoprime_right hfg hno hμ₁ hμ₂ hμ

lemma family_pair_data_left {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {lam₁ lam₂ : ℝ} (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (hlam : lam₁ ≠ lam₂) :
    PosComboRealRooted (C lam₁ * f + g) (C lam₂ * f + g) ∧
    HasPosLeadingCoeff (C lam₁ * f + g) ∧
    HasPosLeadingCoeff (C lam₂ * f + g) ∧
    (C lam₁ * f + g).natDegree = f.natDegree ∧
    (C lam₂ * f + g).natDegree = f.natDegree ∧
    IsCoprime (C lam₁ * f + g) (C lam₂ * f + g) := by
  refine ⟨family_pair_left hfg hlam₁ hlam₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact family_hasPosLeadingCoeff_left hdeg hf_pos hg_pos hlam₁
  · exact family_hasPosLeadingCoeff_left hdeg hf_pos hg_pos hlam₂
  · exact family_natDegree_left hdeg hf_pos hg_pos hlam₁
  · exact family_natDegree_left hdeg hf_pos hg_pos hlam₂
  · exact family_isCoprime_left hfg hno hlam₁ hlam₂ hlam

/-- Specialized `1/2` right-family package for `(f + g, f + 2g)`. This is the
canonical positive-combination reroute used in the same-degree bridge search. -/
lemma family_pair_data_right_one_two {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    PosComboRealRooted (f + C (1 : ℝ) * g) (f + C (2 : ℝ) * g) ∧
    HasPosLeadingCoeff (f + C (1 : ℝ) * g) ∧
    HasPosLeadingCoeff (f + C (2 : ℝ) * g) ∧
    (f + C (1 : ℝ) * g).natDegree = g.natDegree ∧
    (f + C (2 : ℝ) * g).natDegree = g.natDegree ∧
    IsCoprime (f + C (1 : ℝ) * g) (f + C (2 : ℝ) * g) := by
  exact
    family_pair_data_right
      (f := f) (g := g) hfg hdeg hf_pos hg_pos hno zero_lt_one (by norm_num)
      (by norm_num)

/-- Symmetric `1/2` left-family package for `(f + g, 2f + g)`. -/
lemma family_pair_data_left_one_two {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree ≤ f.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    PosComboRealRooted (C (1 : ℝ) * f + g) (C (2 : ℝ) * f + g) ∧
    HasPosLeadingCoeff (C (1 : ℝ) * f + g) ∧
    HasPosLeadingCoeff (C (2 : ℝ) * f + g) ∧
    (C (1 : ℝ) * f + g).natDegree = f.natDegree ∧
    (C (2 : ℝ) * f + g).natDegree = f.natDegree ∧
    IsCoprime (C (1 : ℝ) * f + g) (C (2 : ℝ) * f + g) := by
  exact
    family_pair_data_left
      (f := f) (g := g) hfg hdeg hf_pos hg_pos hno zero_lt_one (by norm_num)
      (by norm_num)

private lemma sub_family_left_one_two {f g : ℝ[X]} :
    (C (2 : ℝ) * f + g) - (C (1 : ℝ) * f + g) = f := by
  ext n
  simp [sub_eq_add_neg]
  ring

private lemma sub_family_right_one_two {f g : ℝ[X]} :
    (f + C (2 : ℝ) * g) - (f + C (1 : ℝ) * g) = g := by
  ext n
  simp [sub_eq_add_neg]
  ring

private lemma add_family_left_one_two {f g : ℝ[X]} :
    (C (1 : ℝ) * f + g) + f = C (2 : ℝ) * f + g := by
  ext n
  simp
  ring

private lemma add_family_right_one_two {f g : ℝ[X]} :
    (f + C (1 : ℝ) * g) + g = f + C (2 : ℝ) * g := by
  ext n
  simp
  ring

private lemma not_isRoot_right_of_isCoprime_of_sub_eq
    {p q h : ℝ[X]} (hcop : IsCoprime p q) (hsub : q - p = h) :
    ∀ r, q.IsRoot r → ¬ h.IsRoot r := by
  intro r hq hh
  have hp : p.IsRoot r := by
    have h_eval : (q - p).eval r = 0 := by
      rw [hsub]
      simpa [Polynomial.IsRoot.def] using hh
    have hq_eval : q.eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hq
    have hp_eval : p.eval r = 0 := by
      rw [eval_sub] at h_eval
      linarith
    simpa [Polynomial.IsRoot.def] using hp_eval
  obtain ⟨a, b, hab⟩ := hcop
  have h_eval := congrArg (fun t : ℝ[X] => t.eval r) hab
  have hp_eval : p.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hp
  have hq_eval : q.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hq
  have : (1 : ℝ) = 0 := by
    simp [eval_add, eval_mul, hp_eval, hq_eval] at h_eval
  exact one_ne_zero this

private lemma not_isRoot_left_of_isCoprime_of_add_eq
    {p q h : ℝ[X]} (hcop : IsCoprime p q) (hadd : p + h = q) :
    ∀ r, p.IsRoot r → ¬ h.IsRoot r := by
  intro r hp hh
  have hq : q.IsRoot r := by
    have hp_eval : p.eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hp
    have hh_eval : h.eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hh
    have hq_eval : q.eval r = 0 := by
      rw [← hadd, eval_add]
      linarith
    simpa [Polynomial.IsRoot.def] using hq_eval
  obtain ⟨a, b, hab⟩ := hcop
  have h_eval := congrArg (fun t : ℝ[X] => t.eval r) hab
  have hp_eval : p.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hp
  have hq_eval : q.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hq
  have : (1 : ℝ) = 0 := by
    simp [eval_add, eval_mul, hp_eval, hq_eval] at h_eval
  exact one_ne_zero this

private lemma family_left_one_two_no_root_f_of_root_q {f g : ℝ[X]}
    (hcop : IsCoprime (C (1 : ℝ) * f + g) (C (2 : ℝ) * f + g)) :
    ∀ r, (C (2 : ℝ) * f + g).IsRoot r → ¬ f.IsRoot r := by
  simpa using
    not_isRoot_right_of_isCoprime_of_sub_eq
      (p := C (1 : ℝ) * f + g) (q := C (2 : ℝ) * f + g) (h := f)
      hcop (sub_family_left_one_two (f := f) (g := g))

private lemma family_left_one_two_no_root_f_of_root_p {f g : ℝ[X]}
    (hcop : IsCoprime (C (1 : ℝ) * f + g) (C (2 : ℝ) * f + g)) :
    ∀ r, (C (1 : ℝ) * f + g).IsRoot r → ¬ f.IsRoot r := by
  simpa using
    not_isRoot_left_of_isCoprime_of_add_eq
      (p := C (1 : ℝ) * f + g) (q := C (2 : ℝ) * f + g) (h := f)
      hcop (add_family_left_one_two (f := f) (g := g))

private lemma family_right_one_two_no_root_g_of_root_q {f g : ℝ[X]}
    (hcop : IsCoprime (f + C (1 : ℝ) * g) (f + C (2 : ℝ) * g)) :
    ∀ r, (f + C (2 : ℝ) * g).IsRoot r → ¬ g.IsRoot r := by
  simpa using
    not_isRoot_right_of_isCoprime_of_sub_eq
      (p := f + C (1 : ℝ) * g) (q := f + C (2 : ℝ) * g) (h := g)
      hcop (sub_family_right_one_two (f := f) (g := g))

private lemma family_right_one_two_no_root_g_of_root_p {f g : ℝ[X]}
    (hcop : IsCoprime (f + C (1 : ℝ) * g) (f + C (2 : ℝ) * g)) :
    ∀ r, (f + C (1 : ℝ) * g).IsRoot r → ¬ g.IsRoot r := by
  simpa using
    not_isRoot_left_of_isCoprime_of_add_eq
      (p := f + C (1 : ℝ) * g) (q := f + C (2 : ℝ) * g) (h := g)
      hcop (add_family_right_one_two (f := f) (g := g))

private lemma family_left_one_two_not_root_of_root_g {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, g.IsRoot r → ¬ (C (1 : ℝ) * f + g).IsRoot r := by
  intro r hgr hp
  have hg_eval : g.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hgr
  have hp_eval : (C (1 : ℝ) * f + g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hp
  have hf_eval : f.eval r = 0 := by
    simpa [eval_add, eval_mul, hg_eval] using hp_eval
  exact hno r
    (by simpa [Polynomial.IsRoot.def] using hf_eval)
    hgr

private lemma family_left_two_two_not_root_of_root_g {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, g.IsRoot r → ¬ (C (2 : ℝ) * f + g).IsRoot r := by
  intro r hgr hq
  have hg_eval : g.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hgr
  have hq_eval : (C (2 : ℝ) * f + g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hq
  have hf_eval : f.eval r = 0 := by
    simpa [eval_add, eval_mul, hg_eval] using hq_eval
  exact hno r
    (by simpa [Polynomial.IsRoot.def] using hf_eval)
    hgr

private lemma family_right_one_two_not_root_of_root_f {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, f.IsRoot r → ¬ (f + C (1 : ℝ) * g).IsRoot r := by
  intro r hfr hp
  have hf_eval : f.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hfr
  have hp_eval : (f + C (1 : ℝ) * g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hp
  have hg_eval : g.eval r = 0 := by
    simpa [eval_add, eval_mul, hf_eval] using hp_eval
  exact hno r
    hfr
    (by simpa [Polynomial.IsRoot.def] using hg_eval)

private lemma family_right_two_two_not_root_of_root_f {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, f.IsRoot r → ¬ (f + C (2 : ℝ) * g).IsRoot r := by
  intro r hfr hq
  have hf_eval : f.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hfr
  have hq_eval : (f + C (2 : ℝ) * g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hq
  have hg_eval : g.eval r = 0 := by
    simpa [eval_add, eval_mul, hf_eval] using hq_eval
  exact hno r
    hfr
    (by simpa [Polynomial.IsRoot.def] using hg_eval)

/-- A common root of the specialized right family `(f + g, f + 2g)` is already
a common root of `(f, g)`, so the original no-common hypothesis excludes it. -/
theorem no_common_root_right_family_one_two_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, (f + C (1 : ℝ) * g).IsRoot r → ¬ (f + C (2 : ℝ) * g).IsRoot r := by
  intro r hp hq
  have hp_eval : (f + C (1 : ℝ) * g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hp
  have hq_eval : (f + C (2 : ℝ) * g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hq
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hp_eval hq_eval
  have hg_eval : g.eval r = 0 := by
    linarith
  have hf_eval : f.eval r = 0 := by
    linarith
  exact hno r
    (by simpa [Polynomial.IsRoot.def] using hf_eval)
    (by simpa [Polynomial.IsRoot.def] using hg_eval)

/-- At a root of `f + 2g`, the companion family member `f + g` has the
opposite sign of `g`; the original no-common-root hypothesis makes the sign
strict. -/
theorem eval_mul_right_family_one_neg_at_root_two_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, (f + C (2 : ℝ) * g).IsRoot r → (f + C (1 : ℝ) * g).eval r * g.eval r < 0 := by
  intro r hroot
  have hq_eval : (f + C (2 : ℝ) * g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hroot
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hq_eval
  have hp_eval : (f + C (1 : ℝ) * g).eval r = -g.eval r := by
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    linarith
  have hg_ne : g.eval r ≠ 0 := by
    intro hg0
    have hf0 : f.eval r = 0 := by
      linarith
    exact hno r
      (by simpa [Polynomial.IsRoot.def] using hf0)
      (by simpa [Polynomial.IsRoot.def] using hg0)
  calc
    (f + C (1 : ℝ) * g).eval r * g.eval r = -(g.eval r) ^ 2 := by
      rw [hp_eval]
      ring
    _ < 0 := by
      have hsq : 0 < (g.eval r) ^ 2 := sq_pos_iff.mpr hg_ne
      nlinarith

/-- At a root of `f + g`, the other specialized right-family member `f + 2g`
has the opposite sign of `f`; again the no-common-root hypothesis makes the
sign strict. -/
theorem eval_mul_right_family_two_neg_at_root_one_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, (f + C (1 : ℝ) * g).IsRoot r → (f + C (2 : ℝ) * g).eval r * f.eval r < 0 := by
  intro r hroot
  have hp_eval0 : (f + C (1 : ℝ) * g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hroot
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hp_eval0
  have hq_eval : (f + C (2 : ℝ) * g).eval r = -f.eval r := by
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    linarith
  have hf_ne : f.eval r ≠ 0 := by
    intro hf0
    have hg0 : g.eval r = 0 := by
      linarith
    exact hno r
      (by simpa [Polynomial.IsRoot.def] using hf0)
      (by simpa [Polynomial.IsRoot.def] using hg0)
  calc
    (f + C (2 : ℝ) * g).eval r * f.eval r = -(f.eval r) ^ 2 := by
      rw [hq_eval]
      ring
    _ < 0 := by
      have hsq : 0 < (f.eval r) ^ 2 := sq_pos_iff.mpr hf_ne
      nlinarith

/-- Same-degree `Prec` can be recovered once one has strict sign changes of `g`
on consecutive roots of `f` and one root of `g` strictly to the right of all
roots of `f`. This repackages the final Ma--Wang assembly step in the form
needed by the same-degree Obreschkoff converse. -/
theorem prec_same_of_root_sign_data
    {f g : ℝ[X]}
    (hf : f ≠ 0 ∧ f.Splits)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ f.natDegree)
    (hsign :
      let rs := f.roots.sort (· ≤ ·)
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        g.eval r₁ * g.eval r₂ < 0)
    (hright :
      let rs := f.roots.sort (· ≤ ·)
      ∃ uR, g.IsRoot uR ∧ ∀ r ∈ rs, r < uR) :
    Prec f g := by
  let rs := f.roots.sort (· ≤ ·)
  have hrs_eq : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hlen : rs.length = f.natDegree := by
    rw [show rs = f.roots.sort (· ≤ ·) by rfl, Multiset.length_sort, card_roots_of_splits hf.2]
  have hn : 1 ≤ rs.length := by
    rw [hlen]
    exact hdeg_pos
  have hg_ne : g ≠ 0 := by
    intro hg0
    simp [HasPosLeadingCoeff, hg0] at hg_pos
  exact
    prec_same_of_strict_signs_of_right_root
      hf hg_ne hrs_sorted hrs_eq hdeg hn
      (by simpa [rs] using hsign)
      (by simpa [rs] using hright)

/-- An equal-degree Obreschkoff alternative can be oriented once we know that
`f` has a root strictly to the right of an upper bound for all roots of `g`. -/
theorem prec_of_prec_or_revPrec_of_root_asymmetry
    {f g : ℝ[X]} {c r : ℝ}
    (h : Prec f g ∨ Prec g f)
    (hg_le : ∀ s ∈ g.roots, s ≤ c)
    (hfr : f.IsRoot r)
    (hc_lt : c < r) :
    Prec g f := by
  rcases h with hfg | hgf
  · exfalso
    have hfle : r ≤ c := roots_le_of_prec_right hfg hg_le r ((mem_roots hfg.1.1).mpr hfr)
    exact (not_le_of_gt hc_lt) hfle
  · exact hgf

/-- Symmetric orientation selector for the equal-degree Obreschkoff
alternative. -/
theorem revPrec_of_prec_or_revPrec_of_root_asymmetry
    {f g : ℝ[X]} {c r : ℝ}
    (h : Prec f g ∨ Prec g f)
    (hf_le : ∀ s ∈ f.roots, s ≤ c)
    (hgr : g.IsRoot r)
    (hc_lt : c < r) :
    Prec f g := by
  exact
    prec_of_prec_or_revPrec_of_root_asymmetry
      (f := g) (g := f) (c := c) (r := r) (by simpa [or_comm] using h)
      hf_le hgr hc_lt

/-- Linear equal-degree case of the same-degree Obreschkoff alternative. -/
theorem prec_or_revPrec_of_same_degree_one
    {f g : ℝ[X]}
    (hdeg : g.natDegree = f.natDegree)
    (hf_deg1 : f.natDegree = 1) :
    Prec f g ∨ Prec g f := by
  have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_degree_one hf_deg1
  have hg_rr : (g ≠ 0 ∧ g.Splits) := by
    apply isRealRooted_of_degree_one
    lia
  obtain ⟨rf, hrf_eq⟩ : ∃ rf, f.roots = {rf} := by
    apply Multiset.card_eq_one.mp
    simpa [hf_deg1] using card_roots_of_splits hf_rr.2
  obtain ⟨rg, hrg_eq⟩ : ∃ rg, g.roots = {rg} := by
    apply Multiset.card_eq_one.mp
    have : g.natDegree = 1 := by lia
    simpa [this] using card_roots_of_splits hg_rr.2
  by_cases hle : rf ≤ rg
  · left
    refine
      ⟨hf_rr, hg_rr, [rf], [rg], List.pairwise_singleton _ _,
        List.pairwise_singleton _ _, ?_, ?_, ?_⟩
    · simp [hrf_eq]
    · simp [hrg_eq]
    · exact Or.inr ⟨by simp, by simp [ListAlternates, ListInterlaces, hle]⟩
  · right
    have hge : rg ≤ rf := le_of_not_ge hle
    refine
      ⟨hg_rr, hf_rr, [rg], [rf], List.pairwise_singleton _ _,
        List.pairwise_singleton _ _, ?_, ?_, ?_⟩
    · simp [hrg_eq]
    · simp [hrf_eq]
    · exact Or.inr ⟨by simp, by simp [ListAlternates, ListInterlaces, hge]⟩

end PosComboRealRooted

/-! ### Note on PosComboRealRooted and interlacing

`PosComboRealRooted f g` (all positive scalar combinations real-rooted) is
equivalent to `f` and `g` having a **common interlacer** (Ryder/Obreschkoff,
Theorem 6.3). This is strictly weaker than `Prec f g` (strong interlacing).

Counterexample: `f = (x+1)(x+3)`, `g = x(x+4)` satisfies `PosComboRealRooted`
but roots `{-4, -3, -1, 0}` don't interlace (pattern g, f, f, g).

For strong interlacing `Prec f g`, one needs the **affine family** hypothesis
`(λx + μ)f + g` real-rooted for all `λ, μ > 0`, with nonneg coefficients.
This is Brändén's Lemma 7.8.4, stated as `prec_of_affine_family_nonneg`
in `InterlacingSequence.lean`.

The correct Obreschkoff converse is: `PosComboRealRooted f g` implies
`∃ h, Prec h f ∧ Prec h g` (existence of a common interlacer). -/

/-- If `f ⊳ g` with positive leading coefficients and positive `λ, μ`,
    then `λf + μg` interlaces `g` from the left: `Prec (λf + μg) g`.
    This is the positive-coefficient special case of `prec_nonneg_combo_right`. -/
theorem prec_convex_right {f g : ℝ[X]}
    (hfg : Prec f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (_hfg_rr : (C a * f + C b * g) ≠ 0 ∧
      (C a * f + C b * g).Splits)
    (_hcop : IsCoprime (C a * f) (C b * g)) :
    Prec (C a * f + C b * g) g := by
  exact prec_nonneg_combo_right hfg hf_pos hg_pos ha.le hb.le (Or.inl ha)

/-- If `f ⊳ g` with positive leading coefficients and non-negative `a, b`,
    not both zero, then `f` interlaces `a·f + b·g` from the right provided
    the Wagner 2 hypotheses hold in the genuinely two-term case. -/
theorem prec_nonneg_combo_left {f g : ℝ[X]}
    (hfg : Prec f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a ∨ 0 < b)
    (hfg_rr : (C a * f + C b * g) ≠ 0 ∧
      (C a * f + C b * g).Splits)
    (hcop : IsCoprime (C a * f) (C b * g)) :
    Prec f (C a * f + C b * g) := by
  rcases hab with ha_pos | hb_pos
  · by_cases hb0 : b = 0
    · simpa [hb0, weightedSum, weightedSum_cons] using
        (prec_C_mul_right (prec_refl hfg.1) ha_pos.ne')
    · have hb_pos : 0 < b := by
        exact lt_of_le_of_ne hb (by simpa [eq_comm] using hb0)
      have hCa_pos : HasPosLeadingCoeff (C a * f) := hasPosLeadingCoeff_C_mul ha_pos hf_pos
      have hCb_pos : HasPosLeadingCoeff (C b * g) := hasPosLeadingCoeff_C_mul hb_pos hg_pos
      exact prec_add_of_prec_left
        (prec_C_mul_right (prec_refl hfg.1) ha_pos.ne')
        (prec_C_mul_right hfg hb_pos.ne')
        hCa_pos hCb_pos hfg_rr hcop
  · by_cases ha0 : a = 0
    · simpa [ha0, weightedSum, weightedSum_cons] using
        (prec_C_mul_right hfg hb_pos.ne')
    · have ha_pos : 0 < a := by
        exact lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
      have hCa_pos : HasPosLeadingCoeff (C a * f) := hasPosLeadingCoeff_C_mul ha_pos hf_pos
      have hCb_pos : HasPosLeadingCoeff (C b * g) := hasPosLeadingCoeff_C_mul hb_pos hg_pos
      exact prec_add_of_prec_left
        (prec_C_mul_right (prec_refl hfg.1) ha_pos.ne')
        (prec_C_mul_right hfg hb_pos.ne')
        hCa_pos hCb_pos hfg_rr hcop

/-- If `f ⊳ g` with positive leading coefficients and positive `a, b`,
    then `f` interlaces `a·f + b·g` from the right: `Prec f (a·f + b·g)`.
    (Wagner 2 applied to `C a * f` and `C b * g`, both interlaced by `f`.) -/
theorem prec_convex_left {f g : ℝ[X]}
    (hfg : Prec f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hfg_rr : (C a * f + C b * g) ≠ 0 ∧
      (C a * f + C b * g).Splits)
    (hcop : IsCoprime (C a * f) (C b * g)) :
    Prec f (C a * f + C b * g) := by
  have hCa_pos : HasPosLeadingCoeff (C a * f) := hasPosLeadingCoeff_C_mul ha hf_pos
  have hCb_pos : HasPosLeadingCoeff (C b * g) := hasPosLeadingCoeff_C_mul hb hg_pos
  exact prec_add_of_prec_left
    (prec_C_mul_right (prec_refl hfg.1) ha.ne')
    (prec_C_mul_right hfg hb.ne')
    hCa_pos hCb_pos hfg_rr hcop

/-- A common-factor version of `prec_convex_left`. If `f` and `g` share a
real-rooted factor `d`, it is enough to verify the Wagner-2 hypotheses after
factoring out `d`. -/
theorem prec_convex_left_of_common_factor {d f g : ℝ[X]}
    (hd : d ≠ 0 ∧ d.Splits)
    {f' g' : ℝ[X]}
    (hf_def : f = d * f') (hg_def : g = d * g')
    (hfg : Prec f' g')
    (hf'_pos : HasPosLeadingCoeff f') (hg'_pos : HasPosLeadingCoeff g')
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hfg'_rr : (C a * f' + C b * g') ≠ 0 ∧
      (C a * f' + C b * g').Splits)
    (hcop : IsCoprime (C a * f') (C b * g')) :
    Prec f (C a * f + C b * g) := by
  subst hf_def hg_def
  have hbase : Prec f' (C a * f' + C b * g') :=
    prec_convex_left hfg hf'_pos hg'_pos ha hb hfg'_rr hcop
  have hmul : Prec (d * f') (d * (C a * f' + C b * g')) :=
    prec_mul_common_factor hd hbase
  simpa [left_distrib, right_distrib, mul_add, mul_assoc, mul_left_comm, mul_comm,
    add_assoc, add_left_comm, add_comm] using hmul

end RealRooted
