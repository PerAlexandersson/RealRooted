import RealRooted.MaWang.StrictSigns

open Polynomial Filter

noncomputable section

namespace RealRooted.MaWangInternal

/-- Liu--Wang differ-by-1 form: if `g ⊳ f`, `F` has degree `deg(f)+1`, positive
leading coefficient, and at every root `r` of `f` the value `F(r)` has the
opposite sign from `g(r)`, then `f ⊳ F`. -/
theorem prec_of_interlaces_eval_mul_neg_succ {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg : F.natDegree = f.natDegree + 1)
    (hroot_sign : ∀ r, f.IsRoot r → F.eval r * g.eval r < 0) :
    Prec f F := by
  obtain ⟨hf, hg, hgdeg, rs, ss, hrs_sorted, hss_sorted, hrs_eq, hss_eq, hint⟩ := hgf
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf.2]
  have hn : 1 ≤ rs.length := by lia
  have hrs_ne : rs ≠ [] := by grind
  obtain ⟨r₀, rs', rfl⟩ : ∃ r₀ rs', rs = r₀ :: rs' := by
    cases rs with
    | nil => lia
    | cons r₀ rs' => lia
  have hr₀_root : f.IsRoot r₀ := by
    apply (mem_roots hf.1).mp
    rw [← hrs_eq]
    simp
  have hlast_root : f.IsRoot ((r₀ :: rs').getLast (by lia)) := by
    apply (mem_roots hf.1).mp
    rw [← hrs_eq]
    simp
  have hno_g_at_f : ∀ r, f.IsRoot r → ¬ g.IsRoot r := by
    intro r hr hgr
    have hprod := hroot_sign r hr
    simp_all
  have hhead_lt_roots_g : ∀ t ∈ g.roots, r₀ < t := by
    intro t ht
    have ht_ss : t ∈ ss := by
      apply Multiset.mem_coe.mp
      lia
    have hr₀_le_t : r₀ ≤ t := listInterlaces_all_ge ss rs' r₀ hint t ht_ss
    have ht_root : g.IsRoot t := (mem_roots hg.1).mp ht
    grind
  have hroots_g_lt_last : ∀ t ∈ g.roots, t < (r₀ :: rs').getLast (by lia) := by
    intro t ht
    have ht_ss : t ∈ ss := by
      apply Multiset.mem_coe.mp
      lia
    have ht_le_last : t ≤ (r₀ :: rs').getLast (by lia) :=
      listInterlaces_all_le_getLast (rs := r₀ :: rs') (by lia) hrs_sorted hint t ht_ss
    have ht_root : g.IsRoot t := (mem_roots hg.1).mp ht
    grind
  have hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        (r₀ :: rs') = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    intro pre r₁ r₂ rest hEq
    have hr₁_root : f.IsRoot r₁ := by
      apply (mem_roots hf.1).mp
      simpa [hrs_eq] using Multiset.mem_coe.mpr (by simp_all : r₁ ∈ r₀ :: rs')
    have hr₂_root : f.IsRoot r₂ := by
      apply (mem_roots hf.1).mp
      simpa [hrs_eq] using Multiset.mem_coe.mpr (by simp_all : r₂ ∈ r₀ :: rs')
    have hFg₁ : F.eval r₁ * g.eval r₁ < 0 := hroot_sign r₁ hr₁_root
    have hFg₂ : F.eval r₂ * g.eval r₂ < 0 := hroot_sign r₂ hr₂_root
    have hgg_nonpos : g.eval r₁ * g.eval r₂ ≤ 0 :=
      eval_mul_eval_nonpos_of_interlacing_consecutive hg.2 hrs_sorted hss_eq hint hEq
    have hg₁_ne : g.eval r₁ ≠ 0 := by simp_all
    have hg₂_ne : g.eval r₂ ≠ 0 := by simp_all
    have hgg_neg : g.eval r₁ * g.eval r₂ < 0 := by grind
    exact mul_neg_of_mul_neg_of_mul_neg hFg₁ hFg₂ hgg_neg
  rcases Nat.even_or_odd f.natDegree with hf_even | hf_odd
  · have hg_odd : Odd g.natDegree := by grind
    have hg_left_neg : g.eval r₀ < 0 :=
      eval_neg_of_all_roots_gt_of_odd hg.1 hg_pos hg_odd hhead_lt_roots_g
    have hF_left_pos : 0 < F.eval r₀ := by
      have hprod := hroot_sign r₀ hr₀_root
      nlinarith
    have hg_right_pos : 0 < g.eval ((r₀ :: rs').getLast (by lia)) :=
      eval_pos_of_all_roots_lt hg.1 hg.2 hg_pos hroots_g_lt_last
    have hF_right_neg : F.eval ((r₀ :: rs').getLast (by lia)) < 0 := by
      have hprod := hroot_sign ((r₀ :: rs').getLast (by lia)) hlast_root
      nlinarith
    exact prec_of_strict_signs_of_endSigns_even hf.1 hf.2 hF_pos hrs_sorted hrs_eq hdeg hn hf_even
      hsign hF_left_pos hF_right_neg
  · have hg_even : Even g.natDegree := by grind
    have hg_left_pos : 0 < g.eval r₀ :=
      eval_pos_of_all_roots_gt_of_even hg.1 hg_pos hg_even hhead_lt_roots_g
    have hF_left_neg : F.eval r₀ < 0 := by
      have hprod := hroot_sign r₀ hr₀_root
      nlinarith
    have hg_right_pos : 0 < g.eval ((r₀ :: rs').getLast (by lia)) :=
      eval_pos_of_all_roots_lt hg.1 hg.2 hg_pos hroots_g_lt_last
    have hF_right_neg : F.eval ((r₀ :: rs').getLast (by lia)) < 0 := by
      have hprod := hroot_sign ((r₀ :: rs').getLast (by lia)) hlast_root
      nlinarith
    exact prec_of_strict_signs_of_endSigns_odd hf.1 hf.2 hF_pos hrs_sorted hrs_eq hdeg hn hf_odd
      hsign hF_left_neg hF_right_neg

/-- Liu--Wang same-degree form: if `g ⊳ f`, `F` has the same degree as `f`,
positive leading coefficient, and at every root `r` of `f` the value `F(r)`
has the opposite sign from `g(r)`, then `f ≺ F` in the same-degree sense. -/
theorem prec_of_interlaces_eval_mul_neg_same {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg : F.natDegree = f.natDegree)
    (hroot_sign : ∀ r, f.IsRoot r → F.eval r * g.eval r < 0) :
    Prec f F := by
  obtain ⟨hf, hg, hgdeg, rs, ss, hrs_sorted, hss_sorted, hrs_eq, hss_eq, hint⟩ := hgf
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf.2]
  have hn : 1 ≤ rs.length := by lia
  have hrs_ne : rs ≠ [] := by grind
  obtain ⟨r₀, rs', rfl⟩ : ∃ r₀ rs', rs = r₀ :: rs' := by
    cases rs with
    | nil => lia
    | cons r₀ rs' => lia
  have hlast_root : f.IsRoot ((r₀ :: rs').getLast (by lia)) := by
    apply (mem_roots hf.1).mp
    rw [← hrs_eq]
    simp
  have hno_g_at_f : ∀ r, f.IsRoot r → ¬ g.IsRoot r := by
    intro r hr hgr
    have hprod := hroot_sign r hr
    simp_all
  have hroots_g_lt_last : ∀ t ∈ g.roots, t < (r₀ :: rs').getLast (by lia) := by
    intro t ht
    have ht_ss : t ∈ ss := by
      apply Multiset.mem_coe.mp
      lia
    have ht_le_last : t ≤ (r₀ :: rs').getLast (by lia) :=
      listInterlaces_all_le_getLast (rs := r₀ :: rs') (by lia) hrs_sorted hint t ht_ss
    have ht_root : g.IsRoot t := (mem_roots hg.1).mp ht
    grind
  have hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        (r₀ :: rs') = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    intro pre r₁ r₂ rest hEq
    have hr₁_root : f.IsRoot r₁ := by
      apply (mem_roots hf.1).mp
      simpa [hrs_eq] using Multiset.mem_coe.mpr (by simp_all : r₁ ∈ r₀ :: rs')
    have hr₂_root : f.IsRoot r₂ := by
      apply (mem_roots hf.1).mp
      simpa [hrs_eq] using Multiset.mem_coe.mpr (by simp_all : r₂ ∈ r₀ :: rs')
    have hFg₁ : F.eval r₁ * g.eval r₁ < 0 := hroot_sign r₁ hr₁_root
    have hFg₂ : F.eval r₂ * g.eval r₂ < 0 := hroot_sign r₂ hr₂_root
    have hgg_nonpos : g.eval r₁ * g.eval r₂ ≤ 0 :=
      eval_mul_eval_nonpos_of_interlacing_consecutive hg.2 hrs_sorted hss_eq hint hEq
    have hg₁_ne : g.eval r₁ ≠ 0 := by simp_all
    have hg₂_ne : g.eval r₂ ≠ 0 := by simp_all
    have hgg_neg : g.eval r₁ * g.eval r₂ < 0 := by grind
    exact mul_neg_of_mul_neg_of_mul_neg hFg₁ hFg₂ hgg_neg
  have hg_right_pos : 0 < g.eval ((r₀ :: rs').getLast (by lia)) :=
    eval_pos_of_all_roots_lt hg.1 hg.2 hg_pos hroots_g_lt_last
  have hF_right_neg : F.eval ((r₀ :: rs').getLast (by lia)) < 0 := by
    have hprod := hroot_sign ((r₀ :: rs').getLast (by lia)) hlast_root
    nlinarith
  have hF_ne : F ≠ 0 := hF_pos.ne_zero
  have hF_natdeg_pos : 0 < F.natDegree := by lia
  have hF_deg_pos : 0 < F.degree := natDegree_pos_iff_degree_pos.mp hF_natdeg_pos
  have hright :
      ∃ uR, F.IsRoot uR ∧ ∀ r ∈ (r₀ :: rs'), r < uR := by
    have ht : Tendsto (fun x => F.eval x) atTop atTop :=
      F.tendsto_atTop_of_leadingCoeff_nonneg hF_deg_pos hF_pos.le
    obtain ⟨uR, huR_ge, huR_root⟩ :=
      exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop (le_of_lt hF_right_neg) ht
    have hlast_lt_uR : (r₀ :: rs').getLast hrs_ne < uR := by
      refine lt_of_le_of_ne huR_ge ?_
      intro hEq
      simp_all
    refine ⟨uR, huR_root, ?_⟩
    intro r hr
    exact lt_of_le_of_lt (hrs_sorted.rel_getLast hr) hlast_lt_uR
  exact prec_same_of_strict_signs_of_right_root hf.1 hf.2 hF_ne hrs_sorted hrs_eq
    hdeg hn hsign hright

/-- Transport a same-degree Liu--Wang root-sign certificate backward through a
continuous polynomial family that never vanishes at a root of the fixed
polynomial. -/
theorem prec_of_interlaces_endpoint_sign_of_no_crossing
    {f g : ℝ[X]} {p : ℝ → ℝ[X]} {a b : ℝ}
    (hgf : Interlaces g f) (hg_pos : HasPosLeadingCoeff g)
    (hpa_pos : HasPosLeadingCoeff (p a))
    (hdeg : (p a).natDegree = f.natDegree) (hab : a ≤ b)
    (hcont : ∀ r, f.IsRoot r →
      ContinuousOn (fun t ↦ (p t).eval r) (Set.Icc a b))
    (hne : ∀ r, f.IsRoot r → ∀ t ∈ Set.Icc a b, (p t).eval r ≠ 0)
    (hend : ∀ r, f.IsRoot r → (p b).eval r * g.eval r < 0) :
    Prec f (p a) := by
  apply prec_of_interlaces_eval_mul_neg_same hgf hg_pos hpa_pos hdeg
  intro r hr
  have hsame : 0 < (p a).eval r * (p b).eval r :=
    eval_endpoint_pos_of_forall_ne_zero hab (hcont r hr) (hne r hr)
  have hfinal := hend r hr
  rcases mul_pos_iff.mp hsame with ⟨ha_pos, hb_pos⟩ | ⟨ha_neg, hb_neg⟩
  · rcases mul_neg_iff.mp hfinal with ⟨_, hg_neg⟩ | ⟨hb_neg, _⟩
    · exact mul_neg_of_pos_of_neg ha_pos hg_neg
    · linarith
  · rcases mul_neg_iff.mp hfinal with ⟨hb_pos, _⟩ | ⟨_, hg_pos⟩
    · linarith
    · exact mul_neg_of_neg_of_pos ha_neg hg_pos

lemma eval_mul_derivative_eq_of_isRoot {f u v : ℝ[X]} {r : ℝ}
    (hr : f.IsRoot r) :
    (u * f + v * f.derivative).eval r * f.derivative.eval r =
      v.eval r * (f.derivative.eval r) ^ 2 := by
  have hf0 : f.eval r = 0 := by simp_all
  calc
    (u * f + v * f.derivative).eval r * f.derivative.eval r
      = ((u.eval r * f.eval r) + v.eval r * f.derivative.eval r) * f.derivative.eval r := by
          simp [eval_add, eval_mul]
    _ = (v.eval r * f.derivative.eval r) * f.derivative.eval r := by simp [hf0]
    _ = v.eval r * (f.derivative.eval r) ^ 2 := by ring

lemma eval_mul_right_eq_of_isRoot {f g a b : ℝ[X]} {r : ℝ}
    (hr : f.IsRoot r) :
    (a * f + b * g).eval r * g.eval r =
      b.eval r * (g.eval r) ^ 2 := by
  have hf0 : f.eval r = 0 := by simp_all
  calc
    (a * f + b * g).eval r * g.eval r
      = ((a.eval r * f.eval r) + b.eval r * g.eval r) * g.eval r := by simp [eval_add, eval_mul]
    _ = (b.eval r * g.eval r) * g.eval r := by simp [hf0]
    _ = b.eval r * (g.eval r) ^ 2 := by ring

lemma eval_mul_right_nonpos_of_isRoot {f g a b : ℝ[X]} {r : ℝ}
    (hr : f.IsRoot r) (hb : b.eval r ≤ 0) :
    (a * f + b * g).eval r * g.eval r ≤ 0 := by
  rw [eval_mul_right_eq_of_isRoot hr]
  have hsq : 0 ≤ (g.eval r) ^ 2 := sq_nonneg (g.eval r)
  exact mul_nonpos_of_nonpos_of_nonneg hb hsq

lemma eval_mul_right_neg_of_isRoot_of_eval_neg_of_not_isRoot
    {f g a b : ℝ[X]} {r : ℝ}
    (hr : f.IsRoot r) (hb : b.eval r < 0) (hg : ¬ g.IsRoot r) :
    (a * f + b * g).eval r * g.eval r < 0 := by
  rw [eval_mul_right_eq_of_isRoot hr]
  have hg_ne : g.eval r ≠ 0 := by simp_all
  have hsq : 0 < (g.eval r) ^ 2 :=
    sq_pos_iff.mpr hg_ne
  exact mul_neg_of_neg_of_pos hb hsq

/-- Structured Liu--Wang differ-by-1 theorem: if `g ⊳ f`, the combination
`a * f + b * g` has degree `deg(f)+1` and positive leading coefficient, `b` is
strictly negative at roots of `f`, and `f` and `g` have no common roots, then
`f ⊳ a * f + b * g`. -/
theorem prec_of_interlaces_evalCoeff_neg_succ
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg : (a * f + b * g).natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + b * g) := by
  refine prec_of_interlaces_eval_mul_neg_succ hgf hg_pos hF_pos hdeg ?_
  intro r hr
  exact eval_mul_right_neg_of_isRoot_of_eval_neg_of_not_isRoot hr (hb_neg r hr) (hno r hr)

/-- Structured Liu--Wang same-degree theorem: if `g ⊳ f`, the combination
`a * f + b * g` has the same degree as `f` and positive leading coefficient,
`b` is strictly negative at roots of `f`, and `f` and `g` have no common
roots, then `f ≺ a * f + b * g`. -/
theorem prec_of_interlaces_evalCoeff_neg_same
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg : (a * f + b * g).natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + b * g) := by
  refine prec_of_interlaces_eval_mul_neg_same hgf hg_pos hF_pos hdeg ?_
  intro r hr
  exact eval_mul_right_neg_of_isRoot_of_eval_neg_of_not_isRoot hr (hb_neg r hr) (hno r hr)

/-- Degree-bounded structured Liu--Wang theorem in the strict-sign/no-common
regime. -/
theorem prec_of_interlaces_evalCoeff_neg
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + b * g) := by
  have hcases :
      (a * f + b * g).natDegree = f.natDegree ∨
        (a * f + b * g).natDegree = f.natDegree + 1 := by
    lia
  rcases hcases with hsame | hsucc
  · exact prec_of_interlaces_evalCoeff_neg_same hgf hg_pos hF_pos hsame hno hb_neg
  · exact prec_of_interlaces_evalCoeff_neg_succ hgf hg_pos hF_pos hsucc hno hb_neg

lemma interlaces_of_interlaces_X_sub_C_mul {f g : ℝ[X]} {r : ℝ}
    (h : Interlaces ((X - C r) * g) ((X - C r) * f)) :
    Interlaces g f := by
  have hprec : Prec ((X - C r) * g) ((X - C r) * f) := h.toPrec
  have hprec' : Prec g f := prec_of_prec_mul_X_sub_C_both r hprec
  obtain ⟨hf_mul, hg_mul, hdeg_mul, _, _, _, _, _, _, _⟩ := h
  have hf0 : f ≠ 0 := right_ne_zero_of_mul hf_mul.1
  have hg0 : g ≠ 0 := right_ne_zero_of_mul hg_mul.1
  have hdeg : g.natDegree + 1 = f.natDegree := by
    rw [natDegree_mul (X_sub_C_ne_zero r) hg0, natDegree_X_sub_C,
      natDegree_mul (X_sub_C_ne_zero r) hf0, natDegree_X_sub_C] at hdeg_mul
    lia
  exact hprec'.toInterlaces hdeg

lemma isRoot_add_mul_of_common_root {f g a b : ℝ[X]} {r : ℝ}
    (hrf : f.IsRoot r) (hrg : g.IsRoot r) :
    (a * f + b * g).IsRoot r := by
  simp_all

lemma add_mul_factor_X_sub_C {a b qf qg : ℝ[X]} {r : ℝ} :
    a * ((X - C r) * qf) + b * ((X - C r) * qg) =
      (X - C r) * (a * qf + b * qg) := by
  ring

/-- If a structured Liu--Wang quotient already satisfies the desired `Prec`
conclusion, multiplying everything by a common linear factor preserves it. This
is the multiplication-back step for common-root reductions. -/
lemma prec_mul_X_sub_C_of_linearCombo_quotient
    {qf qg a b : ℝ[X]} {r : ℝ}
    (hprec : Prec qf (a * qf + b * qg)) :
    Prec ((X - C r) * qf) (a * ((X - C r) * qf) + b * ((X - C r) * qg)) := by
  have hmul :
      Prec ((X - C r) * qf) ((X - C r) * (a * qf + b * qg)) :=
    prec_mul_common_factor (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hprec
  simpa [add_mul_factor_X_sub_C, add_comm, add_left_comm, add_assoc] using hmul

lemma common_root_reduction_data
    {f g a b : ℝ[X]} {r : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hb_nonpos : ∀ s, f.IsRoot s → b.eval s ≤ 0)
    (hrf : f.IsRoot r) (hrg : g.IsRoot r) :
    ∃ qf qg,
      f = (X - C r) * qf ∧
      g = (X - C r) * qg ∧
      Interlaces qg qf ∧
      HasPosLeadingCoeff qg ∧
      HasPosLeadingCoeff (a * qf + b * qg) ∧
      qf.natDegree ≤ (a * qf + b * qg).natDegree ∧
      (a * qf + b * qg).natDegree ≤ qf.natDegree + 1 ∧
      (∀ s, qf.IsRoot s → b.eval s ≤ 0) := by
  have hgf' : Interlaces g f := hgf
  obtain ⟨hf, hg, _, _, _, _, _, _, _, _⟩ := hgf
  obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hrf
  obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hrg
  refine ⟨qf, qg, hqf, hqg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hmul : Interlaces ((X - C r) * qg) ((X - C r) * qf) := by lia
    exact interlaces_of_interlaces_X_sub_C_mul hmul
  · apply hasPosLeadingCoeff_of_X_sub_C_mul (r := r)
    lia
  · apply hasPosLeadingCoeff_of_X_sub_C_mul (r := r)
    grind
  · have hf_ne : f ≠ 0 := hf.1
    have hF_ne : a * f + b * g ≠ 0 := hF_pos.ne_zero
    have hqf_ne : qf ≠ 0 := by simp_all
    have hFq_ne : a * qf + b * qg ≠ 0 := by grind
    rw [hqf, hqg, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
      add_mul_factor_X_sub_C,
      natDegree_mul (X_sub_C_ne_zero r) hFq_ne, natDegree_X_sub_C] at hdeg_lo
    lia
  · have hf_ne : f ≠ 0 := hf.1
    have hF_ne : a * f + b * g ≠ 0 := hF_pos.ne_zero
    have hqf_ne : qf ≠ 0 := by simp_all
    have hFq_ne : a * qf + b * qg ≠ 0 := by grind
    rw [hqf, hqg, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
      add_mul_factor_X_sub_C,
      natDegree_mul (X_sub_C_ne_zero r) hFq_ne, natDegree_X_sub_C] at hdeg_hi
    lia
  · simp_all

lemma natDegree_lt_of_interlaces_degree_lower_bound {f g F : ℝ[X]}
    (hgf : Interlaces g f) (hdeg_lo : f.natDegree ≤ F.natDegree) :
    g.natDegree < F.natDegree := by
  obtain ⟨_, _, hdeg, _, _, _, _, _, _, _⟩ := hgf
  lia

lemma natDegree_sub_C_mul_eq_of_interlaces_degree_lower_bound
    {f g F : ℝ[X]} (hgf : Interlaces g f) (hdeg_lo : f.natDegree ≤ F.natDegree) (c : ℝ) :
    (F - C c * g).natDegree = F.natDegree :=
  natDegree_sub_eq_left_of_natDegree_lt
    ((natDegree_C_mul_le c g).trans_lt
      (natDegree_lt_of_interlaces_degree_lower_bound hgf hdeg_lo))

lemma hasPosLeadingCoeff_sub_C_mul_of_interlaces_degree_lower_bound
    {f g F : ℝ[X]} (hgf : Interlaces g f) (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hF_pos : HasPosLeadingCoeff F) (c : ℝ) :
    HasPosLeadingCoeff (F - C c * g) := by
  unfold HasPosLeadingCoeff at hF_pos ⊢
  have hlt : degree (C c * g) < degree F :=
    degree_lt_degree <|
      (natDegree_C_mul_le c g).trans_lt
        (natDegree_lt_of_interlaces_degree_lower_bound hgf hdeg_lo)
  rw [leadingCoeff_sub_of_degree_lt hlt]
  lia

end RealRooted.MaWangInternal

namespace RealRooted

export MaWangInternal
  (prec_of_interlaces_eval_mul_neg_succ
    prec_of_interlaces_eval_mul_neg_same
    prec_of_interlaces_endpoint_sign_of_no_crossing
    prec_of_interlaces_evalCoeff_neg_succ
    prec_of_interlaces_evalCoeff_neg_same
    prec_of_interlaces_evalCoeff_neg
    natDegree_sub_C_mul_eq_of_interlaces_degree_lower_bound
    hasPosLeadingCoeff_sub_C_mul_of_interlaces_degree_lower_bound)

end RealRooted
