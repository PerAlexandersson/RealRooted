import RealRooted.MaWang.StrictSigns

open Polynomial Filter

noncomputable section

namespace RealRooted.MaWangInternal

/-- Liu--Wang differ-by-1 form: if `g ⊳ f`, `F` has degree `deg(f)+1`, positive
leading coefficient, and at every root `r` of `f` the value `F(r)` has the
opposite sign from `g(r)`, then `f ⊳ F`. -/
theorem strictInterl_of_interlaces_eval_mul_neg_succ {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg : F.natDegree = f.natDegree + 1)
    (hroot_sign : ∀ r, f.IsRoot r → F.eval r * g.eval r < 0) :
    StrictInterl f F := by
  obtain ⟨hf, hg, hgdeg, rs, ss, hrs_sorted, hss_sorted, hrs_eq, hss_eq, hint⟩ := hgf
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf.2]
  have hn : 1 ≤ rs.length := by lia
  have hrs_ne : rs ≠ [] := by grind
  obtain ⟨r₀, rs', rfl⟩ := List.exists_cons_of_ne_nil hrs_ne
  have hr₀_root : f.IsRoot r₀ :=
    (mem_roots hf.1).mp (by rw [← hrs_eq]; simp)
  have hlast_root : f.IsRoot ((r₀ :: rs').getLast (by lia)) :=
    (mem_roots hf.1).mp (by rw [← hrs_eq]; simp)
  have hno_g_at_f : ∀ r, f.IsRoot r → ¬ g.IsRoot r := fun r hr hgr ↦ by
    simpa [hgr.eq_zero] using hroot_sign r hr
  have hhead_lt_roots_g : ∀ t ∈ g.roots, r₀ < t := by
    intro t ht
    have ht_ss : t ∈ ss := Multiset.mem_coe.mp (by simpa [hss_eq] using ht)
    have hr₀_le_t : r₀ ≤ t := listInterlaces_all_ge ss rs' r₀ hint t ht_ss
    have ht_root : g.IsRoot t := (mem_roots hg.1).mp ht
    grind
  have hroots_g_lt_last : ∀ t ∈ g.roots, t < (r₀ :: rs').getLast (by lia) := by
    intro t ht
    have ht_ss : t ∈ ss := Multiset.mem_coe.mp (by simpa [hss_eq] using ht)
    have ht_le_last : t ≤ (r₀ :: rs').getLast (by lia) :=
      listInterlaces_all_le_getLast (rs := r₀ :: rs') (by lia) hrs_sorted hint t ht_ss
    have ht_root : g.IsRoot t := (mem_roots hg.1).mp ht
    grind
  have hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        (r₀ :: rs') = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    intro pre r₁ r₂ rest hEq
    have hr₁_root : f.IsRoot r₁ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq
    have hEq_next : r₀ :: rs' = (pre ++ [r₁]) ++ r₂ :: rest := by simp_all
    have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
    have hFg₁ : F.eval r₁ * g.eval r₁ < 0 := hroot_sign r₁ hr₁_root
    have hFg₂ : F.eval r₂ * g.eval r₂ < 0 := hroot_sign r₂ hr₂_root
    have hgg_nonpos : g.eval r₁ * g.eval r₂ ≤ 0 :=
      eval_mul_eval_nonpos_of_interlacing_consecutive hg.2 hrs_sorted hss_eq hint hEq
    have hg₁_ne : g.eval r₁ ≠ 0 := by simp_all
    have hg₂_ne : g.eval r₂ ≠ 0 := by simp_all
    have hgg_neg := lt_of_le_of_ne hgg_nonpos (mul_ne_zero hg₁_ne hg₂_ne)
    exact mul_neg_of_mul_neg_of_mul_neg hFg₁ hFg₂ hgg_neg
  rcases Nat.even_or_odd f.natDegree with hf_even | hf_odd
  · have hg_odd : Odd g.natDegree := by grind
    have hg_left_neg : g.eval r₀ < 0 :=
      eval_neg_of_all_roots_gt_of_odd hg.1 hg_pos hg_odd hhead_lt_roots_g
    have hF_left_pos : 0 < F.eval r₀ := by nlinarith [hroot_sign r₀ hr₀_root]
    have hg_right_pos : 0 < g.eval ((r₀ :: rs').getLast (by lia)) :=
      eval_pos_of_all_roots_lt hg.1 hg.2 hg_pos hroots_g_lt_last
    have hF_right_neg : F.eval ((r₀ :: rs').getLast (by lia)) < 0 := by
      nlinarith [hroot_sign ((r₀ :: rs').getLast (by lia)) hlast_root]
    exact
      strictInterl_of_strict_signs_of_endSigns_even
        hf.1 hf.2 hF_pos hrs_sorted hrs_eq hdeg hn hf_even
      hsign hF_left_pos hF_right_neg
  · have hg_even : Even g.natDegree := by grind
    have hg_left_pos : 0 < g.eval r₀ :=
      eval_pos_of_all_roots_gt_of_even hg.1 hg_pos hg_even hhead_lt_roots_g
    have hF_left_neg : F.eval r₀ < 0 := by nlinarith [hroot_sign r₀ hr₀_root]
    have hg_right_pos : 0 < g.eval ((r₀ :: rs').getLast (by lia)) :=
      eval_pos_of_all_roots_lt hg.1 hg.2 hg_pos hroots_g_lt_last
    have hF_right_neg : F.eval ((r₀ :: rs').getLast (by lia)) < 0 := by
      nlinarith [hroot_sign ((r₀ :: rs').getLast (by lia)) hlast_root]
    exact
      strictInterl_of_strict_signs_of_endSigns_odd
        hf.1 hf.2 hF_pos hrs_sorted hrs_eq hdeg hn hf_odd
      hsign hF_left_neg hF_right_neg

/-- Liu--Wang same-degree form: if `g ⊳ f`, `F` has the same degree as `f`,
positive leading coefficient, and at every root `r` of `f` the value `F(r)`
has the opposite sign from `g(r)`, then `f ≺ F` in the same-degree sense. -/
theorem strictInterl_of_interlaces_eval_mul_neg_same {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg : F.natDegree = f.natDegree)
    (hroot_sign : ∀ r, f.IsRoot r → F.eval r * g.eval r < 0) :
    StrictInterl f F := by
  obtain ⟨hf, hg, hgdeg, rs, ss, hrs_sorted, hss_sorted, hrs_eq, hss_eq, hint⟩ := hgf
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf.2]
  have hn : 1 ≤ rs.length := by lia
  have hrs_ne : rs ≠ [] := by grind
  obtain ⟨r₀, rs', rfl⟩ := List.exists_cons_of_ne_nil hrs_ne
  have hlast_root : f.IsRoot ((r₀ :: rs').getLast (by lia)) :=
    (mem_roots hf.1).mp (by rw [← hrs_eq]; simp)
  have hno_g_at_f : ∀ r, f.IsRoot r → ¬ g.IsRoot r := fun r hr hgr ↦ by
    simpa [hgr.eq_zero] using hroot_sign r hr
  have hroots_g_lt_last : ∀ t ∈ g.roots, t < (r₀ :: rs').getLast (by lia) := by
    intro t ht
    have ht_ss : t ∈ ss := Multiset.mem_coe.mp (by simpa [hss_eq] using ht)
    have ht_le_last : t ≤ (r₀ :: rs').getLast (by lia) :=
      listInterlaces_all_le_getLast (rs := r₀ :: rs') (by lia) hrs_sorted hint t ht_ss
    have ht_root : g.IsRoot t := (mem_roots hg.1).mp ht
    grind
  have hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        (r₀ :: rs') = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    intro pre r₁ r₂ rest hEq
    have hr₁_root : f.IsRoot r₁ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq
    have hEq_next : r₀ :: rs' = (pre ++ [r₁]) ++ r₂ :: rest := by simp_all
    have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
    have hFg₁ : F.eval r₁ * g.eval r₁ < 0 := hroot_sign r₁ hr₁_root
    have hFg₂ : F.eval r₂ * g.eval r₂ < 0 := hroot_sign r₂ hr₂_root
    have hgg_nonpos : g.eval r₁ * g.eval r₂ ≤ 0 :=
      eval_mul_eval_nonpos_of_interlacing_consecutive hg.2 hrs_sorted hss_eq hint hEq
    have hg₁_ne : g.eval r₁ ≠ 0 := by simp_all
    have hg₂_ne : g.eval r₂ ≠ 0 := by simp_all
    have hgg_neg := lt_of_le_of_ne hgg_nonpos (mul_ne_zero hg₁_ne hg₂_ne)
    exact mul_neg_of_mul_neg_of_mul_neg hFg₁ hFg₂ hgg_neg
  have hg_right_pos : 0 < g.eval ((r₀ :: rs').getLast (by lia)) :=
    eval_pos_of_all_roots_lt hg.1 hg.2 hg_pos hroots_g_lt_last
  have hF_right_neg : F.eval ((r₀ :: rs').getLast (by lia)) < 0 := by
    nlinarith [hroot_sign ((r₀ :: rs').getLast (by lia)) hlast_root]
  have hF_ne : F ≠ 0 := hF_pos.ne_zero
  have hF_deg_pos : 0 < F.degree := natDegree_pos_iff_degree_pos.mp (by lia)
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
  exact strictInterl_same_of_strict_signs_of_right_root hf.1 hf.2 hF_ne hrs_sorted hrs_eq
    hdeg hn hsign hright

/-- Transport a same-degree Liu--Wang root-sign certificate backward through a
continuous polynomial family that never vanishes at a root of the fixed
polynomial. -/
theorem strictInterl_of_interlaces_endpoint_sign_of_no_crossing
    {f g : ℝ[X]} {p : ℝ → ℝ[X]} {a b : ℝ}
    (hgf : Interlaces g f) (hg_pos : HasPosLeadingCoeff g)
    (hpa_pos : HasPosLeadingCoeff (p a))
    (hdeg : (p a).natDegree = f.natDegree) (hab : a ≤ b)
    (hcont : ∀ r, f.IsRoot r →
      ContinuousOn (fun t ↦ (p t).eval r) (Set.Icc a b))
    (hne : ∀ r, f.IsRoot r → ∀ t ∈ Set.Icc a b, (p t).eval r ≠ 0)
    (hend : ∀ r, f.IsRoot r → (p b).eval r * g.eval r < 0) :
    StrictInterl f (p a) := by
  apply strictInterl_of_interlaces_eval_mul_neg_same hgf hg_pos hpa_pos hdeg
  intro r hr
  have hsame : 0 < (p a).eval r * (p b).eval r :=
    eval_endpoint_pos_of_forall_ne_zero hab (hcont r hr) (hne r hr)
  have hfinal := hend r hr
  rcases mul_pos_iff.mp hsame with ⟨ha_pos, hb_pos⟩ | ⟨ha_neg, hb_neg⟩
  · rcases mul_neg_iff.mp hfinal with ⟨_, hg_neg⟩ | ⟨hb_neg, _⟩ <;> nlinarith
  · rcases mul_neg_iff.mp hfinal with ⟨hb_pos, _⟩ | ⟨_, hg_pos⟩ <;> nlinarith

lemma eval_mul_derivative_eq_of_isRoot {f u v : ℝ[X]} {r : ℝ}
    (hr : f.IsRoot r) :
    (u * f + v * f.derivative).eval r * f.derivative.eval r =
      v.eval r * (f.derivative.eval r) ^ 2 := by
  simp only [eval_add, eval_mul, hr.eq_zero, mul_zero, zero_add]
  ring

lemma eval_mul_right_eq_of_isRoot {f g a b : ℝ[X]} {r : ℝ}
    (hr : f.IsRoot r) :
    (a * f + b * g).eval r * g.eval r =
      b.eval r * (g.eval r) ^ 2 := by
  simp only [eval_add, eval_mul, hr.eq_zero, mul_zero, zero_add]
  ring

lemma eval_mul_right_neg_of_isRoot_of_eval_neg_of_not_isRoot
    {f g a b : ℝ[X]} {r : ℝ}
    (hr : f.IsRoot r) (hb : b.eval r < 0) (hg : ¬ g.IsRoot r) :
    (a * f + b * g).eval r * g.eval r < 0 := by
  rw [eval_mul_right_eq_of_isRoot hr]
  have hg_ne : g.eval r ≠ 0 := by simp_all
  exact mul_neg_of_neg_of_pos hb (sq_pos_iff.mpr hg_ne)

/-- Structured Liu--Wang differ-by-1 theorem: if `g ⊳ f`, the combination
`a * f + b * g` has degree `deg(f)+1` and positive leading coefficient, `b` is
strictly negative at roots of `f`, and `f` and `g` have no common roots, then
`f ⊳ a * f + b * g`. -/
theorem strictInterl_of_interlaces_evalCoeff_neg_succ
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg : (a * f + b * g).natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    StrictInterl f (a * f + b * g) :=
  strictInterl_of_interlaces_eval_mul_neg_succ hgf hg_pos hF_pos hdeg fun r hr ↦
    eval_mul_right_neg_of_isRoot_of_eval_neg_of_not_isRoot hr (hb_neg r hr) (hno r hr)

/-- Structured Liu--Wang same-degree theorem: if `g ⊳ f`, the combination
`a * f + b * g` has the same degree as `f` and positive leading coefficient,
`b` is strictly negative at roots of `f`, and `f` and `g` have no common
roots, then `f ≺ a * f + b * g`. -/
theorem strictInterl_of_interlaces_evalCoeff_neg_same
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg : (a * f + b * g).natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    StrictInterl f (a * f + b * g) :=
  strictInterl_of_interlaces_eval_mul_neg_same hgf hg_pos hF_pos hdeg fun r hr ↦
    eval_mul_right_neg_of_isRoot_of_eval_neg_of_not_isRoot hr (hb_neg r hr) (hno r hr)

/-- Degree-bounded structured Liu--Wang theorem in the strict-sign/no-common
regime. -/
theorem strictInterl_of_interlaces_evalCoeff_neg
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    StrictInterl f (a * f + b * g) := by
  rcases Nat.le_and_le_add_one_iff.mp ⟨hdeg_lo, hdeg_hi⟩ with hsame | hsucc
  · exact strictInterl_of_interlaces_evalCoeff_neg_same hgf hg_pos hF_pos hsame hno hb_neg
  · exact strictInterl_of_interlaces_evalCoeff_neg_succ hgf hg_pos hF_pos hsucc hno hb_neg

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
  have hlt : degree (C c * g) < degree F :=
    degree_lt_degree <|
      (natDegree_C_mul_le c g).trans_lt
        (natDegree_lt_of_interlaces_degree_lower_bound hgf hdeg_lo)
  simpa only [HasPosLeadingCoeff, leadingCoeff_sub_of_degree_lt hlt] using hF_pos

end RealRooted.MaWangInternal

namespace RealRooted

export MaWangInternal
  (strictInterl_of_interlaces_eval_mul_neg_succ
    strictInterl_of_interlaces_eval_mul_neg_same
    strictInterl_of_interlaces_endpoint_sign_of_no_crossing
    strictInterl_of_interlaces_evalCoeff_neg_succ
    strictInterl_of_interlaces_evalCoeff_neg_same
    strictInterl_of_interlaces_evalCoeff_neg
    natDegree_sub_C_mul_eq_of_interlaces_degree_lower_bound
    hasPosLeadingCoeff_sub_C_mul_of_interlaces_degree_lower_bound)

end RealRooted

namespace RealRooted

/-- Root-sign test for strict interlacing.  Let `f` be real-rooted of positive degree and positive
leading coefficient, and let `g` have nonnegative coefficients, positive constant term and
degree `deg f` or `deg f + 1`.  If `g(r) f'(r) < 0` at every root `r` of `f`, then `f` and `g`
strictly interlace, they have no common root, and all roots of `g` are negative.  This is the
sign criterion (Lemma 2.1) of Zhang, SSRN 7510941, built on the Liu--Wang type lemmas
`strictInterl_of_interlaces_eval_mul_neg_same` and `..._succ`. -/
theorem strictInterl_and_noCommonRoot_of_eval_mul_derivative_neg {f g : ℝ[X]}
    (hf : f.Splits) (hfpos : HasPosLeadingCoeff f) (hfdeg : f.natDegree ≠ 0)
    (hg : HasNonnegCoeffs g) (hg0 : 0 < g.coeff 0)
    (hdeg : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1)
    (hsign : ∀ r, f.IsRoot r → g.eval r * f.derivative.eval r < 0) :
    StrictInterl f g ∧ (∀ r, f.IsRoot r → ¬ g.IsRoot r) ∧ ∀ r ∈ g.roots, r < 0 := by
  have hgne : g ≠ 0 := fun h => by simp [h] at hg0
  have hgpos : HasPosLeadingCoeff g := hg.pos_leadingCoeff hgne
  have hfder := interlaces_derivative_of_pos_natDegree hfpos.ne_zero hf hfpos (by lia)
  have hfderpos : HasPosLeadingCoeff f.derivative := hfpos.derivative hfdeg
  have hweak : StrictInterl f g := by
    rcases hdeg with hsame | hsucc
    · exact strictInterl_of_interlaces_eval_mul_neg_same hfder hfderpos hgpos hsame hsign
    · exact strictInterl_of_interlaces_eval_mul_neg_succ hfder hfderpos hgpos hsucc hsign
  have hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r := fun r hr hgr ↦ by
    simpa [hgr.eq_zero] using hsign r hr
  refine ⟨hweak, hno, fun r hr => ?_⟩
  refine lt_of_le_of_ne (roots_nonpos_of_hasNonnegCoeffs hg r hr) fun hrzero => ?_
  have hroot : g.IsRoot r := (mem_roots hgne).mp hr
  rw [hrzero, IsRoot.def, ← coeff_zero_eq_eval_zero] at hroot
  exact hg0.ne' hroot

end RealRooted
