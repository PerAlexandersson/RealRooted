import RealRooted.MaWang.Strong

open Polynomial Filter

noncomputable section

namespace RealRooted.MaWangInternal

/-- Weak-sign Liu--Wang perturbation step: subtracting a small positive constant from the
coefficient of `g` makes the root-sign condition strict, so the strict mixed theorem applies. -/
theorem prec_sub_C_mul_of_interlaces_evalCoeff_nonpos_of_no_common
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    Prec f ((a * f + b * g) - C δ * g) := by
  let F : ℝ[X] := a * f + b * g
  have hdeg_lo' : f.natDegree ≤ F.natDegree := by lia
  have hdeg_hi' : F.natDegree ≤ f.natDegree + 1 := by lia
  have hcases : F.natDegree = f.natDegree ∨ F.natDegree = f.natDegree + 1 := by lia
  have hFδ_pos : HasPosLeadingCoeff (F - C δ * g) :=
    hasPosLeadingCoeff_sub_C_mul_of_interlaces_degree_lower_bound hgf hdeg_lo' hF_pos δ
  have hnat_Fδ : (F - C δ * g).natDegree = F.natDegree :=
    natDegree_sub_C_mul_eq_of_interlaces_degree_lower_bound hgf hdeg_lo' δ
  have hroot_sign : ∀ r, f.IsRoot r → (F - C δ * g).eval r * g.eval r < 0 := by
    intro r hr
    have hbδ : (b - C δ).eval r < 0 := by
      rw [Polynomial.eval_sub, Polynomial.eval_C]
      grind
    have hEq : F - C δ * g = a * f + (b - C δ) * g := by
      simp [F, sub_eq_add_neg, add_assoc, right_distrib]
    rw [hEq]
    exact eval_mul_right_neg_of_isRoot_of_eval_neg_of_not_isRoot hr hbδ (hno r hr)
  rcases hcases with hsame | hsucc
  · have hdeg_same : (F - C δ * g).natDegree = f.natDegree := by lia
    exact prec_of_interlaces_eval_mul_neg_same hgf hg_pos hFδ_pos hdeg_same hroot_sign
  · have hdeg_succ : (F - C δ * g).natDegree = f.natDegree + 1 := by lia
    exact prec_of_interlaces_eval_mul_neg_succ hgf hg_pos hFδ_pos hdeg_succ hroot_sign

/-- Real-rootedness for the perturbed weak-sign Liu--Wang combination. -/
theorem isRealRooted_sub_C_mul_of_interlaces_evalCoeff_nonpos_of_no_common
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    (((a * f + b * g) - C δ * g) ≠ 0 ∧ ((a * f + b * g) - C δ * g).Splits) :=
  (prec_sub_C_mul_of_interlaces_evalCoeff_nonpos_of_no_common
    hgf hg_pos hF_pos hdeg_lo hdeg_hi hno hb_nonpos hδ).2.1
lemma mem_range_of_mem_aroots_of_isRealRooted {p : ℝ[X]}
    (hp_splits : p.Splits)
    {z : ℂ} (hz : z ∈ p.aroots ℂ) :
    z ∈ (algebraMap ℝ ℂ).range := by
  have hmap :
      p.roots.map (algebraMap ℝ ℂ) = p.aroots ℂ := by
    simpa [Polynomial.aroots_def] using
      roots_map_of_injective_of_card_eq_natDegree
        (p := p) (f := algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
        (card_roots_of_splits hp_splits)
  rw [← hmap] at hz
  rcases Multiset.mem_map.mp hz with ⟨x, _, rfl⟩
  simp

/-- Weak-sign Liu--Wang real-rootedness theorem in the no-common-roots regime. -/
theorem isRealRooted_of_interlaces_evalCoeff_nonpos_of_no_common
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    ((a * f + b * g) ≠ 0 ∧ (a * f + b * g).Splits) := by
  let F : ℝ[X] := a * f + b * g
  have hF_ne : F ≠ 0 := by simpa [F] using hF_pos.ne_zero
  have hlc_pos : 0 < F.leadingCoeff := by simpa [F, HasPosLeadingCoeff] using hF_pos
  have hlc_ne : F.leadingCoeff ≠ 0 := ne_of_gt hlc_pos
  let q : ℝ[X] := C F.leadingCoeff⁻¹ * F
  have hq_monic : q.Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hq_ne : q ≠ 0 :=
    mul_ne_zero (by simp [hlc_ne]) hF_ne
  have hf_deg_pos : 0 < f.natDegree := by
    obtain ⟨_, _, hdeg, _, _, _, _, _, _, _⟩ := hgf
    lia
  have hq_deg_pos : 0 < q.natDegree := by
    rw [show q = C F.leadingCoeff⁻¹ * F by grind, natDegree_C_mul (inv_ne_zero hlc_ne)]
    lia
  have hroots_real :
      ∀ z ∈ (q.map (algebraMap ℝ ℂ)).roots, z ∈ (algebraMap ℝ ℂ).range := by
    intro z hz
    by_contra hz_not_real
    have hzim_ne : z.im ≠ 0 := by
      intro hzim
      apply hz_not_real
      refine ⟨z.re, ?_⟩
      apply Complex.ext <;> simp [hzim]
    have hz_aroot : z ∈ q.aroots ℂ := by lia
    have hz_aeval : Polynomial.aeval z q = 0 := by simp_all
    let eps0 : ℝ := |z.im|
    have heps0_pos : 0 < eps0 := abs_pos.mpr hzim_ne
    let R : ℝ := max ‖z‖ 1
    let u : ℝ := eps0 / (2 * R)
    let η : ℝ := u ^ q.natDegree / (q.natDegree + 1)
    let M : ℝ := max 1 (coeffSumRange g)
    let A : ℝ := max 1 (‖F.leadingCoeff⁻¹‖ * M)
    let δ : ℝ := η / (2 * A)
    have hη_pos : 0 < η := by
      unfold η u R eps0
      positivity
    have hδ_pos : 0 < δ := by
      unfold δ A
      positivity
    let qδ : ℝ[X] := C F.leadingCoeff⁻¹ * (F - C δ * g)
    have hFδ_natdeg : (F - C δ * g).natDegree = F.natDegree :=
      natDegree_sub_C_mul_eq_of_interlaces_degree_lower_bound hgf
        (by lia) δ
    have hFδ_lc : (F - C δ * g).leadingCoeff = F.leadingCoeff := by
      have hlt : degree (C δ * g) < degree F :=
        degree_lt_degree <|
          (natDegree_C_mul_le δ g).trans_lt
            (natDegree_lt_of_interlaces_degree_lower_bound hgf (by lia))
      rw [leadingCoeff_sub_of_degree_lt hlt]
    have hqδ_monic : qδ.Monic := by
      apply monic_C_mul_of_mul_leadingCoeff_eq_one
      simp_all
    have hqδ_deg : qδ.natDegree = q.natDegree := by
      rw [show qδ = C F.leadingCoeff⁻¹ * (F - C δ * g) by grind,
        show q = C F.leadingCoeff⁻¹ * F by grind,
        natDegree_C_mul (inv_ne_zero hlc_ne), natDegree_C_mul (inv_ne_zero hlc_ne),
        hFδ_natdeg]
    have hqδ_coeff :
        ∀ i : ℕ, ‖qδ.coeff i - q.coeff i‖ < η := by
      intro i
      have hgi_bound : ‖g.coeff i‖ ≤ M :=
        (coeff_norm_le_coeffSumRange g i).trans (le_max_right _ _)
      have hprod_bound : ‖F.leadingCoeff⁻¹‖ * ‖g.coeff i‖ ≤ A := by
        have hA : ‖F.leadingCoeff⁻¹‖ * M ≤ A := le_max_right _ _
        nlinarith [hgi_bound, norm_nonneg (F.leadingCoeff⁻¹), norm_nonneg (g.coeff i)]
      have hcoeff :
          qδ.coeff i - q.coeff i = -(F.leadingCoeff⁻¹ * (δ * g.coeff i)) := by
        simp [qδ, q, Polynomial.coeff_C_mul]
        ring
      calc
        ‖qδ.coeff i - q.coeff i‖
          = ‖-(F.leadingCoeff⁻¹ * (δ * g.coeff i))‖ := by lia
        _ = ‖F.leadingCoeff⁻¹ * (δ * g.coeff i)‖ := by simp
        _ = ‖F.leadingCoeff⁻¹‖ * ‖δ * g.coeff i‖ := by simp
        _ = ‖F.leadingCoeff⁻¹‖ * (δ * ‖g.coeff i‖) := by
              rw [norm_mul, Real.norm_of_nonneg hδ_pos.le]
        _ = δ * (‖F.leadingCoeff⁻¹‖ * ‖g.coeff i‖) := by ring
        _ ≤ δ * A := by simp_all
        _ = η / 2 := by grind
        _ < η := by simp_all
    obtain ⟨w, hw_mem, hw_close⟩ :=
      Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
        (f := q) (g := qδ) hη_pos hz_aeval hq_monic hqδ_monic hqδ_deg hqδ_coeff
        (IsAlgClosed.splits _)
    have hFδ_rr : ((F - C δ * g) ≠ 0 ∧ (F - C δ * g).Splits) :=
      isRealRooted_sub_C_mul_of_interlaces_evalCoeff_nonpos_of_no_common
        hgf hg_pos hF_pos hdeg_lo hdeg_hi hno hb_nonpos hδ_pos
    have hqδ_rr : (qδ ≠ 0 ∧ qδ.Splits) := by simp_all [qδ]
    rcases mem_range_of_mem_aroots_of_isRealRooted hqδ_rr.2 hw_mem with ⟨x, rfl⟩
    have him_le : eps0 ≤ ‖z - x‖ := by
      unfold eps0
      simpa using (Complex.abs_im_le_norm (z - x))
    have hR_pos : 0 < R := by grind
    have hbound_eq :
        (((q.natDegree : ℝ) + 1) * η) ^ ((q.natDegree : ℝ)⁻¹) * R = eps0 / 2 := by
      have hdeg_ne : q.natDegree ≠ 0 := by lia
      have hu_nonneg : 0 ≤ u := by
        unfold u eps0 R
        positivity
      calc
        (((q.natDegree : ℝ) + 1) * η) ^ ((q.natDegree : ℝ)⁻¹) * R
            = (((q.natDegree : ℝ) + 1) * (u ^ q.natDegree / ((q.natDegree : ℝ) + 1)))
                ^ ((q.natDegree : ℝ)⁻¹) * R := by lia
        _ = (u ^ q.natDegree) ^ ((q.natDegree : ℝ)⁻¹) * R := by grind
        _ = u * R := by rw [Real.pow_rpow_inv_natCast hu_nonneg hdeg_ne]
        _ = eps0 / 2 := by grind
    have hclose_eps : ‖z - x‖ < eps0 := by
      calc
        ‖z - x‖ < (((q.natDegree : ℝ) + 1) * η) ^ ((q.natDegree : ℝ)⁻¹) * R := hw_close
        _ = eps0 / 2 := hbound_eq
        _ < eps0 := by simp_all
    grind
  have hq_split : q.Splits :=
    Polynomial.Splits.of_splits_map (i := algebraMap ℝ ℂ)
      (IsAlgClosed.splits _) hroots_real
  have hq_rr : (q ≠ 0 ∧ q.Splits) := by lia
  have hF_eq : C F.leadingCoeff * q = F := by
    unfold q
    calc
      C F.leadingCoeff * (C F.leadingCoeff⁻¹ * F)
          = (C F.leadingCoeff * C F.leadingCoeff⁻¹) * F := by grind
      _ = C (F.leadingCoeff * F.leadingCoeff⁻¹) * F := by simp
      _ = F := by simp [hlc_ne]
  have hF_rr : (F ≠ 0 ∧ F.Splits) := by
    rw [← hF_eq]
    simp_all [-hF_eq]
  lia

/-- If every positive perturbation `F - C δ * g` is real-rooted, then `F` is
real-rooted as well. The interlacing hypothesis is only used to keep the degree
and leading coefficient stable under the subtraction. -/
theorem isRealRooted_of_interlaces_sub_C_mul_of_forall_pos
    {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hsub_rr : ∀ {δ : ℝ}, 0 < δ → ((F - C δ * g) ≠ 0 ∧ (F - C δ * g).Splits)) :
    F ≠ 0 ∧ F.Splits := by
  have hF_ne : F ≠ 0 := hF_pos.ne_zero
  have hlc_pos : 0 < F.leadingCoeff := by simpa [HasPosLeadingCoeff] using hF_pos
  have hlc_ne : F.leadingCoeff ≠ 0 := ne_of_gt hlc_pos
  let q : ℝ[X] := C F.leadingCoeff⁻¹ * F
  have hq_monic : q.Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hq_ne : q ≠ 0 :=
    mul_ne_zero (by simp [hlc_ne]) hF_ne
  have hq_deg_pos : 0 < q.natDegree := by
    rw [show q = C F.leadingCoeff⁻¹ * F by grind, natDegree_C_mul (inv_ne_zero hlc_ne)]
    have hF_deg_pos : 0 < F.natDegree := by
      obtain ⟨_, _, hdeg, _, _, _, _, _, _, _⟩ := hgf
      lia
    lia
  have hroots_real :
      ∀ z ∈ (q.map (algebraMap ℝ ℂ)).roots, z ∈ (algebraMap ℝ ℂ).range := by
    intro z hz
    by_contra hz_not_real
    have hzim_ne : z.im ≠ 0 := by
      intro hzim
      apply hz_not_real
      refine ⟨z.re, ?_⟩
      apply Complex.ext <;> simp [hzim]
    have hz_aroot : z ∈ q.aroots ℂ := by lia
    have hz_aeval : Polynomial.aeval z q = 0 := by simp_all
    let eps0 : ℝ := |z.im|
    have heps0_pos : 0 < eps0 := abs_pos.mpr hzim_ne
    let R : ℝ := max ‖z‖ 1
    let u : ℝ := eps0 / (2 * R)
    let η : ℝ := u ^ q.natDegree / (q.natDegree + 1)
    let M : ℝ := max 1 (coeffSumRange g)
    let A : ℝ := max 1 (‖F.leadingCoeff⁻¹‖ * M)
    let δ : ℝ := η / (2 * A)
    have hη_pos : 0 < η := by
      unfold η u R eps0
      positivity
    have hδ_pos : 0 < δ := by
      unfold δ A
      positivity
    let qδ : ℝ[X] := C F.leadingCoeff⁻¹ * (F - C δ * g)
    have hFδ_natdeg : (F - C δ * g).natDegree = F.natDegree :=
      natDegree_sub_C_mul_eq_of_interlaces_degree_lower_bound hgf hdeg_lo δ
    have hFδ_lc : (F - C δ * g).leadingCoeff = F.leadingCoeff := by
      have hlt : degree (C δ * g) < degree F :=
        degree_lt_degree <|
          (natDegree_C_mul_le δ g).trans_lt
            (natDegree_lt_of_interlaces_degree_lower_bound hgf hdeg_lo)
      rw [leadingCoeff_sub_of_degree_lt hlt]
    have hqδ_monic : qδ.Monic := by
      apply monic_C_mul_of_mul_leadingCoeff_eq_one
      simp_all
    have hqδ_deg : qδ.natDegree = q.natDegree := by
      rw [show qδ = C F.leadingCoeff⁻¹ * (F - C δ * g) by grind,
        show q = C F.leadingCoeff⁻¹ * F by grind,
        natDegree_C_mul (inv_ne_zero hlc_ne), natDegree_C_mul (inv_ne_zero hlc_ne),
        hFδ_natdeg]
    have hqδ_coeff :
        ∀ i : ℕ, ‖qδ.coeff i - q.coeff i‖ < η := by
      intro i
      have hgi_bound : ‖g.coeff i‖ ≤ M :=
        (coeff_norm_le_coeffSumRange g i).trans (le_max_right _ _)
      have hprod_bound : ‖F.leadingCoeff⁻¹‖ * ‖g.coeff i‖ ≤ A := by
        have hA : ‖F.leadingCoeff⁻¹‖ * M ≤ A := le_max_right _ _
        nlinarith [hgi_bound, norm_nonneg (F.leadingCoeff⁻¹), norm_nonneg (g.coeff i)]
      have hcoeff :
          qδ.coeff i - q.coeff i = -(F.leadingCoeff⁻¹ * (δ * g.coeff i)) := by
        simp [qδ, q, Polynomial.coeff_C_mul]
        ring
      calc
        ‖qδ.coeff i - q.coeff i‖
          = ‖-(F.leadingCoeff⁻¹ * (δ * g.coeff i))‖ := by lia
        _ = ‖F.leadingCoeff⁻¹ * (δ * g.coeff i)‖ := by simp
        _ = ‖F.leadingCoeff⁻¹‖ * ‖δ * g.coeff i‖ := by simp
        _ = ‖F.leadingCoeff⁻¹‖ * (δ * ‖g.coeff i‖) := by
              rw [norm_mul, Real.norm_of_nonneg hδ_pos.le]
        _ = δ * (‖F.leadingCoeff⁻¹‖ * ‖g.coeff i‖) := by ring
        _ ≤ δ * A := by simp_all
        _ = η / 2 := by grind
        _ < η := by simp_all
    obtain ⟨w, hw_mem, hw_close⟩ :=
      Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
        (f := q) (g := qδ) hη_pos hz_aeval hq_monic hqδ_monic hqδ_deg hqδ_coeff
        (IsAlgClosed.splits _)
    have hFδ_rr : ((F - C δ * g) ≠ 0 ∧ (F - C δ * g).Splits) := hsub_rr hδ_pos
    have hqδ_rr : (qδ ≠ 0 ∧ qδ.Splits) := by simp_all [qδ]
    rcases mem_range_of_mem_aroots_of_isRealRooted hqδ_rr.2 hw_mem with ⟨x, rfl⟩
    have him_le : eps0 ≤ ‖z - x‖ := by
      unfold eps0
      simpa using (Complex.abs_im_le_norm (z - x))
    have hR_pos : 0 < R := by grind
    have hbound_eq :
        (((q.natDegree : ℝ) + 1) * η) ^ ((q.natDegree : ℝ)⁻¹) * R = eps0 / 2 := by
      have hdeg_ne : q.natDegree ≠ 0 := by lia
      have hu_nonneg : 0 ≤ u := by
        unfold u eps0 R
        positivity
      calc
        (((q.natDegree : ℝ) + 1) * η) ^ ((q.natDegree : ℝ)⁻¹) * R
            = (((q.natDegree : ℝ) + 1) * (u ^ q.natDegree / ((q.natDegree : ℝ) + 1)))
                ^ ((q.natDegree : ℝ)⁻¹) * R := by lia
        _ = (u ^ q.natDegree) ^ ((q.natDegree : ℝ)⁻¹) * R := by grind
        _ = u * R := by rw [Real.pow_rpow_inv_natCast hu_nonneg hdeg_ne]
        _ = eps0 / 2 := by grind
    have hclose_eps : ‖z - x‖ < eps0 := by
      calc
        ‖z - x‖ < (((q.natDegree : ℝ) + 1) * η) ^ ((q.natDegree : ℝ)⁻¹) * R := hw_close
        _ = eps0 / 2 := hbound_eq
        _ < eps0 := by simp_all
    grind
  have hq_split : q.Splits :=
    Polynomial.Splits.of_splits_map (i := algebraMap ℝ ℂ)
      (IsAlgClosed.splits _) hroots_real
  have hq_rr : (q ≠ 0 ∧ q.Splits) := by lia
  have hF_eq : C F.leadingCoeff * q = F := by
    unfold q
    calc
      C F.leadingCoeff * (C F.leadingCoeff⁻¹ * F)
          = (C F.leadingCoeff * C F.leadingCoeff⁻¹) * F := by grind
      _ = C (F.leadingCoeff * F.leadingCoeff⁻¹) * F := by simp
      _ = F := by simp [hlc_ne]
  rw [← hF_eq]
  simp_all [-hF_eq]


end RealRooted.MaWangInternal

namespace RealRooted

export MaWangInternal
  (prec_sub_C_mul_of_interlaces_evalCoeff_nonpos_of_no_common
    isRealRooted_sub_C_mul_of_interlaces_evalCoeff_nonpos_of_no_common
    isRealRooted_of_interlaces_evalCoeff_nonpos_of_no_common
    isRealRooted_of_interlaces_sub_C_mul_of_forall_pos)

end RealRooted
