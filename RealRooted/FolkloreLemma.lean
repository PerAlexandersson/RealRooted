import RealRooted.Basic
import RealRooted.Linear
import RealRooted.Derivative
import RealRooted.Wagner
import RealRooted.ObreschkoffConverse
-- import RealRooted.AffineDerivative  -- uncomment when AffineDerivative is built

/-!
# Folklore lemma for subtracting `X * g`

This file studies the standard claim that, under suitable monic and
nonpositive-root hypotheses, interlacing is preserved by the transformation
`(f, g) ↦ f - X * g`.

At a root `r` of `f`, `(f - X * g)(r) = -r * g(r)`.  Since the roots are
nonpositive, this has the same sign as `g(r)`.  The expected interlacing
conclusion then follows from sign alternation.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- At a root `r` of `f`, `(f - X*g)(r) = -r * g(r)`. -/
lemma eval_sub_X_mul_at_root {f g : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) :
    (f - X * g).eval r = -r * g.eval r := by
  simp [eval_sub, eval_mul, eval_X, IsRoot.def.mp hr]

/-- If `g ⊳ f` (differ-by-1), monic, all roots ≤ 0, then `(f - X*g) ≪₀ f`.
Again this is stated in the zero-aware convention to allow complete
cancellation. -/
theorem prec_sub_X_mul_left {f g : ℝ[X]}
    (hgf : Prec g f)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree + 1 = f.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    Prec0 (f - X * g) f := by
  set q : ℝ[X] := f - X * g
  by_cases hq0 : q = 0
  · simpa [q, hq0] using prec0_zero_left f
  · have hg : (g ≠ 0 ∧ g.Splits) := hgf.1
    have hf : (f ≠ 0 ∧ f.Splits) := hgf.2.1
    have hg_pos : HasPosLeadingCoeff g := hasPosLeadingCoeff_of_monic hg_monic
    have hf_pos : HasPosLeadingCoeff f := hasPosLeadingCoeff_of_monic hf_monic
    have hprec_fXg : Prec f (X * g) :=
      (prec_iff_prec_mul_X_of_roots_nonpos
        (f := g) (g := f) hg.2 hf.2 hg_pos hf_pos hg_nonpos hf_nonpos hdeg).mp hgf
    have hall_fXg : AllComboRealRooted f (X * g) :=
      allComboRealRooted_of_prec hprec_fXg
    have hall_qf : AllComboRealRooted q f := by
      intro α β
      have hrew :
          C α * q + C β * f =
            C (α + β) * f + C (-α) * (X * g) := by
        grind
      simpa [hrew] using hall_fXg (α + β) (-α)
    have hq : (q ≠ 0 ∧ q.Splits) :=
      ⟨hq0, by simpa using hall_qf 1 0⟩
    have hf0 : f ≠ 0 := hf.1
    have hclose := natDegree_close_of_allComboRealRooted hall_qf hq0 hf0
    have hq_lt : q.natDegree < f.natDegree := by
      have hq_le : q.natDegree ≤ f.natDegree := by
        have hXg_le : (X * g).natDegree ≤ f.natDegree := by simp_all
        have hsub : (f - X * g).natDegree ≤ f.natDegree :=
          (natDegree_sub_le_iff_left hXg_le).mpr le_rfl
        lia
      by_contra hnot
      have hf_le_q : f.natDegree ≤ q.natDegree := le_of_not_gt hnot
      have hq_eq : q.natDegree = f.natDegree := le_antisymm hq_le hf_le_q
      have hq_top_ne : q.coeff f.natDegree ≠ 0 := by
        rw [← hq_eq, coeff_natDegree]
        simp_all
      have hq_top_zero : q.coeff f.natDegree = 0 := by
        calc
          q.coeff f.natDegree
              = f.coeff f.natDegree - (X * g).coeff f.natDegree := by
                  simp [q, coeff_sub]
          _ = 1 - (X * g).coeff f.natDegree := by
                simp_all
          _ = 1 - g.coeff g.natDegree := by
                rw [← hdeg, coeff_X_mul]
          _ = 1 - g.leadingCoeff := by
                simp
          _ = 0 := by
                simp [hg_monic.leadingCoeff]
      lia
    have hdeg_qf : q.natDegree + 1 = f.natDegree := by lia
    have hprec_or : Prec q f ∨ Prec f q :=
      prec_of_allComboRealRooted hq.1 hq.2 hf.1 hf.2 hall_qf (Or.inl hdeg_qf)
    have hnot_prec_fq : ¬ Prec f q := by
      intro hfq
      rcases hfq with ⟨_, _, ss, rs, _, _, hss_eq, hrs_eq, hshape⟩
      have hss_len : ss.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
      have hrs_len : rs.length = q.natDegree := by
        rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hq.2]
      lia
    rcases hprec_or with hqf | hfq
    · exact hqf.toPrec0
    · lia

/-- If `g ⊳ f` (differ-by-1), monic, all roots ≤ 0, then `g ≪₀ (f - X*g)`.
This zero-aware form is the right endpoint behavior when cancellation
`f - X*g = 0` occurs. -/
theorem prec_sub_X_mul_right {f g : ℝ[X]}
    (hgf : Prec g f)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree + 1 = f.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    Prec0 g (f - X * g) := by
  set q : ℝ[X] := f - X * g
  by_cases hq0 : q = 0
  · simpa [q, hq0] using prec0_zero_right g
  · have hleft0 : Prec0 q f := by
      simpa [q] using prec_sub_X_mul_left hgf hf_monic hg_monic hdeg hf_nonpos hg_nonpos
    have hf0 : f ≠ 0 := hgf.2.1.1
    have hqf : Prec q f := by
      rcases hleft0 with hqz | hfz | hqf <;> lia
    have hall_qf : AllComboRealRooted q f := allComboRealRooted_of_prec hqf
    have hall_qXg : AllComboRealRooted q (X * g) := by
      intro α β
      have hrew :
          C α * q + C β * (X * g) =
            C (α - β) * q + C β * f := by
        grind
      simpa [hrew] using hall_qf (α - β) β
    have hq : (q ≠ 0 ∧ q.Splits) := hqf.1
    have hg : (g ≠ 0 ∧ g.Splits) := hgf.1
    have hXg : ((X * g) ≠ 0 ∧ (X * g).Splits) := isRealRooted_X_mul hg.1 hg.2
    have hq_lt : q.natDegree < f.natDegree := by
      have hq_le : q.natDegree ≤ f.natDegree := by
        have hXg_le : (X * g).natDegree ≤ f.natDegree := by simp_all
        have hsub : (f - X * g).natDegree ≤ f.natDegree :=
          (natDegree_sub_le_iff_left hXg_le).mpr le_rfl
        lia
      by_contra hnot
      have hf_le_q : f.natDegree ≤ q.natDegree := le_of_not_gt hnot
      have hq_eq : q.natDegree = f.natDegree := le_antisymm hq_le hf_le_q
      have hq_top_ne : q.coeff f.natDegree ≠ 0 := by
        rw [← hq_eq, coeff_natDegree]
        simp_all
      have hq_top_zero : q.coeff f.natDegree = 0 := by
        calc
          q.coeff f.natDegree
              = f.coeff f.natDegree - (X * g).coeff f.natDegree := by
                  simp [q, coeff_sub]
          _ = 1 - (X * g).coeff f.natDegree := by
                simp_all
          _ = 1 - g.coeff g.natDegree := by
                rw [← hdeg, coeff_X_mul]
          _ = 1 - g.leadingCoeff := by
                simp
          _ = 0 := by
                simp [hg_monic.leadingCoeff]
      lia
    have hclose_qf := natDegree_close_of_allComboRealRooted hall_qf hq0 hf0
    have hdeg_qf : q.natDegree + 1 = f.natDegree := by lia
    have hdeg_qXg : q.natDegree + 1 = (X * g).natDegree := by simp_all
    have hprec_or : Prec q (X * g) ∨ Prec (X * g) q :=
      prec_of_allComboRealRooted hq.1 hq.2 hXg.1 hXg.2 hall_qXg (Or.inl hdeg_qXg)
    have hnot_prec_Xgq : ¬ Prec (X * g) q := by
      intro hXgq
      rcases hXgq with ⟨_, _, ss, rs, _, _, hss_eq, hrs_eq, hshape⟩
      have hss_len : ss.length = (X * g).natDegree := by
        rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hXg.2]
      have hrs_len : rs.length = q.natDegree := by
        rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hq.2]
      lia
    have hprec_qXg : Prec q (X * g) := by lia
    have hdeg_gq : g.natDegree = q.natDegree := by lia
    exact
      (prec_of_prec_mul_X_of_sameDegree_of_roots_nonpos
        (f := g) (g := q) hprec_qXg hdeg_gq hg_nonpos).toPrec0

/-- Brändén--Saud minus-sign step in the strict `Prec` convention.

If `g ≪ f`, the two polynomials are monic with `deg f = deg g + 1`, all roots
are nonpositive, and `f - X * g` has positive leading coefficient, then
`g ≪ f - X * g ≪ f`. -/
theorem prec_sub_X_mul_pair_of_posLeadingCoeff {f g : ℝ[X]}
    (hgf : Prec g f)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree + 1 = f.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0)
    (hsub_pos : HasPosLeadingCoeff (f - X * g)) :
    Prec g (f - X * g) ∧ Prec (f - X * g) f := by
  have hsub_ne : f - X * g ≠ 0 := hsub_pos.ne_zero
  constructor
  · exact (prec_sub_X_mul_right hgf hf_monic hg_monic hdeg hf_nonpos hg_nonpos)
      |>.toPrec_of_ne hgf.1.1 hsub_ne
  · exact (prec_sub_X_mul_left hgf hf_monic hg_monic hdeg hf_nonpos hg_nonpos)
      |>.toPrec_of_ne hsub_ne hgf.2.1.1

/-- Brändén--Saud minus-sign step after scaling by a common positive leading
coefficient.

This is the same conclusion as `prec_sub_X_mul_pair_of_posLeadingCoeff`, but it
allows `f` and `g` to share any positive leading coefficient instead of being
monic. -/
theorem prec_sub_X_mul_pair_of_eq_posLeadingCoeff {f g : ℝ[X]}
    (hgf : Prec g f)
    (hf_pos : HasPosLeadingCoeff f)
    (hlc : f.leadingCoeff = g.leadingCoeff)
    (hdeg : g.natDegree + 1 = f.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0)
    (hsub_pos : HasPosLeadingCoeff (f - X * g)) :
    Prec g (f - X * g) ∧ Prec (f - X * g) f := by
  let c : ℝ := f.leadingCoeff⁻¹
  have hf_lc_ne : f.leadingCoeff ≠ 0 := ne_of_gt hf_pos
  have hc_ne : c ≠ 0 := inv_ne_zero hf_lc_ne
  have hc_pos : 0 < c := inv_pos.mpr hf_pos
  have hf_monic : (C c * f).Monic := by
    unfold c
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp [hf_lc_ne]
  have hg_monic : (C c * g).Monic := by
    unfold c
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [← hlc]
    simp [hf_lc_ne]
  have hscaled : Prec (C c * g) (C c * f) :=
    prec_C_mul_right (prec_C_mul_left hgf hc_ne) hc_ne
  have hdeg_scaled : (C c * g).natDegree + 1 = (C c * f).natDegree := by
    rw [natDegree_C_mul hc_ne, natDegree_C_mul hc_ne, hdeg]
  have hf_scaled_nonpos : ∀ r ∈ (C c * f).roots, r ≤ 0 := by
    simpa [roots_C_mul _ hc_ne] using hf_nonpos
  have hg_scaled_nonpos : ∀ r ∈ (C c * g).roots, r ≤ 0 := by
    simpa [roots_C_mul _ hc_ne] using hg_nonpos
  have hsub_scaled_pos : HasPosLeadingCoeff (C c * f - X * (C c * g)) := by
    have hEq : C c * f - X * (C c * g) = C c * (f - X * g) := by
      grind
    rw [hEq]
    exact hasPosLeadingCoeff_C_mul hc_pos hsub_pos
  have hpair_scaled :=
    prec_sub_X_mul_pair_of_posLeadingCoeff
      hscaled hf_monic hg_monic hdeg_scaled hf_scaled_nonpos hg_scaled_nonpos
      hsub_scaled_pos
  have hright_scaled : Prec (C c * g) (C c * (f - X * g)) := by
    have hEq : C c * f - X * (C c * g) = C c * (f - X * g) := by
      grind
    simpa [hEq] using hpair_scaled.1
  have hleft_scaled : Prec (C c * (f - X * g)) (C c * f) := by
    have hEq : C c * f - X * (C c * g) = C c * (f - X * g) := by
      grind
    simpa [hEq] using hpair_scaled.2
  have hcancel_g : C c⁻¹ * (C c * g) = g := by
    calc
      C c⁻¹ * (C c * g) = C (c⁻¹ * c) * g := by grind
      _ = g := by simp [c, hf_lc_ne]
  have hcancel_f : C c⁻¹ * (C c * f) = f := by
    calc
      C c⁻¹ * (C c * f) = C (c⁻¹ * c) * f := by grind
      _ = f := by simp [c, hf_lc_ne]
  have hcancel_sub : C c⁻¹ * (C c * (f - X * g)) = f - X * g := by
    calc
      C c⁻¹ * (C c * (f - X * g)) = C (c⁻¹ * c) * (f - X * g) := by grind
      _ = f - X * g := by simp [c, hf_lc_ne]
  constructor
  · have hback :=
      prec_C_mul_right
        (prec_C_mul_left hright_scaled (inv_ne_zero hc_ne))
        (inv_ne_zero hc_ne)
    simpa [hcancel_g, hcancel_sub] using hback
  · have hback :=
      prec_C_mul_right
        (prec_C_mul_left hleft_scaled (inv_ne_zero hc_ne))
        (inv_ne_zero hc_ne)
    simpa [hcancel_f, hcancel_sub] using hback

/-- A positive right shear preserves `Prec` when a larger scaled subtraction
has positive leading coefficient.

The scale `c > 1` is chosen so that `f` and `C c * g` have equal leading
coefficients.  The equal-leading subtraction theorem handles
`f - X * (C c * g)`, and `f - X * g` is then a positive convex combination
of this cancellation remainder and `f`. -/
theorem prec_right_shear_of_scaled_cancellation {f g : ℝ[X]} (c : ℝ)
    (hc : 1 < c)
    (hgf : Prec g f)
    (hf_pos : HasPosLeadingCoeff f)
    (hdeg : g.natDegree + 1 = f.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0)
    (hlc : f.leadingCoeff = (C c * g).leadingCoeff)
    (hcancel_pos : HasPosLeadingCoeff (f - X * (C c * g))) :
    Prec g (f - X * g) := by
  have hc_pos : 0 < c := lt_trans zero_lt_one hc
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hscaled : Prec (C c * g) f := prec_C_mul_left hgf hc_ne
  have hdeg_scaled : (C c * g).natDegree + 1 = f.natDegree := by
    rw [natDegree_C_mul hc_ne, hdeg]
  have hg_scaled_nonpos : ∀ r ∈ (C c * g).roots, r ≤ 0 := by
    simpa [roots_C_mul _ hc_ne] using hg_nonpos
  have hpair := prec_sub_X_mul_pair_of_eq_posLeadingCoeff
    hscaled hf_pos hlc hdeg_scaled hf_nonpos hg_scaled_nonpos hcancel_pos
  have hleft_scaled : Prec (C c⁻¹ * (C c * g)) (f - X * (C c * g)) :=
    prec_C_mul_left hpair.1 (inv_ne_zero hc_ne)
  have hcancel_left : C c⁻¹ * (C c * g) = g := by
    calc
      C c⁻¹ * (C c * g) = C (c⁻¹ * c) * g := by grind
      _ = g := by simp [hc_ne]
  have hleft : Prec g (f - X * (C c * g)) := by
    rwa [hcancel_left] at hleft_scaled
  have hinv_pos : 0 < c⁻¹ := inv_pos.mpr hc_pos
  have hone_sub_inv_pos : 0 < 1 - c⁻¹ := by
    rw [sub_pos, inv_lt_one₀ hc_pos]
    exact hc
  have hfirst : Prec g (C (1 - c⁻¹) * f) :=
    prec_C_mul_right hgf (ne_of_gt hone_sub_inv_pos)
  have hsecond : Prec g (C c⁻¹ * (f - X * (C c * g))) :=
    prec_C_mul_right hleft (ne_of_gt hinv_pos)
  have hsum : Prec g
      ([C (1 - c⁻¹) * f, C c⁻¹ * (f - X * (C c * g))] : List ℝ[X]).sum := by
    apply prec_sum_left_of_common_left_signed
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hfirst
      · exact hsecond
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hasPosLeadingCoeff_C_mul hone_sub_inv_pos hf_pos
      · exact hasPosLeadingCoeff_C_mul hinv_pos hcancel_pos
    · simp
  have hcinv : C c⁻¹ * C c = (1 : ℝ[X]) := by
    rw [← map_mul, inv_mul_cancel₀ hc_ne, map_one]
  have hsum_eq :
      ([C (1 - c⁻¹) * f, C c⁻¹ * (f - X * (C c * g))] : List ℝ[X]).sum =
        f - X * g := by
    simp only [List.sum_cons, List.sum_nil, add_zero]
    calc
      C (1 - c⁻¹) * f + C c⁻¹ * (f - X * (C c * g)) =
          (C (1 - c⁻¹) + C c⁻¹) * f - (C c⁻¹ * C c) * (X * g) := by ring
      _ = f - X * g := by
        rw [← map_add, sub_add_cancel, map_one, hcinv]
        ring
  rw [hsum_eq] at hsum
  exact hsum

/-- If the oriented same-degree relation `U ≪ X * V` is already known, then
the nonpositive-root Wagner step removes the factor `X` and gives `V ≪ U`. -/
theorem prec_component_of_prec_mul_X_of_roots_nonpos
    {U V : ℝ[X]}
    (hU_XV : Prec U (X * V))
    (hU_pos : HasPosLeadingCoeff U)
    (hV_pos : HasPosLeadingCoeff V)
    (hU_nonpos : ∀ r ∈ U.roots, r ≤ 0)
    (hV_nonpos : ∀ r ∈ V.roots, r ≤ 0)
    (hdeg_VU : V.natDegree + 1 = U.natDegree) :
    Prec V U := by
  have hV_splits : V.Splits := (isRealRooted_of_X_mul hU_XV.2.1.1 hU_XV.2.1.2).2
  exact
    (prec_iff_prec_mul_X_of_roots_nonpos
      (f := V) (g := U) hV_splits hU_XV.1.2 hV_pos hU_pos
      hV_nonpos hU_nonpos hdeg_VU).mpr hU_XV

/-- Root-sum-oriented conversion step for Braun--Jal Claim `(7)`.

If `U ≪ W` and `W = (1 + X) * U + X * V`, the usual Obreschkoff alternative
for `U` and `X * V` can be oriented by the same-degree root-sum order
`U.roots.sum ≤ (X * V).roots.sum`.  This is useful at zero-root endpoints where
the older strict rightmost-root asymmetry condition is too strong. -/
theorem prec_component_of_prec_next_eq_add_X_mul_of_roots_sum_le
    {U V W : ℝ[X]}
    (hUW : Prec U W)
    (hW_eq : W = (1 + X) * U + X * V)
    (hW_pos : HasPosLeadingCoeff W)
    (hWU_lc : W.leadingCoeff = U.leadingCoeff)
    (hdeg_UW : U.natDegree + 1 = W.natDegree)
    (hW_nonpos : ∀ r ∈ W.roots, r ≤ 0)
    (hU_nonpos : ∀ r ∈ U.roots, r ≤ 0)
    (hmid_pos : HasPosLeadingCoeff (U + X * V))
    (hV_pos : HasPosLeadingCoeff V)
    (hV_nonpos : ∀ r ∈ V.roots, r ≤ 0)
    (hdeg_VU : V.natDegree + 1 = U.natDegree)
    (hsum_U_XV : U.roots.sum ≤ (X * V).roots.sum) :
    Prec V U := by
  have hmid_eq : W - X * U = U + X * V := by
    rw [hW_eq]
    ring
  have hU_mid : Prec U (U + X * V) := by
    have hsub_pos : HasPosLeadingCoeff (W - X * U) := by
      simpa [hmid_eq] using hmid_pos
    have hpair :=
      prec_sub_X_mul_pair_of_eq_posLeadingCoeff
        (f := W) (g := U) hUW hW_pos hWU_lc hdeg_UW
        hW_nonpos hU_nonpos hsub_pos
    simpa [hmid_eq] using hpair.1
  have hall_U_mid : AllComboRealRooted U (U + X * V) :=
    allComboRealRooted_of_prec hU_mid
  have hall_U_XV : AllComboRealRooted U (X * V) := by
    intro α β
    have hrew :
        C α * U + C β * (X * V) =
          C (α - β) * U + C β * (U + X * V) := by
      grind
    simpa [hrew] using hall_U_mid (α - β) β
  have hXV_ne : X * V ≠ 0 := mul_ne_zero X_ne_zero hV_pos.ne_zero
  have hXV_splits : (X * V).Splits := by
    simpa using hall_U_XV 0 1
  have hsame : U.natDegree = (X * V).natDegree := by
    rw [natDegree_mul X_ne_zero hV_pos.ne_zero, natDegree_X]
    lia
  have hprec_or : Prec U (X * V) ∨ Prec (X * V) U :=
    prec_of_allComboRealRooted hUW.1.1 hUW.1.2 hXV_ne hXV_splits hall_U_XV
      (Or.inr hsame)
  have hU_XV : Prec U (X * V) := by
    rcases hprec_or with hU_XV | hXV_U
    · exact hU_XV
    · exact prec_of_reverse_prec_of_roots_sum_le hXV_U hsame hsum_U_XV
  have hU_pos : HasPosLeadingCoeff U := by
    simpa [HasPosLeadingCoeff, hWU_lc] using hW_pos
  exact
    prec_component_of_prec_mul_X_of_roots_nonpos
      hU_XV hU_pos hV_pos hU_nonpos hV_nonpos hdeg_VU

/-- Paper-shaped conversion step for Braun--Jal Claim `(7)`.

If `U ≪ W` and `W = (1 + X) * U + X * V`, with the root and degree side
conditions needed to orient the Obreschkoff alternative, then `V ≪ U`. -/
theorem prec_component_of_prec_next_eq_add_X_mul
    {U V W : ℝ[X]}
    (hUW : Prec U W)
    (hW_eq : W = (1 + X) * U + X * V)
    (hW_pos : HasPosLeadingCoeff W)
    (hWU_lc : W.leadingCoeff = U.leadingCoeff)
    (hdeg_UW : U.natDegree + 1 = W.natDegree)
    (hW_nonpos : ∀ r ∈ W.roots, r ≤ 0)
    (hU_nonpos : ∀ r ∈ U.roots, r ≤ 0)
    (hmid_pos : HasPosLeadingCoeff (U + X * V))
    (hV_pos : HasPosLeadingCoeff V)
    (hV_nonpos : ∀ r ∈ V.roots, r ≤ 0)
    (hdeg_VU : V.natDegree + 1 = U.natDegree)
    (hU_bound : ∃ c : ℝ, (∀ s ∈ U.roots, s ≤ c) ∧ c < 0) :
    Prec V U := by
  have hmid_eq : W - X * U = U + X * V := by
    rw [hW_eq]
    ring
  have hU_mid : Prec U (U + X * V) := by
    have hsub_pos : HasPosLeadingCoeff (W - X * U) := by
      simpa [hmid_eq] using hmid_pos
    have hpair :=
      prec_sub_X_mul_pair_of_eq_posLeadingCoeff
        (f := W) (g := U) hUW hW_pos hWU_lc hdeg_UW
        hW_nonpos hU_nonpos hsub_pos
    simpa [hmid_eq] using hpair.1
  have hall_U_mid : AllComboRealRooted U (U + X * V) :=
    allComboRealRooted_of_prec hU_mid
  have hall_U_XV : AllComboRealRooted U (X * V) := by
    intro α β
    have hrew :
        C α * U + C β * (X * V) =
          C (α - β) * U + C β * (U + X * V) := by
      grind
    simpa [hrew] using hall_U_mid (α - β) β
  have hXV_ne : X * V ≠ 0 := mul_ne_zero X_ne_zero hV_pos.ne_zero
  have hXV_splits : (X * V).Splits := by
    simpa using hall_U_XV 0 1
  have hsame : U.natDegree = (X * V).natDegree := by
    rw [natDegree_mul X_ne_zero hV_pos.ne_zero, natDegree_X]
    lia
  have hprec_or : Prec U (X * V) ∨ Prec (X * V) U :=
    prec_of_allComboRealRooted hUW.1.1 hUW.1.2 hXV_ne hXV_splits hall_U_XV
      (Or.inr hsame)
  obtain ⟨c, hU_le, hc_lt⟩ := hU_bound
  have hXV_root0 : (X * V).IsRoot 0 := by
    simp
  have hU_XV : Prec U (X * V) :=
    PosComboRealRooted.revPrec_of_prec_or_revPrec_of_root_asymmetry
      (f := U) (g := X * V) (c := c) (r := 0)
      hprec_or hU_le hXV_root0 hc_lt
  have hV_splits : V.Splits := (isRealRooted_of_X_mul hXV_ne hXV_splits).2
  have hU_pos : HasPosLeadingCoeff U := by
    simpa [HasPosLeadingCoeff, hWU_lc] using hW_pos
  exact
    prec_component_of_prec_mul_X_of_roots_nonpos
      hU_XV hU_pos hV_pos hU_nonpos hV_nonpos hdeg_VU

end RealRooted
