module

public import RealRooted.WagnerX.ListInterlacing

/-!
# Wagner-X nonnegative coefficients and roots
-/

@[expose] public section

open Polynomial Filter

noncomputable section

namespace RealRooted

/-! ## Roots of nonneg-coefficient polynomials are ≤ 0 -/

lemma hasNonnegCoeffs_X_sub_C {r : ℝ} (hr : r ≤ 0) : HasNonnegCoeffs (X - C r) := by
  rintro (_ | _ | n)
  · simp [coeff_sub, hr]
  · simp [coeff_sub]
  · rw [coeff_sub, coeff_X_of_ne_one (by lia), coeff_C_succ]
    simp

protected lemma HasNonnegCoeffs.X_mul {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (X * p) :=
  hasNonnegCoeffs_X.mul hp

lemma hasNonnegCoeffs_X_add_C {a : ℝ} (ha : 0 ≤ a) :
    HasNonnegCoeffs (X + C a : ℝ[X]) := by
  simpa [sub_eq_add_neg] using hasNonnegCoeffs_X_sub_C (r := -a) (by linarith)

lemma hasNonnegCoeffs_X_add_one : HasNonnegCoeffs (X + 1 : ℝ[X]) := by
  simpa using hasNonnegCoeffs_X_add_C (a := 1) (zero_le_one : (0 : ℝ) ≤ 1)

lemma hasNonnegCoeffs_multiset_prod_X_sub_C :
    ∀ s : Multiset ℝ, (∀ r ∈ s, r ≤ 0) → HasNonnegCoeffs ((s.map (X - C ·)).prod) := by
  intro s hs
  induction s using Multiset.induction_on with
  | empty =>
      simpa using hasNonnegCoeffs_one
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact (hasNonnegCoeffs_X_sub_C (hs a (by simp))).mul
        (ih (fun r hr => hs r (by simp [hr])))

@[deprecated "Use `roots_nonpos_of_hasNonnegCoeffs`." (since := "2026-10-12")]
theorem roots_nonpos_of_nonneg_coeffs {p : ℝ[X]} (_ : p.Splits)
    (hnn : HasNonnegCoeffs p) : ∀ r ∈ p.roots, r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs hnn

lemma hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos {p : ℝ[X]} (hp : p.Splits) :
    HasNonnegCoeffs p ∧ p ≠ 0 ↔ HasPosLeadingCoeff p ∧ ∀ r ∈ p.roots, r ≤ 0 := by
  constructor
  · intro ⟨hnn, hp₀⟩
    exact ⟨hnn.pos_leadingCoeff hp₀, roots_nonpos_of_hasNonnegCoeffs hnn⟩
  · rintro ⟨hp₀, hroots_nonpos⟩
    refine ⟨?_, hp₀.ne_zero⟩
    rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (Polynomial.splits_iff_card_roots.mp hp)]
    exact (hasNonnegCoeffs_C hp₀.le).mul
      (hasNonnegCoeffs_multiset_prod_X_sub_C p.roots hroots_nonpos)

/-- A split real polynomial with nonnegative coefficients and constant coefficient one
is a product of linear factors `1 + a X` with positive `a`. -/
theorem exists_eq_prod_one_add_C_mul_X_of_splits {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hp0 : p.coeff 0 = 1) (hps : p.Splits) :
    ∃ a : Fin p.natDegree → ℝ, (∀ i, 0 < a i) ∧
      p = ∏ i, (1 + C (a i) * X) := by
  have hp_ne : p ≠ 0 := by
    intro hp
    rw [hp] at hp0
    simp at hp0
  have hroot_neg : ∀ r ∈ p.roots, r < 0 := by
    intro r hr
    have hr_nonpos := roots_nonpos_of_hasNonnegCoeffs hpnn r hr
    have hr_ne : r ≠ 0 := by
      intro hr_zero
      subst r
      have hroot : p.IsRoot 0 := (mem_roots hp_ne).mp hr
      rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero, hp0] at hroot
      norm_num at hroot
    exact lt_of_le_of_ne hr_nonpos hr_ne
  let e : p.roots ≃ Fin p.natDegree :=
    Fintype.equivFinOfCardEq (by simpa using hps.natDegree_eq_card_roots.symm)
  let a : Fin p.natDegree → ℝ := fun i ↦ -1 / (e.symm i : ℝ)
  have ha : ∀ i, 0 < a i := by
    intro i
    exact div_pos_of_neg_of_neg (by norm_num) (hroot_neg _ (by simp))
  refine ⟨a, ha, ?_⟩
  have hfactor : ∀ r : p.roots,
      1 + C (-1 / (r : ℝ)) * X =
        C (-1 / (r : ℝ)) * (X - C (r : ℝ)) := by
    intro r
    have hr_ne : (r : ℝ) ≠ 0 := ne_of_lt (hroot_neg r (by simp))
    have hscalar : (-1 / (r : ℝ)) * (r : ℝ) = -1 := by
      field_simp
    rw [mul_sub, ← C_mul, hscalar]
    simp [add_comm]
  have hprod_eval :
      (p.roots.map fun r ↦ (0 : ℝ) - r).prod = ∏ r : p.roots, -(r : ℝ) := by
    calc
      (p.roots.map fun r ↦ (0 : ℝ) - r).prod =
          ∏ i ∈ p.roots.toEnumFinset, -i.1 := by
        rw [Multiset.prod_map_eq_prod_toEnumFinset]
        simp
      _ = ∏ r : p.roots, -(r : ℝ) :=
        Multiset.prod_toEnumFinset p.roots (fun r _ ↦ -r)
  have heval : 1 = p.leadingCoeff * ∏ r : p.roots, -(r : ℝ) := by
    calc
      1 = p.coeff 0 := hp0.symm
      _ = p.eval 0 := coeff_zero_eq_eval_zero p
      _ = p.leadingCoeff * (p.roots.map fun r ↦ (0 : ℝ) - r).prod :=
        hps.eval_eq_prod_roots 0
      _ = p.leadingCoeff * ∏ r : p.roots, -(r : ℝ) := by rw [hprod_eval]
  have hlead : p.leadingCoeff = ∏ r : p.roots, (-1 / (r : ℝ)) := by
    calc
      p.leadingCoeff = (∏ r : p.roots, -(r : ℝ))⁻¹ := by
        apply (mul_eq_one_iff_eq_inv₀ ?_).mp heval.symm
        exact Finset.prod_ne_zero_iff.mpr fun r _ ↦
          neg_ne_zero.mpr (ne_of_lt (hroot_neg r (by simp)))
      _ = ∏ r : p.roots, (-1 / (r : ℝ)) := by
        rw [← Finset.prod_inv_distrib]
        apply Finset.prod_congr rfl
        intro r _
        have hr_ne : (r : ℝ) ≠ 0 := ne_of_lt (hroot_neg r (by simp))
        field_simp
  have hprod_poly :
      (p.roots.map (X - C ·)).prod = ∏ r : p.roots, (X - C (r : ℝ)) := by
    calc
      (p.roots.map (X - C ·)).prod =
          ∏ i ∈ p.roots.toEnumFinset, (X - C i.1) := by
        rw [Multiset.prod_map_eq_prod_toEnumFinset]
      _ = ∏ r : p.roots, (X - C (r : ℝ)) :=
        Multiset.prod_toEnumFinset p.roots (fun r _ ↦ X - C r)
  calc
    p = C p.leadingCoeff * (p.roots.map (X - C ·)).prod := hps.eq_prod_roots
    _ = C p.leadingCoeff * ∏ r : p.roots, (X - C (r : ℝ)) := by rw [hprod_poly]
    _ = ∏ r : p.roots, (1 + C (-1 / (r : ℝ)) * X) := by
      rw [hlead, map_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun r _ ↦ hfactor r |>.symm
    _ = ∏ i, (1 + C (a i) * X) := by
      simpa [a] using (e.prod_comp fun i ↦ 1 + C (a i) * X)

/-- If all roots of a real-rooted positive-leading polynomial are at most `r`,
then translating by `X + r` gives a polynomial with nonnegative
coefficients. -/
lemma hasNonnegCoeffs_comp_X_add_C_of_roots_le
    {p : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hp_splits : p.Splits)
    {r : ℝ} (hbound : ∀ s ∈ p.roots, s ≤ r) :
    HasNonnegCoeffs (p.comp (X + C r)) := by
  have hp' : ((p.comp (X + C r)) ≠ 0 ∧ (p.comp (X + C r)).Splits) :=
    isRealRooted_comp_X_add_C hp_pos.ne_zero hp_splits r
  refine ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hp'.2).2 ?_).1
  refine ⟨hp_pos.comp_X_add_C r, ?_⟩
  intro s hs
  simp only [roots_comp_X_add_C r] at hs
  rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
  simp_all

lemma hasNonnegCoeffs_of_dvd_of_hasPosLeadingCoeff
    {p q : ℝ[X]}
    (hp_ne : p ≠ 0) (hpnn : HasNonnegCoeffs p)
    (hq_ne : q ≠ 0) (hq_splits : q.Splits) (hq_pos : HasPosLeadingCoeff q)
    (hqp : q ∣ p) :
    HasNonnegCoeffs q := by
  refine ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hq_splits).mpr ?_).1
  refine ⟨hq_pos, ?_⟩
  intro r hr
  have hrq : q.IsRoot r := (mem_roots hq_ne).mp hr
  have hrp : p.IsRoot r := hrq.dvd hqp
  exact roots_nonpos_of_hasNonnegCoeffs hpnn r ((mem_roots hp_ne).mpr hrp)

private lemma coe_append_zero_eq_roots_X_mul {f : ℝ[X]} (hf : f ≠ 0)
    {ss : List ℝ} (hss : (↑ss : Multiset ℝ) = f.roots) :
    (↑(ss ++ [(0 : ℝ)]) : Multiset ℝ) = (X * f).roots := by
  rw [roots_mul (mul_ne_zero X_ne_zero hf), roots_X, ← hss, ← Multiset.coe_add]
  simp [add_comm]

theorem strictInterl_of_strictInterl_mul_X_of_sameDegree_of_roots_nonpos {f g : ℝ[X]}
    (h : StrictInterl g (X * f))
    (hdeg : f.natDegree = g.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0) :
    StrictInterl f g := by
  rcases h with ⟨hg, hXf, ss_g, rs_Xf, hss_g, hrs_Xf, hss_g_eq, hrs_Xf_eq, hshape⟩
  have hf : f ≠ 0 ∧ f.Splits := by simp_all
  set rs_f := f.roots.sort (· ≤ ·)
  have hrs_f_eq : (↑rs_f : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_f : rs_f.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_f_nonpos : ∀ r ∈ rs_f, r ≤ 0 :=
    fun r hr => hf_nonpos r (by rw [← hrs_f_eq]; exact Multiset.mem_coe.mpr hr)
  have hrs_f0 : (rs_f ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  have hrs_Xf_is : rs_Xf = rs_f ++ [(0 : ℝ)] := by
    exact List.Perm.eq_of_pairwise' hrs_Xf hrs_f0 <| Multiset.coe_eq_coe.mp <|
      hrs_Xf_eq.trans (coe_append_zero_eq_roots_X_mul hf.1 hrs_f_eq).symm
  have hlen_fg : rs_f.length = ss_g.length := by
    rw [← Multiset.coe_card, hrs_f_eq, Polynomial.splits_iff_card_roots.mp hf.2,
      ← Multiset.coe_card, hss_g_eq, Polynomial.splits_iff_card_roots.mp hg.2, hdeg]
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, _⟩
  · rw [hrs_Xf_is] at hint hlen
    have hlen' : ss_g.length + 1 = (rs_f ++ [(0 : ℝ)]).length := by lia
    have hrs_f0_nonpos : ∀ r ∈ rs_f ++ [(0 : ℝ)], r ≤ 0 := by grind
    have halt0 :
        ListAlternates (rs_f ++ [(0 : ℝ)]) (ss_g ++ [(0 : ℝ)]) :=
      listAlternates_append_zero ss_g (rs_f ++ [(0 : ℝ)]) hlen' hint hrs_f0_nonpos
    have halt : ListAlternates rs_f ss_g :=
      listAlternates_of_append_zero_both rs_f ss_g hlen_fg halt0
    exact ⟨hf, hg, rs_f, ss_g, hrs_f, hss_g, hrs_f_eq, hss_g_eq, Or.inr ⟨hlen_fg, halt⟩⟩
  · simp_all

/-! ## Wagner (3): f ≪ g ↔ g ≪ X·f -/

/-- The degree-increasing case of Wagner (3), with nonpositive roots. -/
private theorem strictInterl_iff_mul_X_of_roots_nonpos_of_succ {f g : ℝ[X]}
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0) (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0)
    (hf₀ : f ≠ 0) (hf : f.Splits) (hg₀ : g ≠ 0) (hg : g.Splits)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    StrictInterl f g ↔ StrictInterl g (X * f) := by
  have hXf_deg : (X * f).natDegree = g.natDegree := by simp_all
  constructor
  · -- Forward: StrictInterl f g → StrictInterl g (X * f)
    intro ⟨_, _, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
    rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, _⟩
    · have hrs_nonpos : ∀ r ∈ rs, r ≤ 0 := fun r hr =>
        hg_nonpos r (by rw [← hrs_eq]; exact Multiset.mem_coe.mpr hr)
      have hss0_eq : (↑(ss ++ [(0 : ℝ)]) : Multiset ℝ) = (X * f).roots :=
        coe_append_zero_eq_roots_X_mul hf₀ hss_eq
      have hss_nonpos : ∀ s ∈ ss, s ≤ 0 := fun s hs =>
        hf_nonpos s (by rw [← hss_eq]; exact Multiset.mem_coe.mpr hs)
      have hss0_sorted : (ss ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
      exact
        ⟨⟨hg₀, hg⟩, by simp_all, rs, ss ++ [(0 : ℝ)], hrs, hss0_sorted,
          hrs_eq, hss0_eq,
          Or.inr ⟨by simp_all, listAlternates_append_zero ss rs hlen hint hrs_nonpos⟩⟩
    · have : ss.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_eq, Polynomial.splits_iff_card_roots.mp hf]
      have : rs.length = g.natDegree := by
        rw [← Multiset.coe_card, hrs_eq, Polynomial.splits_iff_card_roots.mp hg]
      lia
  · -- Backward: StrictInterl g (X * f) → StrictInterl f g
    intro ⟨_, _, ss_g, rs_xf, hss_g, hrs_xf, hss_g_eq, hrs_xf_eq, hcase⟩
    rcases hcase with ⟨hlen, _⟩ | ⟨hlen, halt⟩
    · have : ss_g.length = g.natDegree := by
        rw [← Multiset.coe_card, hss_g_eq, Polynomial.splits_iff_card_roots.mp hg]
      have : rs_xf.length = (X * f).natDegree := by
        rw [← Multiset.coe_card, hrs_xf_eq, Polynomial.splits_iff_card_roots.mp (by simp_all)]
      lia
    · set ss_f := f.roots.sort (· ≤ ·)
      have hss_f_eq : (↑ss_f : Multiset ℝ) = f.roots := Multiset.sort_eq ..
      have hss_f_sorted : ss_f.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
      have hrs_xf_is : rs_xf = ss_f ++ [(0 : ℝ)] := by
        have hsorted_concat : (ss_f ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by
          rw [List.pairwise_append]
          exact ⟨hss_f_sorted, List.pairwise_singleton _ _, fun a ha _ hb => by
            simp only [List.mem_singleton] at hb; rw [hb]
            exact hf_nonpos a (by rw [← hss_f_eq]; exact Multiset.mem_coe.mpr ha)⟩
        exact List.Perm.eq_of_pairwise' hrs_xf hsorted_concat <| Multiset.coe_eq_coe.mp <|
          hrs_xf_eq.trans (coe_append_zero_eq_roots_X_mul hf₀ hss_f_eq).symm
      rw [hrs_xf_is] at halt
      have hlen' : ss_f.length + 1 = ss_g.length := by simp_all
      exact
        ⟨⟨hf₀, hf⟩, ⟨hg₀, hg⟩, ss_f, ss_g, hss_f_sorted, hss_g, hss_f_eq,
          hss_g_eq,
          Or.inl ⟨by lia, listInterlaces_of_listAlternates_append_zero ss_f ss_g hlen' halt⟩⟩

theorem strictInterl_sameDegree_to_strictInterl_mul_X_of_roots_nonpos {f g : ℝ[X]}
    (h : StrictInterl f g)
    (hdeg : f.natDegree = g.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    StrictInterl g (X * f) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  have hXf_rr : (X * f) ≠ 0 ∧ (X * f).Splits := by simp_all
  have hss_nonpos : ∀ s ∈ ss, s ≤ 0 := fun s hs =>
    hf_nonpos s (by rw [← hss_eq]; exact Multiset.mem_coe.mpr hs)
  have hss0_sorted : (ss ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  have hss0_eq : (↑(ss ++ [(0 : ℝ)]) : Multiset ℝ) = (X * f).roots :=
    coe_append_zero_eq_roots_X_mul hf.1 hss_eq
  rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · have hss_len : ss.length = f.natDegree := by
      rw [← Multiset.coe_card, hss_eq, Polynomial.splits_iff_card_roots.mp hf.2]
    have hrs_len : rs.length = g.natDegree := by
      rw [← Multiset.coe_card, hrs_eq, Polynomial.splits_iff_card_roots.mp hg.2]
    lia
  · refine ⟨hg, hXf_rr, rs, ss ++ [0], hrs, hss0_sorted, hrs_eq, hss0_eq, Or.inl ?_⟩
    refine ⟨?_, listInterlaces_right_of_listAlternates_append_zero ss rs ?_ halt ?_⟩
    · simp_all
    · lia
    · intro r hr
      exact hg_nonpos r (by rw [← hrs_eq]; exact Multiset.mem_coe.mpr hr)

/-- Wagner (3): if all roots of `f` and `g` are nonpositive, then `f`
interlaces `g` if and only if `g` interlaces `X * f`.

No degree or leading-coefficient hypothesis is needed.  Either side forces
`g.natDegree = f.natDegree` or `g.natDegree = f.natDegree + 1`, and both cases
are covered. -/
theorem strictInterl_iff_mul_X_of_roots_nonpos {f g : ℝ[X]}
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0) (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    StrictInterl f g ↔ StrictInterl g (X * f) := by
  constructor
  · intro h
    rcases h.natDegree_eq_or_eq_succ with hdeg | hdeg
    · exact strictInterl_sameDegree_to_strictInterl_mul_X_of_roots_nonpos h hdeg.symm
        hf_nonpos hg_nonpos
    · exact (strictInterl_iff_mul_X_of_roots_nonpos_of_succ hf_nonpos hg_nonpos
        h.1.1 h.1.2 h.2.1.1 h.2.1.2 hdeg.symm).mp h
  · intro h
    have hf₀ : f ≠ 0 := right_ne_zero_of_mul h.2.1.1
    have hf : f ≠ 0 ∧ f.Splits :=
      isRealRooted_of_dvd h.2.1.1 h.2.1.2 hf₀ (dvd_mul_left f X)
    have hXf_deg : (X * f).natDegree = f.natDegree + 1 := by
      rw [natDegree_mul X_ne_zero hf₀, natDegree_X]
      lia
    rcases h.natDegree_eq_or_eq_succ with hdeg | hdeg
    · exact (strictInterl_iff_mul_X_of_roots_nonpos_of_succ hf_nonpos hg_nonpos
        hf₀ hf.2 h.1.1 h.1.2 (by lia)).mpr h
    · exact strictInterl_of_strictInterl_mul_X_of_sameDegree_of_roots_nonpos h (by lia)
        hf_nonpos

/-- Wagner (3) in the degree-increasing case, for polynomials with nonnegative
coefficients.  See `strictInterl_iff_mul_X_of_roots_nonpos` for the general
form. -/
theorem strictInterl_iff_strictInterl_mul_X {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hf₀ : f ≠ 0) (hf : f.Splits) (hg₀ : g ≠ 0) (hg : g.Splits)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    StrictInterl f g ↔ StrictInterl g (X * f) :=
  strictInterl_iff_mul_X_of_roots_nonpos_of_succ (roots_nonpos_of_hasNonnegCoeffs hfnn)
    (roots_nonpos_of_hasNonnegCoeffs hgnn) hf₀ hf hg₀ hg hdeg

/-- Wagner (3) in the degree-increasing case, for real-rooted polynomials with
nonpositive roots and positive leading coefficients.  See
`strictInterl_iff_mul_X_of_roots_nonpos` for the general form. -/
theorem strictInterl_iff_strictInterl_mul_X_of_roots_nonpos
    {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    StrictInterl f g ↔ StrictInterl g (X * f) :=
  strictInterl_iff_mul_X_of_roots_nonpos_of_succ hf_nonpos hg_nonpos hf_pos.ne_zero hf
    hg_pos.ne_zero hg hdeg

/-- Nonnegative-coefficients form of Wagner (3): if `f ≪ g` and both
polynomials have nonnegative coefficients, then `g ≪ X * f`. This packages
the differ-by-1 and same-degree cases under one theorem. -/
theorem strictInterl_mul_X_of_strictInterl_of_nonneg {f g : ℝ[X]}
    (h : StrictInterl f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    StrictInterl g (X * f) :=
  (strictInterl_iff_mul_X_of_roots_nonpos (roots_nonpos_of_hasNonnegCoeffs hfnn)
    (roots_nonpos_of_hasNonnegCoeffs hgnn)).mp h

/-- Nonzero scalar form of the Wagner `X`-shift bridge. -/
theorem strictInterl_C_mul_X_of_strictInterl_of_nonneg {f g : ℝ[X]} {c : ℝ}
    (h : StrictInterl f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hc : c ≠ 0) :
    StrictInterl g ((C c * X) * f) := by
  simpa [mul_assoc] using
    (StrictInterl.C_mul_right (strictInterl_mul_X_of_strictInterl_of_nonneg h hfnn hgnn) hc)

/-- Zero-aware Wagner (3): if `f ≪₀ g` and both polynomials have nonnegative
coefficients, then `g ≪₀ X * f`. -/
theorem interl_mul_X_of_interl {f g : ℝ[X]}
    (h : Interl f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Interl g (X * f) := by
  rcases h with rfl | rfl | hfg
  · simpa using interl_zero_right g
  · exact interl_zero_left (X * f)
  · exact (strictInterl_mul_X_of_strictInterl_of_nonneg hfg hfnn hgnn).toInterl

/-- Multiplying both polynomials by `X` preserves strict interlacing when all
roots are nonpositive. -/
@[deprecated StrictInterl.mul_X_sub_C_both +typeChanged (since := "2026-10-21")]
theorem StrictInterl.mul_X_both_of_roots_nonpos {f g : ℝ[X]} (h : StrictInterl f g)
    (_hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (_hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    StrictInterl (X * f) (X * g) := by
  simpa using h.mul_X_sub_C_both 0

/-- Cancelling a common factor `X` preserves strict interlacing when all
remaining roots are nonpositive. -/
@[deprecated StrictInterl.of_mul_X_sub_C_both +typeChanged (since := "2026-10-21")]
theorem StrictInterl.of_mul_X_both_of_roots_nonpos {f g : ℝ[X]}
    (h : StrictInterl (X * f) (X * g))
    (_hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (_hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    StrictInterl f g := by
  apply StrictInterl.of_mul_X_sub_C_both (r := 0)
  simpa using h

/-! ## Wagner `X`-multiplication interlacing bridges -/

/- The canonical names below are kept in this lower dependency layer so that
the affine-family API can reuse them without importing derivative results. -/

/-- A split polynomial with nonnegative coefficients precedes its product with
`X`. -/
lemma strictInterl_self_X_mul_of_nonneg {f : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hfnn : HasNonnegCoeffs f) :
    StrictInterl f (X * f) :=
  strictInterl_mul_X_of_strictInterl_of_nonneg (StrictInterl.refl hf_ne hf_splits) hfnn hfnn

/-- The reverse Wagner transport recovers `StrictInterl f g` from `StrictInterl g (X * f)`
when both polynomials have nonnegative coefficients. -/
lemma strictInterl_of_strictInterl_X_mul_of_nonneg {f g : ℝ[X]}
    (h : StrictInterl g (X * f)) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    StrictInterl f g :=
  (strictInterl_iff_mul_X_of_roots_nonpos (roots_nonpos_of_hasNonnegCoeffs hfnn)
    (roots_nonpos_of_hasNonnegCoeffs hgnn)).mpr h

/-- Nonnegative-coefficient form of the common-factor Wagner `X` bridge. -/
@[deprecated StrictInterl.mul_X_sub_C_both +typeChanged (since := "2026-10-21")]
theorem StrictInterl.mul_X_both_of_nonneg {f g : ℝ[X]}
    (h : StrictInterl f g) (_hfnn : HasNonnegCoeffs f) (_hgnn : HasNonnegCoeffs g) :
    StrictInterl (X * f) (X * g) := by
  simpa using h.mul_X_sub_C_both 0

/-- Multiplication by `X` on both sides is an equivalence on strict
interlacing when all roots are nonpositive. -/
@[deprecated StrictInterl.mul_X_sub_C_both_iff +typeChanged (since := "2026-10-21")]
theorem StrictInterl.mul_X_both_iff_of_roots_nonpos {f g : ℝ[X]}
    (_hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (_hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    StrictInterl f g ↔ StrictInterl (X * f) (X * g) := by
  simpa using StrictInterl.mul_X_sub_C_both_iff (f := f) (g := g) 0

/-- Compatibility form of common-`X` multiplication for zero-aware
interlacing. -/
@[deprecated Interl.mul_X_both +typeChanged (since := "2026-10-21")]
theorem Interl.mul_X_both_of_nonneg {f g : ℝ[X]}
    (h : Interl f g) (_hfnn : HasNonnegCoeffs f) (_hgnn : HasNonnegCoeffs g) :
    Interl (X * f) (X * g) := by
  exact h.mul_X_both

end RealRooted
