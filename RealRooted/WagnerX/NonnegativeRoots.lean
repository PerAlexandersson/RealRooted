import RealRooted.WagnerX.ListInterlacing

/-!
# Wagner-X nonnegative coefficients and roots
-/

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

lemma hasNonnegCoeffs_X : HasNonnegCoeffs (X : ℝ[X]) := by
  simpa using hasNonnegCoeffs_X_sub_C (r := 0) le_rfl

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

lemma roots_nonpos_of_nonneg_coeffs {p : ℝ[X]} (hp : p.Splits)
    (hnn : HasNonnegCoeffs p) : ∀ r ∈ p.roots, r ≤ 0 := by
  have _ := hp
  exact roots_nonpos_of_hasNonnegCoeffs hnn

lemma hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos {p : ℝ[X]} (hp : p.Splits) :
    HasNonnegCoeffs p ∧ p ≠ 0 ↔ HasPosLeadingCoeff p ∧ ∀ r ∈ p.roots, r ≤ 0 := by
  constructor
  · intro ⟨hnn, hp₀⟩
    exact ⟨hnn.pos_leadingCoeff hp₀, roots_nonpos_of_nonneg_coeffs hp hnn⟩
  · rintro ⟨hp₀, hroots_nonpos⟩
    refine ⟨?_, hp₀.ne_zero⟩
    rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_of_splits hp)]
    exact (hasNonnegCoeffs_C hp₀.le).mul
      (hasNonnegCoeffs_multiset_prod_X_sub_C p.roots hroots_nonpos)

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

lemma hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
    {p q : ℝ[X]}
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p)
    (hq_ne : q ≠ 0) (hq_splits : q.Splits) (hq_pos : HasPosLeadingCoeff q)
    (hqp : q ∣ p) :
    HasNonnegCoeffs q := by
  refine ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hq_splits).mpr ?_).1
  refine ⟨hq_pos, ?_⟩
  intro r hr
  have hrq : q.IsRoot r := (mem_roots hq_ne).mp hr
  have hrp : p.IsRoot r := IsRoot.of_dvd hqp hrq
  exact roots_nonpos_of_nonneg_coeffs hp_splits hpnn r ((mem_roots hp_ne).mpr hrp)

theorem prec_of_prec_mul_X_of_sameDegree_of_roots_nonpos {f g : ℝ[X]}
    (h : Prec g (X * f))
    (hdeg : f.natDegree = g.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0) :
    Prec f g := by
  rcases h with ⟨hg, hXf, ss_g, rs_Xf, hss_g, hrs_Xf, hss_g_eq, hrs_Xf_eq, hshape⟩
  have hf : f ≠ 0 ∧ f.Splits := by simp_all
  set rs_f := f.roots.sort (· ≤ ·)
  have hrs_f_eq : (↑rs_f : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_f : rs_f.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_f_nonpos : ∀ r ∈ rs_f, r ≤ 0 :=
    fun r hr => hf_nonpos r (by rw [← hrs_f_eq]; exact Multiset.mem_coe.mpr hr)
  have hrs_f0 : (rs_f ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  have hXf_roots : (X * f).roots = {0} + f.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hf.1), roots_X]
  have hrs_Xf_is : rs_Xf = rs_f ++ [(0 : ℝ)] := by
    have hmultiset_eq : (↑rs_Xf : Multiset ℝ) = ↑(rs_f ++ [(0 : ℝ)]) := by
      rw [hrs_Xf_eq, hXf_roots, ← hrs_f_eq, ← Multiset.coe_add]
      simp [add_comm]
    exact List.Perm.eq_of_pairwise' hrs_Xf hrs_f0 (Multiset.coe_eq_coe.mp hmultiset_eq)
  have hlen_fg : rs_f.length = ss_g.length := by
    rw [← Multiset.coe_card, hrs_f_eq, card_roots_of_splits hf.2,
      ← Multiset.coe_card, hss_g_eq, card_roots_of_splits hg.2, hdeg]
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

theorem prec_iff_prec_mul_X {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hf₀ : f ≠ 0) (hf : f.Splits) (hg₀ : g ≠ 0) (hg : g.Splits)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Prec f g ↔ Prec g (X * f) := by
  have hXf_roots : (X * f).roots = {0} + f.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hf₀), roots_X]
  have hXf_deg : (X * f).natDegree = g.natDegree := by simp_all
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf hfnn
  have hg_nonpos : ∀ r ∈ g.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hg hgnn
  constructor
  · -- Forward: Prec f g → Prec g (X * f)
    intro ⟨_, _, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
    rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, _⟩
    · have hrs_nonpos : ∀ r ∈ rs, r ≤ 0 := fun r hr =>
        hg_nonpos r (by rw [← hrs_eq]; exact Multiset.mem_coe.mpr hr)
      have hss0_eq : (↑(ss ++ [(0 : ℝ)]) : Multiset ℝ) = (X * f).roots := by
        have : (↑(ss ++ [(0 : ℝ)]) : Multiset ℝ) = ↑ss + {(0 : ℝ)} := by
          rw [← Multiset.coe_add]; simp
        grind
      have hss_nonpos : ∀ s ∈ ss, s ≤ 0 := fun s hs =>
        hf_nonpos s (by rw [← hss_eq]; exact Multiset.mem_coe.mpr hs)
      have hss0_sorted : (ss ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
      exact
        ⟨⟨hg₀, hg⟩, by simp_all, rs, ss ++ [(0 : ℝ)], hrs, hss0_sorted,
          hrs_eq, hss0_eq,
          Or.inr ⟨by simp_all, listAlternates_append_zero ss rs hlen hint hrs_nonpos⟩⟩
    · have : ss.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf]
      have : rs.length = g.natDegree := by
        rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg]
      lia
  · -- Backward: Prec g (X * f) → Prec f g
    intro ⟨_, _, ss_g, rs_xf, hss_g, hrs_xf, hss_g_eq, hrs_xf_eq, hcase⟩
    rcases hcase with ⟨hlen, _⟩ | ⟨hlen, halt⟩
    · have : ss_g.length = g.natDegree := by
        rw [← Multiset.coe_card, hss_g_eq, card_roots_of_splits hg]
      have : rs_xf.length = (X * f).natDegree := by
        rw [← Multiset.coe_card, hrs_xf_eq, card_roots_of_splits (by simp_all)]
      lia
    · set ss_f := f.roots.sort (· ≤ ·)
      have hss_f_eq : (↑ss_f : Multiset ℝ) = f.roots := Multiset.sort_eq ..
      have hss_f_sorted : ss_f.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
      have hrs_xf_is : rs_xf = ss_f ++ [(0 : ℝ)] := by
        have hmultiset_eq : (↑rs_xf : Multiset ℝ) = ↑(ss_f ++ [(0 : ℝ)]) := by
          rw [hrs_xf_eq, hXf_roots, ← hss_f_eq, ← Multiset.coe_add]; simp [add_comm]
        have hsorted_concat : (ss_f ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by
          rw [List.pairwise_append]
          exact ⟨hss_f_sorted, List.pairwise_singleton _ _, fun a ha _ hb => by
            simp only [List.mem_singleton] at hb; rw [hb]
            exact hf_nonpos a (by rw [← hss_f_eq]; exact Multiset.mem_coe.mpr ha)⟩
        exact List.Perm.eq_of_pairwise' hrs_xf hsorted_concat
          (Multiset.coe_eq_coe.mp hmultiset_eq)
      rw [hrs_xf_is] at halt
      have hlen' : ss_f.length + 1 = ss_g.length := by simp_all
      exact
        ⟨⟨hf₀, hf⟩, ⟨hg₀, hg⟩, ss_f, ss_g, hss_f_sorted, hss_g, hss_f_eq,
          hss_g_eq,
          Or.inl ⟨by lia, listInterlaces_of_listAlternates_append_zero ss_f ss_g hlen' halt⟩⟩

theorem prec_sameDegree_to_prec_mul_X_of_roots_nonpos {f g : ℝ[X]}
    (h : Prec f g)
    (hdeg : f.natDegree = g.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    Prec g (X * f) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  have hXf_rr : (X * f) ≠ 0 ∧ (X * f).Splits := by simp_all
  have hXf_roots : (X * f).roots = {0} + f.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hf.1), roots_X]
  have hss_nonpos : ∀ s ∈ ss, s ≤ 0 := fun s hs =>
    hf_nonpos s (by rw [← hss_eq]; exact Multiset.mem_coe.mpr hs)
  have hss0_sorted : (ss ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  have hss0_eq : (↑(ss ++ [(0 : ℝ)]) : Multiset ℝ) = (X * f).roots := by
    have : (↑(ss ++ [(0 : ℝ)]) : Multiset ℝ) = (↑ss : Multiset ℝ) + {(0 : ℝ)} := by
      rw [← Multiset.coe_add]
      simp
    grind
  rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · have hss_len : ss.length = f.natDegree := by
      rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
    have hrs_len : rs.length = g.natDegree := by
      rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
    lia
  · refine ⟨hg, hXf_rr, rs, ss ++ [0], hrs, hss0_sorted, hrs_eq, hss0_eq, Or.inl ?_⟩
    refine ⟨?_, listInterlaces_right_of_listAlternates_append_zero ss rs ?_ halt ?_⟩
    · simp_all
    · lia
    · intro r hr
      exact hg_nonpos r (by rw [← hrs_eq]; exact Multiset.mem_coe.mpr hr)

theorem prec_of_prec_mul_X_sameDegree_of_roots_nonpos {f g : ℝ[X]}
    (h : Prec g (X * f))
    (hdeg : f.natDegree = g.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0) :
    Prec f g := by
  rcases h with
    ⟨hg, hXf, ss_g, rs_Xf, hss_g, hrs_Xf, hss_g_eq, hrs_Xf_eq, hshape⟩
  have hf : f ≠ 0 ∧ f.Splits := by simp_all
  set rs_f := f.roots.sort (· ≤ ·)
  have hrs_f_eq : (↑rs_f : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_f : rs_f.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_f_nonpos : ∀ r ∈ rs_f, r ≤ 0 :=
    fun r hr => hf_nonpos r (by rw [← hrs_f_eq]; exact Multiset.mem_coe.mpr hr)
  have hrs_f0 : (rs_f ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  have hXf_roots : (X * f).roots = {0} + f.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hf.1), roots_X]
  have hrs_Xf_is : rs_Xf = rs_f ++ [(0 : ℝ)] := by
    have hmultiset_eq : (↑rs_Xf : Multiset ℝ) = ↑(rs_f ++ [(0 : ℝ)]) := by
      rw [hrs_Xf_eq, hXf_roots, ← hrs_f_eq, ← Multiset.coe_add]
      simp [add_comm]
    exact List.Perm.eq_of_pairwise' hrs_Xf hrs_f0 (Multiset.coe_eq_coe.mp hmultiset_eq)
  have hlen_fg : rs_f.length = ss_g.length := by
    rw [← Multiset.coe_card, hrs_f_eq, card_roots_of_splits hf.2,
      ← Multiset.coe_card, hss_g_eq, card_roots_of_splits hg.2, hdeg]
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, _⟩
  · rw [hrs_Xf_is] at hint hlen
    have hlen' : ss_g.length + 1 = (rs_f ++ [(0 : ℝ)]).length := by lia
    have hrs_f0_nonpos : ∀ r ∈ rs_f ++ [(0 : ℝ)], r ≤ 0 := by grind
    have halt0 :
        ListAlternates (rs_f ++ [(0 : ℝ)]) (ss_g ++ [(0 : ℝ)]) :=
      listAlternates_append_zero ss_g (rs_f ++ [(0 : ℝ)]) hlen' hint hrs_f0_nonpos
    have halt : ListAlternates rs_f ss_g :=
      listAlternates_of_append_zero_both rs_f ss_g hlen_fg halt0
    exact ⟨hf, hg, rs_f, ss_g, hrs_f, hss_g, hrs_f_eq, hss_g_eq,
      Or.inr ⟨hlen_fg, halt⟩⟩
  · simp_all

theorem prec_iff_prec_mul_X_of_roots_nonpos {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Prec f g ↔ Prec g (X * f) := by
  have ⟨hfnn, hf₀⟩ := (hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hf).mpr
    ⟨hf_pos, hf_nonpos⟩
  have ⟨hgnn, hg₀⟩ := (hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hg).mpr
    ⟨hg_pos, hg_nonpos⟩
  exact prec_iff_prec_mul_X hfnn hgnn hf₀ hf hg₀ hg hdeg

/-- Nonnegative-coefficients form of Wagner (3): if `f ≪ g` and both
polynomials have nonnegative coefficients, then `g ≪ X * f`. This packages
the differ-by-1 and same-degree cases under one theorem. -/
theorem prec_mul_X_of_prec_of_nonneg {f g : ℝ[X]}
    (h : Prec f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec g (X * f) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf.2 hfnn
  have hg_nonpos : ∀ r ∈ g.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hg.2 hgnn
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · have hdeg : f.natDegree + 1 = g.natDegree := by
      have hss_len : ss.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
      have hrs_len : rs.length = g.natDegree := by
        rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
      lia
    exact (prec_iff_prec_mul_X_of_roots_nonpos hf.2 hg.2 (hfnn.pos_leadingCoeff hf.1)
      (hgnn.pos_leadingCoeff hg.1) hf_nonpos hg_nonpos hdeg).mp
        ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, Or.inl ⟨hlen, hint⟩⟩
  · have hdeg : f.natDegree = g.natDegree := by
      have hss_len : ss.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
      have hrs_len : rs.length = g.natDegree := by
        rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
      lia
    exact
      prec_sameDegree_to_prec_mul_X_of_roots_nonpos
        ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, Or.inr ⟨hlen, halt⟩⟩
        hdeg hf_nonpos hg_nonpos

/-- Nonzero scalar form of the Wagner `X`-shift bridge. -/
theorem prec_C_mul_X_of_prec_of_nonneg {f g : ℝ[X]} {c : ℝ}
    (h : Prec f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hc : c ≠ 0) :
    Prec g ((C c * X) * f) := by
  simpa [mul_assoc] using
    (prec_C_mul_right (prec_mul_X_of_prec_of_nonneg h hfnn hgnn) hc)

/-- Zero-aware Wagner (3): if `f ≪₀ g` and both polynomials have nonnegative
coefficients, then `g ≪₀ X * f`. -/
theorem prec0_mul_X_of_prec0 {f g : ℝ[X]}
    (h : Prec0 f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec0 g (X * f) := by
  rcases h with rfl | rfl | hfg
  · simpa using prec0_zero_right g
  · exact prec0_zero_left (X * f)
  · exact (prec_mul_X_of_prec_of_nonneg hfg hfnn hgnn).toPrec0

theorem prec_mul_X_both_of_roots_nonpos {f g : ℝ[X]} (h : Prec f g)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    Prec (X * f) (X * g) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  have hXf : (X * f) ≠ 0 ∧ (X * f).Splits := by simp_all
  have hXg : (X * g) ≠ 0 ∧ (X * g).Splits := by simp_all
  have hXf_roots : (X * f).roots = {0} + f.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hf.1), roots_X]
  have hXg_roots : (X * g).roots = {0} + g.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hg.1), roots_X]
  have hss_nonpos : ∀ s ∈ ss, s ≤ 0 := fun s hs =>
    hf_nonpos s (by rw [← hss_eq]; exact Multiset.mem_coe.mpr hs)
  have hrs_nonpos : ∀ r ∈ rs, r ≤ 0 := fun r hr =>
    hg_nonpos r (by rw [← hrs_eq]; exact Multiset.mem_coe.mpr hr)
  have hss0_sorted : (ss ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  have hrs0_sorted : (rs ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  refine ⟨hXf, hXg, ss ++ [0], rs ++ [0], hss0_sorted, hrs0_sorted, ?_, ?_, ?_⟩
  · have : (↑(ss ++ [(0 : ℝ)]) : Multiset ℝ) = (↑ss : Multiset ℝ) + {(0 : ℝ)} := by
      rw [← Multiset.coe_add]
      simp
    grind
  · have : (↑(rs ++ [(0 : ℝ)]) : Multiset ℝ) = (↑rs : Multiset ℝ) + {(0 : ℝ)} := by
      rw [← Multiset.coe_add]
      simp
    grind
  · rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
    · exact Or.inl
        ⟨by simp_all, listInterlaces_append_zero_both ss rs hlen hint hrs_nonpos⟩
    · exact Or.inr
        ⟨by simp_all, listAlternates_append_zero_both ss rs hlen halt hrs_nonpos⟩

theorem prec_of_prec_mul_X_both_of_roots_nonpos {f g : ℝ[X]}
    (h : Prec (X * f) (X * g))
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    Prec f g := by
  rcases h with ⟨hXf, hXg, ss_xf, rs_xg, hss_xf, hrs_xg, hss_xf_eq, hrs_xg_eq, hcase⟩
  have hf : f ≠ 0 ∧ f.Splits := by simp_all
  have hg : g ≠ 0 ∧ g.Splits := by simp_all
  have hXf_roots : (X * f).roots = {0} + f.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hf.1), roots_X]
  have hXg_roots : (X * g).roots = {0} + g.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hg.1), roots_X]
  set ss_f := f.roots.sort (· ≤ ·)
  set rs_g := g.roots.sort (· ≤ ·)
  have hss_f_eq : (↑ss_f : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_g_eq : (↑rs_g : Multiset ℝ) = g.roots := Multiset.sort_eq ..
  have hss_f_sorted : ss_f.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_g_sorted : rs_g.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hss_f_nonpos : ∀ s ∈ ss_f, s ≤ 0 := fun s hs =>
    hf_nonpos s (by rw [← hss_f_eq]; exact Multiset.mem_coe.mpr hs)
  have hrs_g_nonpos : ∀ r ∈ rs_g, r ≤ 0 := fun r hr =>
    hg_nonpos r (by rw [← hrs_g_eq]; exact Multiset.mem_coe.mpr hr)
  have hss_f0_sorted : (ss_f ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  have hrs_g0_sorted : (rs_g ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  have hss_xf_is : ss_xf = ss_f ++ [(0 : ℝ)] := by
    have hmultiset_eq : (↑ss_xf : Multiset ℝ) = ↑(ss_f ++ [(0 : ℝ)]) := by
      rw [hss_xf_eq, hXf_roots, ← hss_f_eq, ← Multiset.coe_add]
      simp [add_comm]
    exact List.Perm.eq_of_pairwise' hss_xf hss_f0_sorted (Multiset.coe_eq_coe.mp hmultiset_eq)
  have hrs_xg_is : rs_xg = rs_g ++ [(0 : ℝ)] := by
    have hmultiset_eq : (↑rs_xg : Multiset ℝ) = ↑(rs_g ++ [(0 : ℝ)]) := by
      rw [hrs_xg_eq, hXg_roots, ← hrs_g_eq, ← Multiset.coe_add]
      simp [add_comm]
    exact List.Perm.eq_of_pairwise' hrs_xg hrs_g0_sorted (Multiset.coe_eq_coe.mp hmultiset_eq)
  rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · rw [hss_xf_is, hrs_xg_is] at hint hlen
    have hlen' : ss_f.length + 1 = rs_g.length := by simp_all
    exact ⟨hf, hg, ss_f, rs_g, hss_f_sorted, hrs_g_sorted, hss_f_eq, hrs_g_eq,
      Or.inl ⟨hlen', listInterlaces_of_append_zero_both ss_f rs_g hlen' hint⟩⟩
  · rw [hss_xf_is, hrs_xg_is] at halt hlen
    have hlen' : ss_f.length = rs_g.length := by simp_all
    exact ⟨hf, hg, ss_f, rs_g, hss_f_sorted, hrs_g_sorted, hss_f_eq, hrs_g_eq,
      Or.inr ⟨hlen', listAlternates_of_append_zero_both ss_f rs_g hlen' halt⟩⟩

/-- Nonnegative-coefficient form of the common-factor Wagner `X` bridge. -/
theorem prec_mul_X_both_of_prec_of_nonneg {f g : ℝ[X]}
    (h : Prec f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec (X * f) (X * g) :=
  prec_mul_X_both_of_roots_nonpos h
    (roots_nonpos_of_nonneg_coeffs h.1.2 hfnn)
    (roots_nonpos_of_nonneg_coeffs h.2.1.2 hgnn)

theorem prec_iff_prec_mul_X_both_of_roots_nonpos {f g : ℝ[X]}
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    Prec f g ↔ Prec (X * f) (X * g) :=
  ⟨fun h => prec_mul_X_both_of_roots_nonpos h hf_nonpos hg_nonpos,
    fun h => prec_of_prec_mul_X_both_of_roots_nonpos h hf_nonpos hg_nonpos⟩

theorem prec0_mul_X_both_of_nonneg {f g : ℝ[X]}
    (h : Prec0 f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec0 (X * f) (X * g) := by
  rcases h with rfl | rfl | hfg
  · simpa using prec0_zero_left (X * g)
  · simpa using prec0_zero_right (X * f)
  · exact
      (prec_mul_X_both_of_roots_nonpos hfg
        (roots_nonpos_of_nonneg_coeffs hfg.1.2 hfnn)
        (roots_nonpos_of_nonneg_coeffs hfg.2.1.2 hgnn)).toPrec0

theorem prec0_of_prec0_mul_X_both_of_nonneg {f g : ℝ[X]}
    (h : Prec0 (X * f) (X * g)) (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    Prec0 f g := by
  by_cases hf0 : f = 0
  · simpa [hf0] using prec0_zero_left g
  by_cases hg0 : g = 0
  · simpa [hg0] using prec0_zero_right f
  have hXf0 : X * f ≠ 0 := mul_ne_zero X_ne_zero hf0
  have hXg0 : X * g ≠ 0 := mul_ne_zero X_ne_zero hg0
  have hstrict : Prec (X * f) (X * g) := h.toPrec_of_ne hXf0 hXg0
  have hf : f ≠ 0 ∧ f.Splits := isRealRooted_of_X_mul hstrict.1.1 hstrict.1.2
  have hg : g ≠ 0 ∧ g.Splits := isRealRooted_of_X_mul hstrict.2.1.1 hstrict.2.1.2
  exact
    (prec_of_prec_mul_X_both_of_roots_nonpos hstrict
      (roots_nonpos_of_nonneg_coeffs hf.2 hfnn)
      (roots_nonpos_of_nonneg_coeffs hg.2 hgnn)).toPrec0

theorem prec0_iff_prec0_mul_X_both_of_nonneg {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec0 f g ↔ Prec0 (X * f) (X * g) :=
  ⟨fun h => prec0_mul_X_both_of_nonneg h hfnn hgnn,
    fun h => prec0_of_prec0_mul_X_both_of_nonneg h hfnn hgnn⟩

end RealRooted
