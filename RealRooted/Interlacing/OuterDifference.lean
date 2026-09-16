import RealRooted.MaWang
import RealRooted.ObreschkoffConverse
import RealRooted.PosCombo
import RealRooted.Interlacing.Multiplicity
import RealRooted.Interlacing.Residue
import RealRooted.WagnerRightSum.Sign

/-!
# Outer differences in an ordered proper-position triple

This file proves the signed-cone specialization used in Brändén--Vecchi's
Chow-operator argument.  In the positive-leading root-order convention, the
paper's two signed relations `g ≺ -f` and `g ≺ h` become the ordered triple
`f ≪ g ≪ h`.  If `h - f` retains positive leading sign, then it lies to the
right of the middle polynomial.
-/

open Polynomial

noncomputable section

namespace RealRooted

private lemma list_eq_of_forall₂_le_of_sum_eq :
    ∀ {xs ys : List ℝ},
      List.Forall₂ (fun x y : ℝ => x ≤ y) xs ys →
      xs.sum = ys.sum → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hxy, hsum => by
      simp only [List.forall₂_cons] at hxy
      simp only [List.sum_cons] at hsum
      have htail : xs.sum ≤ ys.sum := List.Forall₂.sum_le_sum hxy.2
      have hhead : x = y := by linarith
      subst y
      have hsum_tail : xs.sum = ys.sum := by linarith
      rw [list_eq_of_forall₂_le_of_sum_eq hxy.2 hsum_tail]

/-- Equality in the root-sum order of a same-degree proper-position pair,
together with equality of leading coefficients, forces equality of the
polynomials. -/
theorem eq_of_prec_sameDegree_of_leadingCoeff_eq_of_roots_sum_eq
    {f g : ℝ[X]}
    (hprec : Prec f g) (hdeg : f.natDegree = g.natDegree)
    (hlc : f.leadingCoeff = g.leadingCoeff)
    (hsum : f.roots.sum = g.roots.sum) :
    f = g := by
  rcases hprec with ⟨hf, hg, ss, rs, _hss_sorted, _hrs_sorted,
    hss_eq, hrs_eq, hshape⟩
  have hlen_ss : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hlen_rs : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  have halt : ListAlternates ss rs := by simp_all
  have hlist : ss = rs := by
    apply list_eq_of_forall₂_le_of_sum_eq (listAlternates_forall₂_le halt)
    rw [← Multiset.sum_coe, hss_eq, ← Multiset.sum_coe, hrs_eq]
    exact hsum
  have hroots : f.roots = g.roots := by
    rw [← hss_eq, ← hrs_eq, hlist]
  rw [hf.2.eq_prod_roots, hg.2.eq_prod_roots, hlc, hroots]

/-- At a root of the right polynomial in a positive-leading proper-position
pair, the left value and right derivative have nonnegative product. -/
theorem eval_mul_derivative_nonneg_of_prec_right_root
    {f g : ℝ[X]} (hprec : Prec f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {r : ℝ} (hr : g.IsRoot r) :
    0 ≤ f.eval r * g.derivative.eval r := by
  have hr_mem : r ∈ g.roots := (mem_roots hprec.2.1.1).mpr hr
  have hgdeg_pos : 0 < g.natDegree := by
    have hroots_ne : g.roots ≠ 0 := by
      intro hzero
      rw [hzero] at hr_mem
      simp at hr_mem
    have hcard_pos : 0 < g.roots.card := Multiset.card_pos.mpr hroots_ne
    rwa [card_roots_of_splits hprec.2.1.2] at hcard_pos
  have hgder_pos : HasPosLeadingCoeff g.derivative :=
    hg_pos.derivative (by lia)
  have hder_prec : Prec g.derivative g := by
    rcases eq_or_lt_of_le (show 1 ≤ g.natDegree by lia) with hdeg_one | hdeg_two
    · have hbase : Prec (1 : ℝ[X]) g :=
        (interlaces_one_linear (by lia)).toPrec
      have hder_deg : g.derivative.natDegree = 0 := by
        rw [g.natDegree_derivative]
        lia
      have hder_C : g.derivative = C (g.derivative.coeff 0) :=
        eq_C_of_natDegree_eq_zero hder_deg
      have hcoeff_pos : 0 < g.derivative.coeff 0 := by
        unfold HasPosLeadingCoeff at hgder_pos
        rw [leadingCoeff, hder_deg] at hgder_pos
        exact hgder_pos
      rw [hder_C]
      simpa using prec_C_mul_left hbase (ne_of_gt hcoeff_pos)
    · exact (derivative_interlaces hprec.2.1.2 (by lia)).toPrec
  exact
    eval_mul_eval_nonneg_of_prec_right
      hprec hder_prec hf_pos hgder_pos hr

/-- At a root of the left polynomial in a positive-leading proper-position
pair, the right value and left derivative have nonpositive product. -/
theorem eval_mul_derivative_nonpos_of_prec_left_root
    {f g : ℝ[X]} (hprec : Prec f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    {r : ℝ} (hr : f.IsRoot r) :
    g.eval r * f.derivative.eval r ≤ 0 := by
  obtain ⟨bf, hbf⟩ := exists_root_upper_bound f
  obtain ⟨bg, hbg⟩ := exists_root_upper_bound g
  let b : ℝ := max bf bg + 1
  have hf_le : ∀ x ∈ f.roots, x ≤ b := by
    intro x hx
    exact (hbf x hx).trans (by dsimp [b]; linarith [le_max_left bf bg])
  have hg_le : ∀ x ∈ g.roots, x ≤ b := by
    intro x hx
    exact (hbg x hx).trans (by dsimp [b]; linarith [le_max_right bf bg])
  have hr_lt : r < b := by
    have hr_mem : r ∈ f.roots := (mem_roots hprec.1.1).mpr hr
    have := hbf r hr_mem
    dsimp [b]
    linarith [le_max_left bf bg]
  have hpad : Prec g ((X - C b) * f) := by
    rcases hprec.natDegree_eq_or_eq_succ with hsame | hsucc
    · exact prec_sameDegree_to_prec_mul_X_sub_C_of_roots_le
        b hprec hsame.symm hf_pos hg_pos hf_le hg_le
    · exact (prec_iff_prec_mul_X_sub_C_of_roots_le
        b hprec.1.2 hprec.2.1.2 hf_pos hg_pos hf_le hg_le (by lia)).mp hprec
  have hpad_pos : HasPosLeadingCoeff ((X - C b) * f) :=
    hasPosLeadingCoeff_X_sub_C_mul hf_pos
  have hroot_pad : ((X - C b) * f).IsRoot r := by
    simp [Polynomial.IsRoot.def, Polynomial.IsRoot.def.mp hr]
  have hsign :=
    eval_mul_derivative_nonneg_of_prec_right_root
      hpad hg_pos hpad_pos hroot_pad
  have hder_eval : ((X - C b) * f).derivative.eval r =
      (r - b) * f.derivative.eval r := by
    rw [derivative_mul]
    simp [Polynomial.IsRoot.def.mp hr]
  rw [hder_eval] at hsign
  nlinarith

/-- Values of the two outer members of a positive-leading ordered triple have
opposite-or-zero signs at every root of the middle member. -/
theorem eval_mul_eval_nonpos_of_prec_sandwich
    {f g h : ℝ[X]} (hfg : Prec f g) (hgh : Prec g h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hh_pos : HasPosLeadingCoeff h)
    {r : ℝ} (hr : g.IsRoot r) :
    f.eval r * h.eval r ≤ 0 := by
  by_cases hsimple : g.rootMultiplicity r = 1
  · have hder_ne : g.derivative.eval r ≠ 0 :=
      eval_derivative_ne_zero_of_rootMultiplicity_eq_one hr hsimple
    have hleft : 0 ≤ f.eval r * g.derivative.eval r :=
      eval_mul_derivative_nonneg_of_prec_right_root hfg hf_pos hg_pos hr
    have hright : h.eval r * g.derivative.eval r ≤ 0 :=
      eval_mul_derivative_nonpos_of_prec_left_root hgh hg_pos hh_pos hr
    rcases lt_or_gt_of_ne hder_ne with hneg | hpos
    · have hf_nonpos : f.eval r ≤ 0 := by nlinarith
      have hh_nonneg : 0 ≤ h.eval r := by nlinarith
      exact mul_nonpos_of_nonpos_of_nonneg hf_nonpos hh_nonneg
    · have hf_nonneg : 0 ≤ f.eval r := by nlinarith
      have hh_nonpos : h.eval r ≤ 0 := by nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos hf_nonneg hh_nonpos
  · have hmult : 2 ≤ g.rootMultiplicity r := by
      have hpos := (rootMultiplicity_pos hfg.2.1.1).mpr hr
      lia
    have hf_mult : 1 ≤ f.rootMultiplicity r := by
      have := (rootMultiplicity_bounds_of_prec hfg r).2
      lia
    have hh_mult : 1 ≤ h.rootMultiplicity r := by
      have := (rootMultiplicity_bounds_of_prec hgh r).1
      lia
    have hfr : f.IsRoot r := (rootMultiplicity_pos hfg.1.1).mp (by lia)
    have hhr : h.IsRoot r := (rootMultiplicity_pos hgh.2.1.1).mp (by lia)
    simp [Polynomial.IsRoot.def.mp hfr, Polynomial.IsRoot.def.mp hhr]

private theorem natDegree_sub_lower_bound_of_prec_triple
    {f g h : ℝ[X]} (hfg : Prec f g) (hgh : Prec g h) (hfh : Prec f h)
    (hf_pos : HasPosLeadingCoeff f) (hh_pos : HasPosLeadingCoeff h)
    (hsub_pos : HasPosLeadingCoeff (h - f)) :
    g.natDegree ≤ (h - f).natDegree := by
  have hfg_bounds := natDegree_bounds_of_prec hfg
  have hgh_bounds := natDegree_bounds_of_prec hgh
  have hfh_bounds := natDegree_bounds_of_prec hfh
  rcases hfh.natDegree_eq_or_eq_succ with hsame | hsucc
  · have hdeg : f.natDegree = h.natDegree := hsame.symm
    have hlc_gt : f.leadingCoeff < h.leadingCoeff := by
      by_contra hnot
      have hlc_le : h.leadingCoeff ≤ f.leadingCoeff := le_of_not_gt hnot
      rcases eq_or_lt_of_le hlc_le with hlc_eq | hlc_lt
      · have hroots_le := roots_sum_le_of_prec_sameDegree hfh hdeg
        rcases eq_or_lt_of_le hroots_le with hroots_eq | hroots_lt
        · have hEq :=
            eq_of_prec_sameDegree_of_leadingCoeff_eq_of_roots_sum_eq
              hfh hdeg hlc_eq.symm hroots_eq
          rw [hEq, sub_self] at hsub_pos
          simp [HasPosLeadingCoeff] at hsub_pos
        · have hf_vieta :=
            hfh.1.2.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
          have hh_vieta :=
            hfh.2.1.2.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
          have hnext_lt : h.nextCoeff < f.nextCoeff := by
            have hflc_pos : 0 < f.leadingCoeff := hf_pos
            rw [hf_vieta, hh_vieta, hlc_eq]
            nlinarith
          have hdeg_pos : 0 < f.natDegree := by
            by_contra hzero
            have hfdeg0 : f.natDegree = 0 := by lia
            have hhdeg0 : h.natDegree = 0 := by lia
            rw [eq_C_of_natDegree_eq_zero hfdeg0,
              eq_C_of_natDegree_eq_zero hhdeg0] at hroots_lt
            simp at hroots_lt
          have hcoeff_neg : (h - f).coeff (f.natDegree - 1) < 0 := by
            have hhdeg_pos : 0 < h.natDegree := by lia
            simpa [Polynomial.nextCoeff, ne_of_gt hdeg_pos,
              ne_of_gt hhdeg_pos, hdeg] using hnext_lt
          have htop_zero : (h - f).coeff f.natDegree = 0 := by
            rw [coeff_sub]
            change h.coeff f.natDegree - f.leadingCoeff = 0
            rw [show h.coeff f.natDegree = h.leadingCoeff by rw [hdeg]; rfl,
              hlc_eq]
            simp
          have hsub_deg_lt : (h - f).natDegree < f.natDegree := by
            apply (natDegree_lt_iff_degree_lt hsub_pos.ne_zero).mpr
            rw [Polynomial.degree_lt_iff_coeff_zero]
            intro m hm
            rcases eq_or_lt_of_le hm with rfl | hm
            · exact htop_zero
            · have hfzero : f.coeff m = 0 := coeff_eq_zero_of_natDegree_lt hm
              have hhzero : h.coeff m = 0 :=
                coeff_eq_zero_of_natDegree_lt (by lia)
              simp [hfzero, hhzero]
          have hsub_deg : (h - f).natDegree = f.natDegree - 1 := by
            apply le_antisymm
            · lia
            · exact le_natDegree_of_ne_zero (ne_of_lt hcoeff_neg)
          have : (h - f).leadingCoeff < 0 := by
            rw [leadingCoeff, hsub_deg]
            exact hcoeff_neg
          change 0 < (h - f).leadingCoeff at hsub_pos
          linarith
      · have hdegree : h.degree = f.degree := by
          rw [degree_eq_natDegree hh_pos.ne_zero, degree_eq_natDegree hf_pos.ne_zero,
            hdeg.symm]
        have hlc_sub : (h - f).leadingCoeff = h.leadingCoeff - f.leadingCoeff :=
          leadingCoeff_sub_of_degree_eq hdegree (by linarith)
        change 0 < (h - f).leadingCoeff at hsub_pos
        linarith
    have hdegree : h.degree = f.degree := by
      rw [degree_eq_natDegree hh_pos.ne_zero, degree_eq_natDegree hf_pos.ne_zero,
        hdeg.symm]
    have hsub_lc : (h - f).leadingCoeff = h.leadingCoeff - f.leadingCoeff :=
      leadingCoeff_sub_of_degree_eq hdegree (by linarith)
    have hsub_deg : (h - f).natDegree = h.natDegree := by
      apply le_antisymm
      · exact (natDegree_sub_le h f).trans (by simp [hdeg])
      · apply le_natDegree_of_ne_zero
        rw [show (h - f).coeff h.natDegree = h.leadingCoeff - f.leadingCoeff by
          rw [coeff_sub, coeff_natDegree]
          change h.leadingCoeff - f.coeff h.natDegree = _
          rw [← hdeg]
          rfl]
        exact ne_of_gt (sub_pos.mpr hlc_gt)
    lia
  · have hdeg : h.natDegree = f.natDegree + 1 := hsucc
    have hsub_deg : (h - f).natDegree = h.natDegree := by
      rw [natDegree_sub_eq_left_of_natDegree_lt (by lia)]
    lia

private theorem natDegree_sub_upper_bound_of_prec_triple
    {f g h : ℝ[X]} (hfg : Prec f g) (hgh : Prec g h) :
    (h - f).natDegree ≤ g.natDegree + 1 := by
  have hf_le : f.natDegree ≤ g.natDegree := (natDegree_bounds_of_prec hfg).1
  have hh_le : h.natDegree ≤ g.natDegree + 1 := (natDegree_bounds_of_prec hgh).2
  exact (natDegree_sub_le h f).trans
    (max_le hh_le (hf_le.trans (Nat.le_succ _)))

/-- **Signed outer-difference cone.**  Let `f`, `g`, and `h` be an ordered
positive-leading proper-position triple.  If the outer difference has positive
leading coefficient, then the middle polynomial precedes that difference.

The proof does not assume that `h - f` splits.  Splitting comes from the outer
Obreschkoff pencil.  Repeated roots of the middle polynomial are removed
recursively; in the simple-root case, derivative interlacing and the two
endpoint sign lemmas give the Liu--Wang root certificate. -/
theorem prec_sub_of_prec_triple_of_posLeadingCoeff
    {f g h : ℝ[X]} (hfg : Prec f g) (hgh : Prec g h) (hfh : Prec f h)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hh_pos : HasPosLeadingCoeff h)
    (hsub_pos : HasPosLeadingCoeff (h - f)) :
    Prec g (h - f) := by
  classical
  refine Nat.strong_induction_on
    (p := fun n => ∀ {f g h : ℝ[X]}, g.natDegree = n →
      Prec f g → Prec g h → Prec f h →
      HasPosLeadingCoeff f → HasPosLeadingCoeff g → HasPosLeadingCoeff h →
      HasPosLeadingCoeff (h - f) → Prec g (h - f))
    g.natDegree ?_ rfl hfg hgh hfh hf_pos hg_pos hh_pos hsub_pos
  intro n ih f g h hgdeg hfg hgh hfh hf_pos hg_pos hh_pos hsub_pos
  by_cases hdup : ¬g.roots.Nodup
  · rw [Multiset.nodup_iff_count_le_one] at hdup
    push Not at hdup
    obtain ⟨r, hcount⟩ := hdup
    let qf : ℝ[X] := f /ₘ (X - C r)
    let qg : ℝ[X] := g /ₘ (X - C r)
    let qh : ℝ[X] := h /ₘ (X - C r)
    have hg_mult : 2 ≤ g.rootMultiplicity r := by
      rw [← count_roots]
      exact hcount
    have hrg' : g.IsRoot r :=
      (rootMultiplicity_pos hfg.2.1.1).mp (by lia)
    have hf_mult : 1 ≤ f.rootMultiplicity r := by
      have := (rootMultiplicity_bounds_of_prec hfg r).2
      lia
    have hrf' : f.IsRoot r :=
      (rootMultiplicity_pos hfg.1.1).mp (by lia)
    have hh_mult : 1 ≤ h.rootMultiplicity r := by
      have := (rootMultiplicity_bounds_of_prec hgh r).1
      lia
    have hrh' : h.IsRoot r := (rootMultiplicity_pos hgh.2.1.1).mp (by lia)
    have hffactor : f = (X - C r) * qf := by
      exact (mul_divByMonic_eq_iff_isRoot.mpr hrf').symm
    have hgfactor : g = (X - C r) * qg := by
      exact (mul_divByMonic_eq_iff_isRoot.mpr hrg').symm
    have hhfactor : h = (X - C r) * qh := by
      exact (mul_divByMonic_eq_iff_isRoot.mpr hrh').symm
    have hqfg : Prec qf qg := prec_cofactor_of_common_root hfg hrg' hrf'
    have hqgh : Prec qg qh := prec_cofactor_of_common_root hgh hrh' hrg'
    have hqfh : Prec qf qh := prec_cofactor_of_common_root hfh hrh' hrf'
    have hqf_pos : HasPosLeadingCoeff qf := hf_pos.divByMonic_X_sub_C hrf'
    have hqg_pos : HasPosLeadingCoeff qg := hg_pos.divByMonic_X_sub_C hrg'
    have hqh_pos : HasPosLeadingCoeff qh := hh_pos.divByMonic_X_sub_C hrh'
    have hsub_factor : h - f = (X - C r) * (qh - qf) := by
      rw [hffactor, hhfactor]
      ring
    have hqsub_pos : HasPosLeadingCoeff (qh - qf) := by
      apply hasPosLeadingCoeff_of_X_sub_C_mul
      simpa [hsub_factor] using hsub_pos
    have hqg_deg : qg.natDegree + 1 = g.natDegree := by
      rw [hgfactor, natDegree_mul (X_sub_C_ne_zero r) hqg_pos.ne_zero,
        natDegree_X_sub_C]
      lia
    have hqprec : Prec qg (qh - qf) :=
      ih qg.natDegree (by lia) rfl hqfg hqgh hqfh
        hqf_pos hqg_pos hqh_pos hqsub_pos
    have hmul :=
      prec_mul_common_factor
        (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hqprec
    simpa [hgfactor, hsub_factor] using hmul
  · have hg_nodup : g.roots.Nodup := not_not.mp hdup
    have hsub_splits : (h - f).Splits := by
      have hall := allComboRealRooted_of_prec hfh
      simpa [sub_eq_add_neg, add_comm, mul_comm] using hall (-1) 1
    have hdeg_lo : g.natDegree ≤ (h - f).natDegree :=
      natDegree_sub_lower_bound_of_prec_triple
        hfg hgh hfh hf_pos hh_pos hsub_pos
    have hdeg_hi : (h - f).natDegree ≤ g.natDegree + 1 :=
      natDegree_sub_upper_bound_of_prec_triple hfg hgh
    by_cases hgzero : g.natDegree = 0
    · have hsub_cases : (h - f).natDegree = 0 ∨ (h - f).natDegree = 1 := by lia
      rcases hsub_cases with hsub_zero | hsub_one
      · have hgC : g = C (g.coeff 0) := eq_C_of_natDegree_eq_zero hgzero
        have hdC : h - f = C ((h - f).coeff 0) :=
          eq_C_of_natDegree_eq_zero hsub_zero
        have hbase : Prec (1 : ℝ[X]) (1 : ℝ[X]) := prec_refl (by simp) (by simp)
        have hgcoeff : g.coeff 0 ≠ 0 := by
          intro hc
          apply hg_pos.ne_zero
          rw [hgC, hc]
          simp
        have hdcoeff : (h - f).coeff 0 ≠ 0 := by
          intro hc
          apply hsub_pos.ne_zero
          rw [hdC, hc]
          simp
        rw [hgC, hdC]
        simpa only [mul_one] using
          prec_C_mul_right (prec_C_mul_left hbase hgcoeff) hdcoeff
      · have hbase : Prec (1 : ℝ[X]) (h - f) :=
          (interlaces_one_linear hsub_one).toPrec
        have hgC : g = C (g.coeff 0) := eq_C_of_natDegree_eq_zero hgzero
        have hgcoeff : g.coeff 0 ≠ 0 := by
          intro hc
          apply hg_pos.ne_zero
          rw [hgC, hc]
          simp
        rw [hgC]
        simpa only [mul_one] using prec_C_mul_left hbase hgcoeff
    · have hgdeg_pos : 0 < g.natDegree := Nat.pos_of_ne_zero hgzero
      have hgder_pos : HasPosLeadingCoeff g.derivative :=
        hg_pos.derivative hgzero
      have hder_inter : Interlaces g.derivative g := by
        rcases eq_or_lt_of_le (show 1 ≤ g.natDegree by lia) with hone | htwo
        · have hbase := interlaces_one_linear (p := g) (by lia)
          have hder_deg : g.derivative.natDegree = 0 := by
            rw [g.natDegree_derivative]
            lia
          have hderC : g.derivative = C (g.derivative.coeff 0) :=
            eq_C_of_natDegree_eq_zero hder_deg
          have hc : g.derivative.coeff 0 ≠ 0 := by
            intro hc
            apply hgder_pos.ne_zero
            rw [hderC, hc]
            simp
          rw [hderC]
          exact interlaces_C_linear hc (by lia)
        · exact derivative_interlaces hfg.2.1.2 (by lia)
      have hno : ∀ r, g.IsRoot r → ¬g.derivative.IsRoot r := by
        intro r hgr hgdr
        have hmult : 2 ≤ g.rootMultiplicity r := by
          have hpos := (rootMultiplicity_pos hfg.2.1.1).mpr hgr
          by_contra hlt
          have hone : g.rootMultiplicity r = 1 := by lia
          exact (eval_derivative_ne_zero_of_rootMultiplicity_eq_one hgr hone)
            (Polynomial.IsRoot.def.mp hgdr)
        have hcount_le := Multiset.nodup_iff_count_le_one.mp hg_nodup r
        rw [count_roots] at hcount_le
        lia
      have hroot_sign : ∀ r, g.IsRoot r →
          (h - f).eval r * g.derivative.eval r ≤ 0 := by
        intro r hgr
        have hleft : 0 ≤ f.eval r * g.derivative.eval r :=
          eval_mul_derivative_nonneg_of_prec_right_root hfg hf_pos hg_pos hgr
        have hright : h.eval r * g.derivative.eval r ≤ 0 :=
          eval_mul_derivative_nonpos_of_prec_left_root hgh hg_pos hh_pos hgr
        rw [eval_sub]
        linarith
      exact
        prec_of_interlaces_eval_mul_nonpos_of_no_common
          hder_inter hgder_pos hsub_pos.ne_zero hsub_splits hsub_pos
          hdeg_lo hdeg_hi hno hroot_sign

end RealRooted
