import RealRooted.AllCombo
import RealRooted.AffineDerivative
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import RealRooted.ObreschkoffConverse.Converse

/-!
# Obreschkoff forward direction

The proper-position to all-real-rooted pencil half of Obreschkoff's theorem.
-/

open Polynomial

noncomputable section

namespace RealRooted

section

private theorem allComboRealRooted_of_prec_succDegree_pos
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree + 1 = g.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g) :
    AllComboRealRooted f g := by
  let hfg_inter : Interlaces f g := hfg.toInterlaces hdeg
  intro α β
  by_cases hβ0 : β = 0
  · by_cases hα0 : α = 0
    · simp [hα0, hβ0]
    · have hrr : ((C α * f) ≠ 0 ∧ (C α * f).Splits) :=
        isRealRooted_C_mul hfg.1.1 hfg.1.2 hα0
      simp_all
  · rcases lt_or_gt_of_ne hβ0 with hβneg | hβpos
    · by_cases hα_nonpos : α ≤ 0
      · have hrr_neg :
            ((C (-α) * f + C (-β) * g) ≠ 0 ∧ (C (-α) * f + C (-β) * g).Splits) :=
          isRealRooted_nonneg_combo_of_prec
            hfg hf_pos hg_pos
            (by simp_all) (by grind) (Or.inr (by simp_all))
        have hrr :
            ((C (-1 : ℝ) * (C (-α) * f + C (-β) * g)) ≠ 0 ∧
              (C (-1 : ℝ) * (C (-α) * f + C (-β) * g)).Splits) :=
          isRealRooted_C_mul hrr_neg.1 hrr_neg.2 (by simp : (-1 : ℝ) ≠ 0)
        grind
      · have hαpos : 0 < α := lt_of_not_ge hα_nonpos
        have hmix_pos : HasPosLeadingCoeff (C (-β) * g + C (-α) * f) := by
          have hdeg_scaled :
              (C (-α) * f).natDegree < (C (-β) * g).natDegree := by
            rw [natDegree_C_mul (show -α ≠ 0 by grind),
              natDegree_C_mul (show -β ≠ 0 by simp_all)]
            lia
          exact
            hasPosLeadingCoeff_add_of_natDegree_lt_left
              hdeg_scaled
              (hasPosLeadingCoeff_C_mul (by simp_all) hg_pos)
        have hmix_deg :
            (C (-β) * g + C (-α) * f).natDegree = g.natDegree := by
          have hdeg_scaled :
              (C (-α) * f).natDegree < (C (-β) * g).natDegree := by
            rw [natDegree_C_mul (show -α ≠ 0 by grind),
              natDegree_C_mul (show -β ≠ 0 by simp_all)]
            lia
          calc
            (C (-β) * g + C (-α) * f).natDegree = (C (-β) * g).natDegree :=
              natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_scaled
                (hasPosLeadingCoeff_C_mul (by simp_all) hg_pos)
            _ = g.natDegree := by rw [natDegree_C_mul (by simp_all : (-β) ≠ 0)]
        have hrr_neg :
            ((C (-β) * g + C (-α) * f) ≠ 0 ∧ (C (-β) * g + C (-α) * f).Splits) := by
          have hmix_lo : g.natDegree ≤ (C (-β) * g + C (-α) * f).natDegree := by lia
          have hmix_hi : (C (-β) * g + C (-α) * f).natDegree ≤ g.natDegree + 1 := by lia
          have hprec_mix :
              Prec g (C (-β) * g + C (-α) * f) :=
            prec_of_interlaces_evalCoeff_nonpos
              (f := g) (g := f) (a := C (-β)) (b := C (-α))
              hfg_inter hf_pos hmix_pos
              hmix_lo hmix_hi
              (by
                intro r _
                simp
                grind)
          exact hprec_mix.2.1
        have hrr :
            ((C (-1 : ℝ) * (C (-β) * g + C (-α) * f)) ≠ 0 ∧
              (C (-1 : ℝ) * (C (-β) * g + C (-α) * f)).Splits) :=
          isRealRooted_C_mul hrr_neg.1 hrr_neg.2 (by simp : (-1 : ℝ) ≠ 0)
        simp_all
    · by_cases hα_nonneg : 0 ≤ α
      · by_cases hα0 : α = 0
        · have hrr : ((C β * g) ≠ 0 ∧ (C β * g).Splits) :=
            isRealRooted_C_mul hfg.2.1.1 hfg.2.1.2 hβ0
          simp_all
        · exact
            (isRealRooted_nonneg_combo_of_prec
              hfg hf_pos hg_pos hα_nonneg (le_of_lt hβpos)
              (Or.inr hβpos)).2
      · have hαneg : α < 0 := lt_of_not_ge hα_nonneg
        have hmix_pos : HasPosLeadingCoeff (C β * g + C α * f) := by
          have hdeg_scaled :
              (C α * f).natDegree < (C β * g).natDegree := by
            rw [natDegree_C_mul (show α ≠ 0 by grind), natDegree_C_mul hβ0]
            lia
          exact
            hasPosLeadingCoeff_add_of_natDegree_lt_left
              hdeg_scaled
              (hasPosLeadingCoeff_C_mul hβpos hg_pos)
        have hmix_deg :
            (C β * g + C α * f).natDegree = g.natDegree := by
          have hdeg_scaled :
              (C α * f).natDegree < (C β * g).natDegree := by
            rw [natDegree_C_mul (show α ≠ 0 by grind), natDegree_C_mul hβ0]
            lia
          calc
            (C β * g + C α * f).natDegree = (C β * g).natDegree :=
              natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_scaled
                (hasPosLeadingCoeff_C_mul hβpos hg_pos)
            _ = g.natDegree := by rw [natDegree_C_mul hβ0]
        have hmix_lo : g.natDegree ≤ (C β * g + C α * f).natDegree := by lia
        have hmix_hi : (C β * g + C α * f).natDegree ≤ g.natDegree + 1 := by lia
        have hprec_mix :
            Prec g (C β * g + C α * f) :=
          prec_of_interlaces_evalCoeff_nonpos
            (f := g) (g := f) (a := C β) (b := C α)
            hfg_inter hf_pos hmix_pos
            hmix_lo hmix_hi
            (by
              intro r _
              simp
              grind)
        simpa [add_comm, add_left_comm, add_assoc] using hprec_mix.2.1.2

private theorem allComboRealRooted_of_prec_succDegree
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    AllComboRealRooted f g := by
  have hf : (f ≠ 0 ∧ f.Splits) := hfg.1
  have hg : (g ≠ 0 ∧ g.Splits) := hfg.2.1
  have hf_lc_ne : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf.1
  have hg_lc_ne : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg.1
  let sf : ℝ := if 0 < f.leadingCoeff then 1 else -1
  let sg : ℝ := if 0 < g.leadingCoeff then 1 else -1
  have hsf_ne : sf ≠ 0 := by grind
  have hsg_ne : sg ≠ 0 := by grind
  have hsf_sq : sf * sf = 1 := by grind
  have hsg_sq : sg * sg = 1 := by grind
  have hsf_pos : 0 < sf * f.leadingCoeff := by
    dsimp [sf]
    split_ifs with hpos
    · lia
    · grind
  have hsg_pos : 0 < sg * g.leadingCoeff := by
    dsimp [sg]
    split_ifs with hpos
    · lia
    · grind
  let f₀ : ℝ[X] := C sf * f
  let g₀ : ℝ[X] := C sg * g
  have hfg₀ : Prec f₀ g₀ := prec_C_mul_right (prec_C_mul_left hfg hsf_ne) hsg_ne
  have hdeg₀ : f₀.natDegree + 1 = g₀.natDegree := by
    simpa [f₀, g₀, natDegree_C_mul hsf_ne, natDegree_C_mul hsg_ne] using hdeg
  have hf₀_pos : HasPosLeadingCoeff f₀ := by
    unfold HasPosLeadingCoeff f₀
    simp_all
  have hg₀_pos : HasPosLeadingCoeff g₀ := by
    unfold HasPosLeadingCoeff g₀
    simp_all
  have hall₀ : AllComboRealRooted f₀ g₀ :=
    allComboRealRooted_of_prec_succDegree_pos hfg₀ hdeg₀ hf₀_pos hg₀_pos
  intro α β
  have hEq_f : C α * C sf * (C sf * f) = C α * f := by grind
  have hEq_g : C β * C sg * (C sg * g) = C β * g := by grind
  simpa [f₀, g₀, mul_assoc, hEq_f, hEq_g] using hall₀ (α * sf) (β * sg)

/-- To prove the same-degree forward direction of Obreschkoff, it is enough to
handle the no-common-roots case. Shared roots can be factored out recursively,
and `AllComboRealRooted` is rebuilt using
`allComboRealRooted_mul_common_factor`. This mirrors the converse reduction but
keeps the orientation fixed. -/
private theorem allComboRealRooted_of_prec_sameDegree_of_no_common
    (hstep :
      ∀ {f g : ℝ[X]},
        Prec f g →
        f.natDegree = g.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        AllComboRealRooted f g)
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree) :
    AllComboRealRooted f g := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          Prec f g →
          f.natDegree = g.natDegree →
          AllComboRealRooted f g)
      f.natDegree ?_ rfl hfg hdeg
  intro n ih f g hfdeg hfg hdeg
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · simp_all
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hrf
    obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hrg
    have hqf_ne : qf ≠ 0 :=
      right_ne_zero_of_mul (by simpa [hqf] using hfg.1.1)
    have hqg_ne : qg ≠ 0 :=
      right_ne_zero_of_mul (by simpa [hqg] using hfg.2.1.1)
    have hqdeg : qf.natDegree = qg.natDegree := by
      rw [hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
        hqg, natDegree_mul (X_sub_C_ne_zero r) hqg_ne, natDegree_X_sub_C] at hdeg
      lia
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C]
      lia
    have hprec_q : Prec qf qg := by
      apply prec_of_prec_mul_X_sub_C_both r
      lia
    have hqhall : AllComboRealRooted qf qg :=
      ih qf.natDegree hqf_deg_lt rfl hprec_q hqdeg
    have hmul :
        AllComboRealRooted ((X - C r) * qf) ((X - C r) * qg) :=
      allComboRealRooted_mul_common_factor (isRealRooted_X_sub_C r).2 hqhall
    lia

private lemma no_common_with_right_factor_quotient
    {f q : ℝ[X]} {uR : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ ((X - C uR) * q).IsRoot r) :
    ∀ r, f.IsRoot r → ¬ q.IsRoot r := by
  simp_all

private lemma root_lt_rightmost_of_prec_sameDegree_no_common
    {f g : ℝ[X]} {uR : ℝ}
    (hfg : Prec f g)
    (huR_root : g.IsRoot uR)
    (huR_max : ∀ r ∈ g.roots, r ≤ uR)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, f.IsRoot r → r < uR := by
  intro r hr
  have hr_le : r ≤ uR :=
    roots_le_of_prec_right hfg huR_max r ((mem_roots hfg.1.1).mpr hr)
  grind

private lemma prec_of_right_factor_combo_of_natDegree_ge
    {f q : ℝ[X]} {uR α β : ℝ}
    (hqf : Interlaces q f)
    (hq_pos : HasPosLeadingCoeff q)
    (hF_pos : HasPosLeadingCoeff (C α * f + C β * ((X - C uR) * q)))
    (hdeg_lo : f.natDegree ≤ (C α * f + C β * ((X - C uR) * q)).natDegree)
    (hq_no : ∀ r, f.IsRoot r → ¬ q.IsRoot r)
    (hroot_lt : ∀ r, f.IsRoot r → r < uR)
    (hβ : 0 < β) :
    Prec f (C α * f + C β * ((X - C uR) * q)) := by
  have hq_ne : q ≠ 0 := hqf.2.1.1
  have hbeta_term_eq :
      C β * ((X - C uR) * q) = (C β * (X - C uR)) * q := by
    grind
  have hdeg_hi :
      (C α * f + C β * ((X - C uR) * q)).natDegree ≤ f.natDegree + 1 := by
    have hsum_le :
        (C α * f + (C β * (X - C uR)) * q).natDegree ≤
          max (C α * f).natDegree (((C β * (X - C uR)) * q).natDegree) :=
      natDegree_add_le _ _
    have hscaled_le : (C α * f).natDegree ≤ f.natDegree := natDegree_C_mul_le α f
    have hbeta_term_deg : ((C β * (X - C uR)) * q).natDegree = f.natDegree := by
      rw [natDegree_mul
          (show C β * (X - C uR) ≠ 0 by
            exact mul_ne_zero (C_ne_zero.mpr hβ.ne') (X_sub_C_ne_zero uR))
          hq_ne]
      rw [natDegree_mul (C_ne_zero.mpr hβ.ne') (X_sub_C_ne_zero uR),
        natDegree_C, natDegree_X_sub_C]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hqf.2.2.1
    grind
  have hb_neg : ∀ r, f.IsRoot r → (C β * (X - C uR)).eval r < 0 := by
    intro r hr
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    have hru : r - uR < 0 := sub_neg.mpr (hroot_lt r hr)
    nlinarith
  have hF_pos' : HasPosLeadingCoeff (C α * f + (C β * (X - C uR)) * q) := by lia
  have hdeg_lo' : f.natDegree ≤ (C α * f + (C β * (X - C uR)) * q).natDegree := by lia
  have hprec :
      Prec f (C α * f + (C β * (X - C uR)) * q) :=
    prec_of_interlaces_evalCoeff_neg
      (f := f) (g := q) (a := C α) (b := C β * (X - C uR))
      hqf hq_pos hF_pos' hdeg_lo' (by lia) hq_no hb_neg
  lia

/-- A nonzero combination `α f + β (X - uR) q` with `β > 0` is real-rooted in
the same-degree/no-common-roots regime. This is the core right-factor reduction
used in the forward equal-degree Obreschkoff proof: depending on whether the
top coefficient cancels, the combination either becomes the left interlacer of
`f` or stays same-degree and is forced to be real-rooted by strict sign changes
plus one outer root. -/
private theorem isRealRooted_of_right_factor_combo_posβ
    {f q : ℝ[X]} {uR α β : ℝ}
    (hqf : Interlaces q f)
    (hq_pos : HasPosLeadingCoeff q)
    (hq_no : ∀ r, f.IsRoot r → ¬ q.IsRoot r)
    (hroot_lt : ∀ r, f.IsRoot r → r < uR)
    (hβ : 0 < β)
    (hF_ne : C α * f + C β * ((X - C uR) * q) ≠ 0)
    (hdeg_pos : 1 ≤ f.natDegree) :
    ((C α * f + C β * ((X - C uR) * q)) ≠ 0 ∧
      (C α * f + C β * ((X - C uR) * q)).Splits) := by
  let F : ℝ[X] := C α * f + C β * ((X - C uR) * q)
  have hf : (f ≠ 0 ∧ f.Splits) := hqf.1
  have hq : (q ≠ 0 ∧ q.Splits) := hqf.2.1
  have hF_ne' : F ≠ 0 := by lia
  have hdeg_le : F.natDegree ≤ f.natDegree := by
    have hsum_le :
        F.natDegree ≤ max (C α * f).natDegree (C β * ((X - C uR) * q)).natDegree := by
      simpa [F] using natDegree_add_le (C α * f) (C β * ((X - C uR) * q))
    have hleft_le : (C α * f).natDegree ≤ f.natDegree := natDegree_C_mul_le α f
    have hright_eq : (C β * ((X - C uR) * q)).natDegree = f.natDegree := by
      rw [natDegree_C_mul hβ.ne', natDegree_mul (X_sub_C_ne_zero uR) hq.1, natDegree_X_sub_C]
      simpa [Nat.add_comm] using hqf.2.2.1
    simp_all
  have hroot_sign :
      ∀ r, f.IsRoot r → F.eval r * q.eval r < 0 := by
    intro r hr
    have hf_eval : f.eval r = 0 := by simp_all
    have hq_eval_ne : q.eval r ≠ 0 := by simp_all
    have hru : r - uR < 0 := sub_neg.mpr (hroot_lt r hr)
    have hsq : 0 < (q.eval r) ^ 2 := sq_pos_iff.mpr hq_eval_ne
    have hcalc : F.eval r * q.eval r = β * (r - uR) * (q.eval r) ^ 2 := by
      dsimp [F]
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hf_eval,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      ring
    have hprod_neg : β * (r - uR) * (q.eval r) ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hβ hru) hsq
    lia
  have hsign_core :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        f.roots.sort (· ≤ ·) = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    intro pre r₁ r₂ rest hEq
    have hrs_eq : (↑(f.roots.sort (· ≤ ·)) : Multiset ℝ) = f.roots := Multiset.sort_eq ..
    have hr₁_root : f.IsRoot r₁ := by
      apply (mem_roots hf.1).mp
      simpa [hrs_eq] using
        Multiset.mem_coe.mpr (by simp_all : r₁ ∈ f.roots.sort (· ≤ ·))
    have hr₂_root : f.IsRoot r₂ := by
      apply (mem_roots hf.1).mp
      simpa [hrs_eq] using
        Multiset.mem_coe.mpr (by simp_all : r₂ ∈ f.roots.sort (· ≤ ·))
    have hFq₁ : F.eval r₁ * q.eval r₁ < 0 := hroot_sign r₁ hr₁_root
    have hFq₂ : F.eval r₂ * q.eval r₂ < 0 := hroot_sign r₂ hr₂_root
    have hqq : q.eval r₁ * q.eval r₂ < 0 :=
      ObreschkoffConverseInternal.eval_mul_eval_neg_of_interlaces_consecutive_of_no_common
        hqf hq_no pre hEq
    exact mul_neg_of_mul_neg_of_mul_neg hFq₁ hFq₂ hqq
  have hsign :
      let rs := f.roots.sort (· ≤ ·)
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    grind
  by_cases hdeg_lt : F.natDegree < f.natDegree
  · exact (interlaces_of_consecutive_signs_of_natDegree_lt hf.1 hf.2 hF_ne' hdeg_lt hsign).2.1
  · have hdeg_eq : F.natDegree = f.natDegree := by lia
    by_cases hdeg_one : f.natDegree = 1
    · have hF_deg_one : F.natDegree = 1 := by lia
      exact isRealRooted_of_degree_one hF_deg_one
    · have hdeg_two : 2 ≤ f.natDegree := by lia
      exact
        ObreschkoffConverseInternal.isRealRooted_of_interlaces_eval_mul_neg_same_any_lc
          hqf hq_pos hdeg_eq hdeg_two hroot_sign

/-- Positive-leading, no-common-roots equal-degree forward Obreschkoff. This is
the honest same-degree core: same-sign combinations are covered by Wagner
addition, while opposite-sign combinations are routed through the rightmost
root factorization `g = (X - C uR) * qg` and the helper
`isRealRooted_of_right_factor_combo_posβ`. -/
private theorem allComboRealRooted_of_prec_sameDegree_pos_of_no_common
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    AllComboRealRooted f g := by
  have hf : (f ≠ 0 ∧ f.Splits) := hfg.1
  have hg : (g ≠ 0 ∧ g.Splits) := hfg.2.1
  by_cases hdeg0 : f.natDegree = 0
  · intro α β
    by_cases hcomb : C α * f + C β * g = 0
    · simp [hcomb]
    · have hgdeg0 : g.natDegree = 0 := by lia
      have hfC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hdeg0
      have hgC : g = C (g.coeff 0) := eq_C_of_natDegree_eq_zero hgdeg0
      rw [hfC, hgC] at hcomb ⊢
      have hsum_eq :
          C α * C (f.coeff 0) + C β * C (g.coeff 0) =
            C (α * f.coeff 0 + β * g.coeff 0) := by
        simp
      have hroots_eq :
          (C α * C (f.coeff 0) + C β * C (g.coeff 0)).roots =
            (C (α * f.coeff 0 + β * g.coeff 0)).roots := by
        lia
      have hnat_eq :
          (C α * C (f.coeff 0) + C β * C (g.coeff 0)).natDegree =
            (C (α * f.coeff 0 + β * g.coeff 0)).natDegree := by
        lia
      apply splits_of_card_roots
      rw [hroots_eq, hnat_eq, roots_C, natDegree_C]
      simp
  have hdeg_pos : 1 ≤ f.natDegree := by lia
  obtain ⟨uR, huR_root, huR_max⟩ :=
    exists_rightmost_root_of_isRealRooted hg.1 hg.2 (by lia)
  obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr huR_root
  have hqg_inter : Interlaces qg f :=
    interlaces_of_prec_sameDegree_rightmost_factor hfg hdeg huR_max hqg
  have hqg_no : ∀ r, f.IsRoot r → ¬ qg.IsRoot r := by simp_all
  have hroot_lt : ∀ r, f.IsRoot r → r < uR :=
    root_lt_rightmost_of_prec_sameDegree_no_common hfg huR_root huR_max hno
  have hqg_pos : HasPosLeadingCoeff qg := by
    apply hasPosLeadingCoeff_of_X_sub_C_mul (r := uR)
    simp_all
  intro α β
  by_cases hβ0 : β = 0
  · simp_all
  · rcases lt_or_gt_of_ne hβ0 with hβneg | hβpos
    · by_cases hα_nonpos : α ≤ 0
      · have hrr_neg :
          ((C (-α) * f + C (-β) * g) ≠ 0 ∧ (C (-α) * f + C (-β) * g).Splits) :=
        isRealRooted_nonneg_combo_of_prec
          hfg hf_pos hg_pos (by simp_all) (by grind) (Or.inr (by simp_all))
        have hrr :
            ((C (-1 : ℝ) * (C (-α) * f + C (-β) * g)) ≠ 0 ∧
              (C (-1 : ℝ) * (C (-α) * f + C (-β) * g)).Splits) :=
          isRealRooted_C_mul hrr_neg.1 hrr_neg.2 (by simp : (-1 : ℝ) ≠ 0)
        grind
      · have hαpos : 0 < α := lt_of_not_ge hα_nonpos
        have hcomb_neg : C (-α) * f + C (-β) * g ≠ 0 :=
          fun hlin =>
            ObreschkoffConverseInternal.no_nontrivial_linear_relation_of_no_common_root
              hf.1 hf.2 hno (by lia) (neg_ne_zero.mpr hαpos.ne') (neg_ne_zero.mpr hβ0) hlin
        have hrr_neg :
            ((C (-α) * f + C (-β) * g) ≠ 0 ∧ (C (-α) * f + C (-β) * g).Splits) := by
          simpa [hqg] using
            isRealRooted_of_right_factor_combo_posβ
              (f := f) (q := qg) (uR := uR) (α := -α) (β := -β)
              hqg_inter hqg_pos hqg_no hroot_lt (by simp_all) (by lia)
              hdeg_pos
        have hrr :
            ((C (-1 : ℝ) * (C (-α) * f + C (-β) * g)) ≠ 0 ∧
              (C (-1 : ℝ) * (C (-α) * f + C (-β) * g)).Splits) :=
          isRealRooted_C_mul hrr_neg.1 hrr_neg.2 (by simp : (-1 : ℝ) ≠ 0)
        grind
    · by_cases hα_nonneg : 0 ≤ α
      · exact
          (isRealRooted_nonneg_combo_of_prec
            hfg hf_pos hg_pos hα_nonneg (le_of_lt hβpos)
            (Or.inr hβpos)).2
      · have hαneg : α < 0 := lt_of_not_ge hα_nonneg
        have hcomb_pos : C α * f + C β * ((X - C uR) * qg) ≠ 0 := by
          intro hlin_q
          have hlin : C α * f + C β * g = 0 := by simp_all
          exact
            ObreschkoffConverseInternal.no_nontrivial_linear_relation_of_no_common_root
              hf.1 hf.2 hno (by lia) hαneg.ne hβpos.ne' hlin
        simpa [hqg] using
          (isRealRooted_of_right_factor_combo_posβ
            (f := f) (q := qg) (uR := uR) (α := α) (β := β)
            hqg_inter hqg_pos hqg_no hroot_lt hβpos hcomb_pos hdeg_pos).2

/-- Opposite-sign right-factor combinations are real-rooted even when the top
coefficient does not have the sign needed to orient a `Prec` witness directly.
The proof splits into the genuine degree-drop case, where the combination
becomes a left interlacer of `f`, and the same-degree case, where strict sign
changes plus one outer root are enough to force real-rootedness. -/
private theorem allComboRealRooted_of_prec_sameDegree
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree) :
    AllComboRealRooted f g := by
  refine allComboRealRooted_of_prec_sameDegree_of_no_common ?_ hfg hdeg
  intro f g hfg hdeg hno
  have hf : (f ≠ 0 ∧ f.Splits) := hfg.1
  have hg : (g ≠ 0 ∧ g.Splits) := hfg.2.1
  have hf_lc_ne : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf.1
  have hg_lc_ne : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg.1
  let sf : ℝ := if 0 < f.leadingCoeff then 1 else -1
  let sg : ℝ := if 0 < g.leadingCoeff then 1 else -1
  have hsf_ne : sf ≠ 0 := by grind
  have hsg_ne : sg ≠ 0 := by grind
  have hsf_sq : sf * sf = 1 := by grind
  have hsg_sq : sg * sg = 1 := by grind
  have hsf_pos : 0 < sf * f.leadingCoeff := by
    dsimp [sf]
    split_ifs with hpos
    · lia
    · grind
  have hsg_pos : 0 < sg * g.leadingCoeff := by
    dsimp [sg]
    split_ifs with hpos
    · lia
    · grind
  let f₀ : ℝ[X] := C sf * f
  let g₀ : ℝ[X] := C sg * g
  have hfg₀ : Prec f₀ g₀ := prec_C_mul_right (prec_C_mul_left hfg hsf_ne) hsg_ne
  have hdeg₀ : f₀.natDegree = g₀.natDegree := by
    simpa [f₀, g₀, natDegree_C_mul hsf_ne, natDegree_C_mul hsg_ne] using hdeg
  have hf₀_pos : HasPosLeadingCoeff f₀ := by
    unfold HasPosLeadingCoeff f₀
    simp_all
  have hg₀_pos : HasPosLeadingCoeff g₀ := by
    unfold HasPosLeadingCoeff g₀
    simp_all
  have hno₀ : ∀ r, f₀.IsRoot r → ¬ g₀.IsRoot r := by
    intro r hrf₀ hrg₀
    have hrf : f.IsRoot r := by
      have hrf₀_eval : (C sf * f).eval r = 0 := by
        simpa [f₀, Polynomial.IsRoot.def] using hrf₀
      simp_all
    have hrg : g.IsRoot r := by
      have hrg₀_eval : (C sg * g).eval r = 0 := by
        simpa [g₀, Polynomial.IsRoot.def] using hrg₀
      simp_all
    simp_all
  have hall₀ : AllComboRealRooted f₀ g₀ :=
    allComboRealRooted_of_prec_sameDegree_pos_of_no_common hfg₀ hdeg₀ hf₀_pos hg₀_pos hno₀
  intro α β
  have hEq_f : C α * C sf * (C sf * f) = C α * f := by grind
  have hEq_g : C β * C sg * (C sg * g) = C β * g := by grind
  simpa [f₀, g₀, mul_assoc, hEq_f, hEq_g] using hall₀ (α * sf) (β * sg)

/-- Forward direction of Obreschkoff: if `f ≪ g` then all real combinations
`αf + βg` are real-rooted (or zero). Follows from Wagner addition. -/
theorem allComboRealRooted_of_prec {f g : ℝ[X]}
    (hfg : Prec f g) :
    AllComboRealRooted f g := by
  rcases hfg.natDegree_eq_or_eq_succ with hsame | hsucc
  · exact allComboRealRooted_of_prec_sameDegree hfg hsame.symm
  · exact allComboRealRooted_of_prec_succDegree hfg hsucc.symm

end
end RealRooted
