import RealRooted.MaWang
import RealRooted.ParkingFunctions.ToricContribution.Definitions

/-!
# Root insertion on the unit interval

This file proves the abstract Ma--Wang step for the first-order operator
`M_{a,b} f = z(1-z)f' + (a-bz)f`.  If the roots of `f` lie strictly between
zero and one and `0 < a < b`, then the sign-normalized output `-M_{a,b}f`
has positive leading coefficient, one higher degree, and is in proper
position with `f`.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace ParkingFunctions
namespace ToricContribution

@[simp]
theorem insertionOperator_eval_one (a b : ℝ) (f : ℝ[X]) :
    (insertionOperator a b f).eval 1 = (a - b) * f.eval 1 := by
  simp [insertionOperator, intervalWeight]

theorem insertionOperator_eval_isRoot
    (a b : ℝ) {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) :
    (insertionOperator a b f).eval r = r * (1 - r) * f.derivative.eval r := by
  simp only [insertionOperator, intervalWeight, eval_add, eval_mul, eval_sub,
    eval_X, eval_one, eval_C]
  rw [show f.eval r = 0 from hr]
  ring

@[simp]
theorem insertionOperator_neg (a b : ℝ) (f : ℝ[X]) :
    insertionOperator a b (-f) = -insertionOperator a b f := by
  simp only [insertionOperator, derivative_neg]
  ring

/-- The derivative does not vanish at a root of multiplicity one. -/
theorem eval_derivative_ne_zero_of_rootMultiplicity_eq_one
    {p : ℝ[X]} {r : ℝ} (hr : p.IsRoot r) (hmult : p.rootMultiplicity r = 1) :
    p.derivative.eval r ≠ 0 := by
  have hder_ne : p.derivative ≠ 0 := by
    intro hder
    have hp_ne : p ≠ 0 := fun hp => by simp [hp] at hmult
    have hp_C : p = C (p.coeff 0) :=
      eq_C_of_natDegree_eq_zero (derivative_eq_zero.mp hder)
    rw [hp_C, IsRoot.def, eval_C] at hr
    rw [hp_C, hr] at hp_ne
    simp at hp_ne
  have hmult_derivative :
      p.derivative.rootMultiplicity r = p.rootMultiplicity r - 1 :=
    derivative_rootMultiplicity_of_root hr
  simp_all

theorem coeff_neg_insertionOperator_succ_natDegree
    (a b : ℝ) {f : ℝ[X]} (hdeg : 1 ≤ f.natDegree) :
    (-insertionOperator a b f).coeff (f.natDegree + 1) =
      ((f.natDegree : ℝ) + b) * f.leadingCoeff := by
  have hform :
      -insertionOperator a b f =
        X * (X * f.derivative) - X * f.derivative +
          C b * (X * f) - C a * f := by
    simp only [insertionOperator, intervalWeight]
    ring
  rw [hform, coeff_sub, coeff_add, coeff_sub, coeff_X_mul, coeff_X_mul,
    show f.natDegree = (f.natDegree - 1) + 1 by lia, coeff_X_mul,
    coeff_C_mul, coeff_X_mul, coeff_C_mul]
  simp only [coeff_derivative, Nat.sub_add_cancel hdeg]
  rw [coeff_eq_zero_of_natDegree_lt (by lia : f.natDegree < f.natDegree + 1)]
  rw [coeff_natDegree]
  simp only [Nat.cast_sub hdeg, Nat.cast_one]
  ring

theorem natDegree_neg_insertionOperator
    (a b : ℝ) {f : ℝ[X]} (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree)
    (hb : 0 < b) :
    (-insertionOperator a b f).natDegree = f.natDegree + 1 := by
  have hform :
      -insertionOperator a b f =
        X * (X * f.derivative) - X * f.derivative +
          C b * (X * f) - C a * f := by
    simp only [insertionOperator, intervalWeight]
    ring
  have hXX : (X * (X * f.derivative)).natDegree ≤ f.natDegree + 1 := by
    calc
      (X * (X * f.derivative)).natDegree ≤
          X.natDegree + (X * f.derivative).natDegree := natDegree_mul_le
      _ ≤ X.natDegree + (X.natDegree + f.derivative.natDegree) :=
        Nat.add_le_add_left natDegree_mul_le _
      _ ≤ f.natDegree + 1 := by rw [natDegree_X, f.natDegree_derivative]; lia
  have hX : (X * f.derivative).natDegree ≤ f.natDegree + 1 := by
    calc
      (X * f.derivative).natDegree ≤ X.natDegree + f.derivative.natDegree :=
        natDegree_mul_le
      _ ≤ f.natDegree + 1 := by rw [natDegree_X, f.natDegree_derivative]; lia
  have hbX : (C b * (X * f)).natDegree ≤ f.natDegree + 1 := by
    calc
      (C b * (X * f)).natDegree ≤ (X * f).natDegree := by
        simpa using Polynomial.natDegree_C_mul_le b (X * f)
      _ ≤ X.natDegree + f.natDegree := natDegree_mul_le
      _ = f.natDegree + 1 := by simp [natDegree_X, Nat.add_comm]
  have ha : (C a * f).natDegree ≤ f.natDegree + 1 := by
    exact (Polynomial.natDegree_C_mul_le a f).trans (by lia)
  have hsub :
      (X * (X * f.derivative) - X * f.derivative).natDegree ≤
        f.natDegree + 1 := by
    exact (natDegree_sub_le _ _).trans (max_le hXX hX)
  have hadd :
      (X * (X * f.derivative) - X * f.derivative + C b * (X * f)).natDegree ≤
        f.natDegree + 1 := by
    exact (natDegree_add_le _ _).trans (max_le hsub hbX)
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [hform]
    exact (natDegree_sub_le _ _).trans (max_le hadd ha)
  · rw [coeff_neg_insertionOperator_succ_natDegree a b hdeg]
    exact mul_ne_zero (by positivity) (leadingCoeff_ne_zero.mpr hf)

theorem leadingCoeff_neg_insertionOperator
    (a b : ℝ) {f : ℝ[X]} (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree)
    (hb : 0 < b) :
    (-insertionOperator a b f).leadingCoeff =
      ((f.natDegree : ℝ) + b) * f.leadingCoeff := by
  rw [leadingCoeff, natDegree_neg_insertionOperator a b hf hdeg hb,
    coeff_neg_insertionOperator_succ_natDegree a b hdeg]

theorem hasPosLeadingCoeff_neg_insertionOperator
    (a b : ℝ) {f : ℝ[X]} (hf : f ≠ 0) (hdeg : 1 ≤ f.natDegree)
    (hb : 0 < b) (hf_pos : HasPosLeadingCoeff f) :
    HasPosLeadingCoeff (-insertionOperator a b f) := by
  rw [HasPosLeadingCoeff, leadingCoeff_neg_insertionOperator a b hf hdeg hb]
  exact mul_pos (by positivity) hf_pos

/-- The interval-insertion operator adds one real root and puts the input in
proper position with its sign-normalized output. -/
theorem prec_neg_insertionOperator
    (a b : ℝ) {f : ℝ[X]}
    (hf : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hdeg : 1 ≤ f.natDegree)
    (hroots : ∀ r, f.IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1)
    (hsimple : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0)
    (hb : 0 < b) :
    Prec f (-insertionOperator a b f) := by
  let u := -(C a - C b * X)
  let v := -intervalWeight
  have hform : u * f + v * f.derivative = -insertionOperator a b f := by
    simp only [u, v, insertionOperator]
    ring
  rw [← hform]
  apply prec_ma_wang_succ hf hdeg
  · rw [hform]
    exact natDegree_neg_insertionOperator a b hf_pos.ne_zero (by lia) hb
  · rw [hform]
    exact hasPosLeadingCoeff_neg_insertionOperator a b hf_pos.ne_zero (by lia) hb hf_pos
  · exact hf_pos
  · intro r hr
    have hrI := hroots r hr
    have hd := hsimple r hr
    simp only [v, intervalWeight, eval_neg, eval_mul, eval_X, eval_sub, eval_one]
    exact mul_neg_of_neg_of_pos
      (neg_neg_of_pos (mul_pos hrI.1 (sub_pos.mpr hrI.2)))
      (sq_pos_of_ne_zero hd)

theorem insertionOperator_no_common_root
    (a b : ℝ) {f : ℝ[X]}
    (hroots : ∀ r, f.IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1)
    (hsimple : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0) :
    ∀ r, f.IsRoot r → ¬(insertionOperator a b f).IsRoot r := by
  intro r hr hMr
  rw [IsRoot.def, insertionOperator_eval_isRoot a b hr] at hMr
  have hrI := hroots r hr
  have hd := hsimple r hr
  exact (mul_ne_zero (mul_ne_zero (ne_of_gt hrI.1) (sub_ne_zero.mpr (ne_of_gt hrI.2))) hd)
    hMr

/-- Under the endpoint inequalities, the inserted outer roots also remain
strictly inside the unit interval. -/
theorem roots_neg_insertionOperator_mem_Ioo
    (a b : ℝ) {f : ℝ[X]}
    (hf : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hdeg : 2 ≤ f.natDegree)
    (hroots : ∀ r, f.IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1)
    (hsimple : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0)
    (ha : 0 < a) (hba : 0 < b - a) :
    ∀ r ∈ (-insertionOperator a b f).roots, r ∈ Set.Ioo (0 : ℝ) 1 := by
  let F := -insertionOperator a b f
  have hb : 0 < b := by linarith
  have hprec : Prec f F := by
    simpa [F] using prec_neg_insertionOperator a b hf hf_pos (by lia) hroots hsimple hb
  have hFdeg : F.natDegree = f.natDegree + 1 := by
    simpa [F] using natDegree_neg_insertionOperator a b hf_pos.ne_zero (by lia) hb
  have hF_pos : HasPosLeadingCoeff F := by
    simpa [F] using
      hasPosLeadingCoeff_neg_insertionOperator a b hf_pos.ne_zero (by lia) hb hf_pos
  rcases hprec with
    ⟨hfrr, hFrr, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hfrr.2]
  have hrs_len : rs.length = F.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hFrr.2]
  have hint : ListInterlaces ss rs := by
    rcases hshape with ⟨_, hint⟩ | ⟨hlen, _⟩
    · exact hint
    · lia
  have hlen : ss.length + 1 = rs.length := by lia
  have hss_Ioo : ∀ s ∈ ss, s ∈ Set.Ioo (0 : ℝ) 1 := by
    intro s hs
    apply hroots s
    apply (mem_roots hfrr.1).mp
    rw [← hss_eq]
    exact Multiset.mem_coe.mpr hs
  have hf0_not_root : ¬f.IsRoot 0 := by
    intro h0
    have := hroots 0 h0
    simp at this
  have hf1_not_root : ¬f.IsRoot 1 := by
    intro h1
    have := hroots 1 h1
    simp at this
  have hF0_eval : F.eval 0 = -a * f.eval 0 := by
    simp [F, insertionOperator_eval_zero]
  have hF1_eval : F.eval 1 = (b - a) * f.eval 1 := by
    simp [F, insertionOperator_eval_one]
    ring
  have hF0_not_root : ¬F.IsRoot 0 := by
    rw [IsRoot.def, hF0_eval]
    exact mul_ne_zero (neg_ne_zero.mpr ha.ne') (by simpa [IsRoot.def] using hf0_not_root)
  have hF1_not_root : ¬F.IsRoot 1 := by
    rw [IsRoot.def, hF1_eval]
    exact mul_ne_zero hba.ne' (by simpa [IsRoot.def] using hf1_not_root)
  have hsign_zero : ¬(0 < f.eval 0 ↔ 0 < F.eval 0) := by
    intro hsame
    have hf0_ne : f.eval 0 ≠ 0 := by simpa [IsRoot.def] using hf0_not_root
    rcases lt_or_gt_of_ne hf0_ne with hf0_neg | hf0_pos
    · have hF0_pos : 0 < F.eval 0 := by
        rw [hF0_eval]
        exact mul_pos_of_neg_of_neg (neg_neg_of_pos ha) hf0_neg
      exact (not_lt_of_ge hf0_neg.le) (hsame.mpr hF0_pos)
    · have hF0_neg : F.eval 0 < 0 := by rw [hF0_eval]; nlinarith
      exact (not_lt_of_ge hF0_neg.le) (hsame.mp hf0_pos)
  have hsign_one : 0 < f.eval 1 ↔ 0 < F.eval 1 := by
    rw [hF1_eval, mul_pos_iff_of_pos_left hba]
  have hodd_zero :
      Odd ((f.roots.filter ((0 : ℝ) < ·)).card +
        (F.roots.filter ((0 : ℝ) < ·)).card) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact hsign_zero ((hfrr.2.even_card_roots_gt_add_iff_eval_pos_iff
      hFrr.2 hf_pos hF_pos hf0_not_root hF0_not_root).mp heven)
  have heven_one :
      Even ((f.roots.filter ((1 : ℝ) < ·)).card +
        (F.roots.filter ((1 : ℝ) < ·)).card) := by
    exact (hfrr.2.even_card_roots_gt_add_iff_eval_pos_iff
      hFrr.2 hf_pos hF_pos hf1_not_root hF1_not_root).mpr hsign_one
  have hss_above_zero :
      (ss.filter ((0 : ℝ) < ·)).length = ss.length := by
    congr 1
    apply List.filter_eq_self.mpr
    intro s hs
    simpa using (hss_Ioo s hs).1
  have hss_above_one : (ss.filter ((1 : ℝ) < ·)).length = 0 := by
    rw [List.length_eq_zero_iff]
    apply List.filter_eq_nil_iff.mpr
    intro s hs
    simpa using not_lt_of_ge (hss_Ioo s hs).2.le
  have hodd_zero_list :
      Odd ((ss.filter ((0 : ℝ) < ·)).length +
        (rs.filter ((0 : ℝ) < ·)).length) := by
    simpa [← hss_eq, ← hrs_eq] using hodd_zero
  have heven_one_list :
      Even ((ss.filter ((1 : ℝ) < ·)).length +
        (rs.filter ((1 : ℝ) < ·)).length) := by
    simpa [← hss_eq, ← hrs_eq] using heven_one
  have hrs_above_zero :
      (rs.filter ((0 : ℝ) < ·)).length = ss.length + 1 := by
    have hlo := listInterlaces_filter_lt_le (x := (0 : ℝ)) hint hlen
    have hhi := listInterlaces_filter_lt_le_succ (x := (0 : ℝ)) hint hlen
    rw [hss_above_zero] at hlo hhi hodd_zero_list
    grind
  have hrs_above_one : (rs.filter ((1 : ℝ) < ·)).length = 0 := by
    have hhi := listInterlaces_filter_lt_le_succ (x := (1 : ℝ)) hint hlen
    rw [hss_above_one] at hhi heven_one_list
    grind
  have hrs_at_most_zero : (rs.filter (· ≤ (0 : ℝ))).length = 0 := by
    have hpartition := filter_le_add_filter_lt_length (x := (0 : ℝ)) rs
    rw [hrs_above_zero, hlen] at hpartition
    lia
  intro r hr
  have hr_rs : r ∈ rs := by
    apply Multiset.mem_coe.mp
    rw [hrs_eq]
    exact hr
  constructor
  · by_contra hr0
    have hrle : r ≤ 0 := not_lt.mp hr0
    have : r ∈ rs.filter (· ≤ (0 : ℝ)) :=
      List.mem_filter.mpr ⟨hr_rs, by simpa using hrle⟩
    rw [List.length_eq_zero_iff.mp hrs_at_most_zero] at this
    simp at this
  · have hrle : r ≤ 1 := by
      by_contra hr1
      have : r ∈ rs.filter ((1 : ℝ) < ·) :=
        List.mem_filter.mpr ⟨hr_rs, by simpa using lt_of_not_ge hr1⟩
      rw [List.length_eq_zero_iff.mp hrs_above_one] at this
      simp at this
    exact lt_of_le_of_ne hrle (fun hre => hF1_not_root (by
      apply (mem_roots hFrr.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr (hre ▸ hr_rs)))

theorem neg_insertionOperator_splits
    (a b : ℝ) {f : ℝ[X]}
    (hf : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hdeg : 2 ≤ f.natDegree)
    (hroots : ∀ r, f.IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1)
    (hsimple : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0)
    (hb : 0 < b) :
    (-insertionOperator a b f).Splits :=
  (prec_neg_insertionOperator a b hf hf_pos (by lia) hroots hsimple hb).2.1.2

theorem insertionOperator_splits
    (a b : ℝ) {f : ℝ[X]}
    (hf : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hdeg : 2 ≤ f.natDegree)
    (hroots : ∀ r, f.IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1)
    (hsimple : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0)
    (hb : 0 < b) :
    (insertionOperator a b f).Splits := by
  simpa using neg_insertionOperator_splits a b hf hf_pos hdeg hroots hsimple hb

/-- Every inserted root has multiplicity one.  This is the strictness part of
the root-slot theorem: an output root cannot be shared with the input, and
proper position bounds its multiplicity by one. -/
theorem rootMultiplicity_neg_insertionOperator_eq_one
    (a b : ℝ) {f : ℝ[X]}
    (hf : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hdeg : 2 ≤ f.natDegree)
    (hroots : ∀ r, f.IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1)
    (hsimple : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0)
    (hb : 0 < b) {r : ℝ} (hr : (-insertionOperator a b f).IsRoot r) :
    (-insertionOperator a b f).rootMultiplicity r = 1 := by
  have hprec := prec_neg_insertionOperator a b hf hf_pos (by lia) hroots hsimple hb
  have hnot : ¬f.IsRoot r := by
    intro hfr
    exact insertionOperator_no_common_root a b hroots hsimple r hfr (by
      simpa [IsRoot.def] using hr)
  have hfmult : f.rootMultiplicity r = 0 := rootMultiplicity_eq_zero hnot
  have hbound := (rootMultiplicity_bounds_of_prec hprec r).2
  have hpos : 0 < (-insertionOperator a b f).rootMultiplicity r :=
    (rootMultiplicity_pos hprec.2.1.1).mpr hr
  lia

theorem rootMultiplicity_insertionOperator_eq_one
    (a b : ℝ) {f : ℝ[X]}
    (hf : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hdeg : 2 ≤ f.natDegree)
    (hroots : ∀ r, f.IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1)
    (hsimple : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0)
    (hb : 0 < b) {r : ℝ} (hr : (insertionOperator a b f).IsRoot r) :
    (insertionOperator a b f).rootMultiplicity r = 1 := by
  have hneg := rootMultiplicity_neg_insertionOperator_eq_one
    a b hf hf_pos hdeg hroots hsimple hb (by simpa [IsRoot.def] using hr)
  rw [← count_roots] at hneg ⊢
  simpa using hneg

theorem insertionOperator_eval_derivative_ne_zero
    (a b : ℝ) {f : ℝ[X]}
    (hf : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hdeg : 2 ≤ f.natDegree)
    (hroots : ∀ r, f.IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1)
    (hsimple : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0)
    (hb : 0 < b) {r : ℝ} (hr : (insertionOperator a b f).IsRoot r) :
    (insertionOperator a b f).derivative.eval r ≠ 0 :=
  eval_derivative_ne_zero_of_rootMultiplicity_eq_one hr
    (rootMultiplicity_insertionOperator_eq_one
      a b hf hf_pos hdeg hroots hsimple hb hr)

theorem roots_insertionOperator_mem_Ioo
    (a b : ℝ) {f : ℝ[X]}
    (hf : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hdeg : 2 ≤ f.natDegree)
    (hroots : ∀ r, f.IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1)
    (hsimple : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0)
    (ha : 0 < a) (hba : 0 < b - a) :
    ∀ r ∈ (insertionOperator a b f).roots, r ∈ Set.Ioo (0 : ℝ) 1 := by
  simpa using roots_neg_insertionOperator_mem_Ioo
    a b hf hf_pos hdeg hroots hsimple ha hba

/-- Sign-free splitting form of interval insertion.  The leading coefficient
orientation is chosen internally and does not appear in the hypotheses. -/
theorem insertionOperator_splits_of_simple_roots_Ioo
    (a b : ℝ) {f : ℝ[X]}
    (hf : f.Splits) (hdeg : 2 ≤ f.natDegree)
    (hroots : ∀ r, f.IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1)
    (hsimple : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0)
    (hb : 0 < b) :
    (insertionOperator a b f).Splits := by
  have hf_ne : f ≠ 0 := by
    intro hzero
    simp [hzero] at hdeg
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hf_ne) with hlc | hlc
  · have hneg_pos : HasPosLeadingCoeff (-f) := hasPosLeadingCoeff_neg hlc
    have hneg_splits : (-f).Splits := by simpa using hf
    have hneg_roots : ∀ r, (-f).IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1 := by
      intro r hr
      apply hroots r
      simpa [IsRoot.def] using hr
    have hneg_simple : ∀ r, (-f).IsRoot r → (-f).derivative.eval r ≠ 0 := by
      intro r hr
      have hs := hsimple r (by simpa [IsRoot.def] using hr)
      simpa using neg_ne_zero.mpr hs
    simpa using insertionOperator_splits
      a b hneg_splits hneg_pos (by simpa using hdeg) hneg_roots hneg_simple hb
  · exact insertionOperator_splits a b hf hlc hdeg hroots hsimple hb

theorem roots_insertionOperator_mem_Ioo_of_simple_roots_Ioo
    (a b : ℝ) {f : ℝ[X]}
    (hf : f.Splits) (hdeg : 2 ≤ f.natDegree)
    (hroots : ∀ r, f.IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1)
    (hsimple : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0)
    (ha : 0 < a) (hba : 0 < b - a) :
    ∀ r ∈ (insertionOperator a b f).roots, r ∈ Set.Ioo (0 : ℝ) 1 := by
  have hf_ne : f ≠ 0 := by
    intro hzero
    simp [hzero] at hdeg
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hf_ne) with hlc | hlc
  · have hneg_pos : HasPosLeadingCoeff (-f) := hasPosLeadingCoeff_neg hlc
    have hneg_splits : (-f).Splits := by simpa using hf
    have hneg_roots : ∀ r, (-f).IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1 := by
      intro r hr
      apply hroots r
      simpa [IsRoot.def] using hr
    have hneg_simple : ∀ r, (-f).IsRoot r → (-f).derivative.eval r ≠ 0 := by
      intro r hr
      have hs := hsimple r (by simpa [IsRoot.def] using hr)
      simpa using neg_ne_zero.mpr hs
    simpa using roots_insertionOperator_mem_Ioo
      a b hneg_splits hneg_pos (by simpa using hdeg) hneg_roots hneg_simple ha hba
  · exact roots_insertionOperator_mem_Ioo
      a b hf hlc hdeg hroots hsimple ha hba

theorem insertionOperator_eval_derivative_ne_zero_of_simple_roots_Ioo
    (a b : ℝ) {f : ℝ[X]}
    (hf : f.Splits) (hdeg : 2 ≤ f.natDegree)
    (hroots : ∀ r, f.IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1)
    (hsimple : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0)
    (hb : 0 < b) {r : ℝ} (hr : (insertionOperator a b f).IsRoot r) :
    (insertionOperator a b f).derivative.eval r ≠ 0 := by
  have hf_ne : f ≠ 0 := by
    intro hzero
    simp [hzero] at hdeg
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hf_ne) with hlc | hlc
  · have hneg_pos : HasPosLeadingCoeff (-f) := hasPosLeadingCoeff_neg hlc
    have hneg_splits : (-f).Splits := by simpa using hf
    have hneg_roots : ∀ s, (-f).IsRoot s → s ∈ Set.Ioo (0 : ℝ) 1 := by
      intro s hs
      apply hroots s
      simpa [IsRoot.def] using hs
    have hneg_simple : ∀ s, (-f).IsRoot s → (-f).derivative.eval s ≠ 0 := by
      intro s hs
      have hs' := hsimple s (by simpa [IsRoot.def] using hs)
      simpa using neg_ne_zero.mpr hs'
    have hout := insertionOperator_eval_derivative_ne_zero
      a b hneg_splits hneg_pos (by simpa using hdeg) hneg_roots hneg_simple hb
      (r := r) (by simpa [IsRoot.def] using hr)
    simpa using neg_ne_zero.mpr hout
  · exact insertionOperator_eval_derivative_ne_zero
      a b hf hlc hdeg hroots hsimple hb hr

theorem insertionOperator_eq_C_mul_X_sub_C_of_natDegree_zero
    (a b : ℝ) {f : ℝ[X]} (hdeg : f.natDegree = 0) (hf0 : f.eval 0 ≠ 0)
    (hb : b ≠ 0) :
    insertionOperator a b f =
      C (-b * f.eval 0) * (X - C (a / b)) := by
  have hfC : f = C (f.eval 0) := by
    calc
      f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
      _ = C (f.eval 0) := by rw [coeff_zero_eq_eval_zero]
  conv_lhs => rw [hfC]
  apply Polynomial.funext
  intro x
  simp [insertionOperator, intervalWeight]
  field_simp
  ring

theorem natDegree_insertionOperator_of_natDegree_zero
    (a b : ℝ) {f : ℝ[X]} (hdeg : f.natDegree = 0) (hf0 : f.eval 0 ≠ 0)
    (hb : b ≠ 0) :
    (insertionOperator a b f).natDegree = 1 := by
  rw [insertionOperator_eq_C_mul_X_sub_C_of_natDegree_zero a b hdeg hf0 hb,
    natDegree_mul (C_ne_zero.mpr (mul_ne_zero (neg_ne_zero.mpr hb) hf0))
      (X_sub_C_ne_zero (a / b)), natDegree_C, natDegree_X_sub_C]

theorem insertionOperator_splits_of_natDegree_zero
    (a b : ℝ) {f : ℝ[X]} (hdeg : f.natDegree = 0) (hf0 : f.eval 0 ≠ 0)
    (hb : b ≠ 0) :
    (insertionOperator a b f).Splits := by
  rw [insertionOperator_eq_C_mul_X_sub_C_of_natDegree_zero a b hdeg hf0 hb]
  exact (isRealRooted_X_sub_C (a / b)).2.C_mul (-b * f.eval 0)

theorem roots_insertionOperator_mem_Ioo_of_natDegree_zero
    (a b : ℝ) {f : ℝ[X]} (hdeg : f.natDegree = 0) (hf0 : f.eval 0 ≠ 0)
    (ha : 0 < a) (hba : 0 < b - a) :
    ∀ r ∈ (insertionOperator a b f).roots, r ∈ Set.Ioo (0 : ℝ) 1 := by
  have hb : 0 < b := by linarith
  have hM_ne : insertionOperator a b f ≠ 0 := by
    rw [insertionOperator_eq_C_mul_X_sub_C_of_natDegree_zero a b hdeg hf0 hb.ne']
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (neg_ne_zero.mpr hb.ne') hf0))
      (X_sub_C_ne_zero (a / b))
  intro r hr
  have hr_root := (mem_roots hM_ne).mp hr
  rw [insertionOperator_eq_C_mul_X_sub_C_of_natDegree_zero a b hdeg hf0 hb.ne',
    IsRoot.def] at hr_root
  have hr_eq : r = a / b := by
    have : r - a / b = 0 := by simpa [hb.ne', hf0] using hr_root
    linarith
  rw [hr_eq]
  constructor
  · exact div_pos ha hb
  · rw [div_lt_one hb]
    linarith

theorem insertionOperator_eval_derivative_ne_zero_of_natDegree_zero
    (a b : ℝ) {f : ℝ[X]} (hdeg : f.natDegree = 0) (hf0 : f.eval 0 ≠ 0)
    (hb : b ≠ 0) (r : ℝ) :
    (insertionOperator a b f).derivative.eval r ≠ 0 := by
  rw [insertionOperator_eq_C_mul_X_sub_C_of_natDegree_zero a b hdeg hf0 hb]
  simp [hb, hf0]

@[simp]
theorem insertionOperator_C_mul (a b k : ℝ) (f : ℝ[X]) :
    insertionOperator a b (C k * f) = C k * insertionOperator a b f := by
  simp only [insertionOperator, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

/-- The complete interval-insertion conclusion for the monic linear input.
This is the low-degree bridge needed after inserting into a constant. -/
theorem insertionOperator_X_sub_C_data
    (a b u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (ha : 0 < a) (hba : 0 < b - a) :
    (insertionOperator a b (X - C u)).natDegree = 2 ∧
      (insertionOperator a b (X - C u)).Splits ∧
      (∀ r ∈ (insertionOperator a b (X - C u)).roots,
        r ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ r, (insertionOperator a b (X - C u)).IsRoot r →
        (insertionOperator a b (X - C u)).derivative.eval r ≠ 0) := by
  let f : ℝ[X] := X - C u
  let F : ℝ[X] := -insertionOperator a b f
  have hb : 0 < b := by linarith
  have hfdeg : f.natDegree = 1 := by simp [f]
  have hFdeg : F.natDegree = 2 := by
    simpa [F, hfdeg] using
      natDegree_neg_insertionOperator a b (X_sub_C_ne_zero u) (by simp) hb
  have hF_ne : F ≠ 0 := by
    intro hzero
    simp [hzero] at hFdeg
  have hF0 : F.eval 0 = a * u := by
    simp [F, f, insertionOperator, intervalWeight]
  have hFu : F.eval u = -u * (1 - u) := by
    simp [F, f, insertionOperator, intervalWeight]
  have hF1 : F.eval 1 = (b - a) * (1 - u) := by
    simp [F, f, insertionOperator, intervalWeight]
    ring
  have hsign_left : F.eval 0 * F.eval u < 0 := by
    rw [hF0, hFu]
    have h0 : 0 < a * u := mul_pos ha hu.1
    have h1 : 0 < u * (1 - u) := mul_pos hu.1 (sub_pos.mpr hu.2)
    nlinarith
  have hsign_right : F.eval u * F.eval 1 < 0 := by
    rw [hFu, hF1]
    have h0 : 0 < u * (1 - u) := mul_pos hu.1 (sub_pos.mpr hu.2)
    have h1 : 0 < (b - a) * (1 - u) := mul_pos hba (sub_pos.mpr hu.2)
    nlinarith
  obtain ⟨sL, hsL0, hsLu, hsLroot⟩ :=
    exists_isRoot_between_of_eval_mul_neg hu.1 hsign_left
  obtain ⟨sR, hsuR, hsR1, hsRroot⟩ :=
    exists_isRoot_between_of_eval_mul_neg hu.2 hsign_right
  have hsLR : sL < sR := lt_trans hsLu hsuR
  have hsub : (↑[sL, sR] : Multiset ℝ) ≤ F.roots := by
    rw [Multiset.le_iff_subset (by simp [ne_of_lt hsLR])]
    intro r hr
    have : r = sL ∨ r = sR := by simpa using Multiset.mem_coe.mp hr
    rcases this with rfl | rfl
    · exact (mem_roots hF_ne).mpr hsLroot
    · exact (mem_roots hF_ne).mpr hsRroot
  have hcard : F.roots.card = 2 := by
    apply le_antisymm
    · simpa [hFdeg] using card_roots' F
    · simpa using Multiset.card_le_card hsub
  have hF_splits : F.Splits := by
    apply splits_of_card_roots
    simpa [hFdeg] using hcard
  have heq : (↑[sL, sR] : Multiset ℝ) = F.roots :=
    Multiset.eq_of_le_of_card_le hsub (by simp [hcard])
  have hMdeg : (insertionOperator a b f).natDegree = 2 := by
    simpa [F] using hFdeg
  have hMsplits : (insertionOperator a b f).Splits := by
    simpa [F] using hF_splits
  have hMroots :
      ∀ r ∈ (insertionOperator a b f).roots, r ∈ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    have hrF : r ∈ F.roots := by simpa [F] using hr
    rw [← heq] at hrF
    have hr_eq : r = sL ∨ r = sR := by simpa using hrF
    rcases hr_eq with rfl | rfl
    · exact ⟨hsL0, lt_trans hsLu hu.2⟩
    · exact ⟨lt_trans hu.1 hsuR, hsR1⟩
  have hMsimple :
      ∀ r, (insertionOperator a b f).IsRoot r →
        (insertionOperator a b f).derivative.eval r ≠ 0 := by
    intro r hr
    have hrF : F.IsRoot r := by simpa [F, IsRoot.def] using hr
    have hmultF : F.rootMultiplicity r = 1 := by
      rw [← count_roots, ← heq]
      have hrmem : r = sL ∨ r = sR := by
        have : r ∈ F.roots := (mem_roots hF_ne).mpr hrF
        rw [← heq] at this
        simpa using this
      rcases hrmem with rfl | rfl <;> simp [ne_of_lt hsLR]
    have hderF := eval_derivative_ne_zero_of_rootMultiplicity_eq_one hrF hmultF
    simpa [F] using neg_ne_zero.mpr hderF
  dsimp [f] at hMdeg hMsplits hMroots hMsimple
  exact ⟨hMdeg, hMsplits, hMroots, hMsimple⟩

theorem insertionOperator_C_mul_X_sub_C_data
    (a b k u : ℝ) (hk : k ≠ 0) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (ha : 0 < a) (hba : 0 < b - a) :
    (insertionOperator a b (C k * (X - C u))).natDegree = 2 ∧
      (insertionOperator a b (C k * (X - C u))).Splits ∧
      (∀ r ∈ (insertionOperator a b (C k * (X - C u))).roots,
        r ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ r, (insertionOperator a b (C k * (X - C u))).IsRoot r →
        (insertionOperator a b (C k * (X - C u))).derivative.eval r ≠ 0) := by
  obtain ⟨hdeg, hsplits, hroots, hsimple⟩ :=
    insertionOperator_X_sub_C_data a b u hu ha hba
  let p := insertionOperator a b (X - C u)
  have hp_ne : p ≠ 0 := by
    intro hzero
    simp [p, hzero] at hdeg
  have hscaled_ne : C k * p ≠ 0 := mul_ne_zero (C_ne_zero.mpr hk) hp_ne
  have hscaled_deg : (C k * p).natDegree = 2 := by
    rw [natDegree_C_mul hk]
    exact hdeg
  have hscaled_splits : (C k * p).Splits := hsplits.C_mul k
  have hscaled_roots : ∀ r ∈ (C k * p).roots, r ∈ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    have hr_scaled := (mem_roots hscaled_ne).mp hr
    have hrp : p.IsRoot r := by
      rw [IsRoot.def] at hr_scaled ⊢
      simpa [hk] using hr_scaled
    apply hroots r
    exact (mem_roots hp_ne).mpr hrp
  have hscaled_simple :
      ∀ r, (C k * p).IsRoot r → (C k * p).derivative.eval r ≠ 0 := by
    intro r hr
    have hrp : p.IsRoot r := by
      rw [IsRoot.def] at hr ⊢
      simpa [hk] using hr
    have hpder := hsimple r hrp
    simpa [hk, p] using mul_ne_zero hk hpder
  rw [insertionOperator_C_mul]
  change (C k * p).natDegree = 2 ∧ (C k * p).Splits ∧
    (∀ r ∈ (C k * p).roots, r ∈ Set.Ioo (0 : ℝ) 1) ∧
    (∀ r, (C k * p).IsRoot r → (C k * p).derivative.eval r ≠ 0)
  exact ⟨hscaled_deg, hscaled_splits, hscaled_roots, hscaled_simple⟩

theorem insertionOperator_natDegree_one_data
    (a b : ℝ) {f : ℝ[X]} (hf : f.Splits) (hdeg : f.natDegree = 1)
    (hroots : ∀ r, f.IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1)
    (ha : 0 < a) (hba : 0 < b - a) :
    (insertionOperator a b f).natDegree = 2 ∧
      (insertionOperator a b f).Splits ∧
      (∀ r ∈ (insertionOperator a b f).roots, r ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ r, (insertionOperator a b f).IsRoot r →
        (insertionOperator a b f).derivative.eval r ≠ 0) := by
  have hf_ne : f ≠ 0 := by
    intro hzero
    simp [hzero] at hdeg
  have hcard : f.roots.card = 1 := by
    rw [card_roots_of_splits hf, hdeg]
  obtain ⟨u, hu_roots⟩ := Multiset.card_eq_one.mp hcard
  have hu_root : f.IsRoot u := by
    apply (mem_roots hf_ne).mp
    rw [hu_roots]
    simp
  have hu := hroots u hu_root
  have hfactor : f = C f.leadingCoeff * (X - C u) := by
    have hprod :=
      (C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_of_splits hf)).symm
    rw [hu_roots] at hprod
    simpa using hprod
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf_ne
  rw [hfactor]
  exact insertionOperator_C_mul_X_sub_C_data a b f.leadingCoeff u hlc hu ha hba

/-- Uniform interval-insertion data in every input degree.  The endpoint value
hypothesis excludes the zero polynomial in the constant case. -/
theorem insertionOperator_data_of_simple_roots_Ioo
    (a b : ℝ) {f : ℝ[X]} (hf : f.Splits) (hf0 : f.eval 0 ≠ 0)
    (hroots : ∀ r, f.IsRoot r → r ∈ Set.Ioo (0 : ℝ) 1)
    (hsimple : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0)
    (ha : 0 < a) (hba : 0 < b - a) :
    (insertionOperator a b f).natDegree = f.natDegree + 1 ∧
      (insertionOperator a b f).Splits ∧
      (∀ r ∈ (insertionOperator a b f).roots,
        r ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ r, (insertionOperator a b f).IsRoot r →
        (insertionOperator a b f).derivative.eval r ≠ 0) := by
  rcases eq_or_lt_of_le (Nat.zero_le f.natDegree) with hdeg | hdeg
  · have hdegree := natDegree_insertionOperator_of_natDegree_zero
      a b hdeg.symm hf0 (by linarith : b ≠ 0)
    refine ⟨by rw [← hdeg]; exact hdegree,
      insertionOperator_splits_of_natDegree_zero a b hdeg.symm hf0 (by linarith),
      roots_insertionOperator_mem_Ioo_of_natDegree_zero a b hdeg.symm hf0 ha hba,
      fun r _ => insertionOperator_eval_derivative_ne_zero_of_natDegree_zero
        a b hdeg.symm hf0 (by linarith) r⟩
  · have hone : 1 ≤ f.natDegree := by lia
    rcases eq_or_lt_of_le hone with hdegree | hdegree
    · have hdata := insertionOperator_natDegree_one_data
        a b hf hdegree.symm hroots ha hba
      rw [← hdegree]
      simpa using hdata
    · have htwo : 2 ≤ f.natDegree := by lia
      have hb : 0 < b := by linarith
      refine ⟨?_, insertionOperator_splits_of_simple_roots_Ioo
          a b hf htwo hroots hsimple hb,
        roots_insertionOperator_mem_Ioo_of_simple_roots_Ioo
          a b hf htwo hroots hsimple ha hba,
        fun r hr => insertionOperator_eval_derivative_ne_zero_of_simple_roots_Ioo
          a b hf htwo hroots hsimple hb hr⟩
      rw [← natDegree_neg]
      exact natDegree_neg_insertionOperator a b (by
        intro hzero
        simp [hzero] at htwo) (by lia) hb

end ToricContribution
end ParkingFunctions
end RealRooted
