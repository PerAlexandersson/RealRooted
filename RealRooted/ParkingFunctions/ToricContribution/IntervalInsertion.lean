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

private theorem eval_derivative_ne_zero_of_rootMultiplicity_eq_one
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
    (hdeg : 2 ≤ f.natDegree)
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
    simpa [F] using prec_neg_insertionOperator a b hf hf_pos hdeg hroots hsimple hb
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
  (prec_neg_insertionOperator a b hf hf_pos hdeg hroots hsimple hb).2.1.2

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
  have hprec := prec_neg_insertionOperator a b hf hf_pos hdeg hroots hsimple hb
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

end ToricContribution
end ParkingFunctions
end RealRooted
