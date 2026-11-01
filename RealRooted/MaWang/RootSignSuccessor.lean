module

public import RealRooted.MaWang.CriticalSign
import RealRooted.MaWang.Weak.DerivativeSign
import RealRooted.Interlacing.NegativeRoots
import RealRooted.Interlacing.Residue
import RealRooted.Derivative.Algebra
import RealRooted.Hadamard.SchurSzegoSigns
import RealRooted.MaWang.StrictSigns.Assembly
import RealRooted.MaWang.StrictSigns.RootSigns
import RealRooted.Mathlib.Algebra.Polynomial.Derivative

/-!
# Root-sign successor criteria

This file infers the degree and leading sign of an endpoint polynomial from
its critical signs, its value at zero, and its prospective top coefficient.
-/

public section

open Polynomial Filter

noncomputable section

namespace RealRooted

private lemma eval_derivative_ne_zero_of_nodup
    {p : ℝ[X]} (hp : p ≠ 0) (hnodup : p.roots.Nodup)
    {r : ℝ} (hr : p.IsRoot r) :
    p.derivative.eval r ≠ 0 := by
  intro hder
  have hle : p.rootMultiplicity r ≤ 1 := by
    rw [← count_roots]
    exact Multiset.nodup_iff_count_le_one.mp hnodup r
  have hlt : 1 < p.rootMultiplicity r :=
    (one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨hr, hder⟩
  lia

private lemma hasNonnegCoeffs_of_splits_of_pos_of_roots_neg
    {p : ℝ[X]} (hp : p.Splits) (hp_pos : HasPosLeadingCoeff p)
    (hroots : ∀ r ∈ p.roots, r < 0) :
    HasNonnegCoeffs p := by
  intro k
  by_cases hk : k ≤ p.natDegree
  · have h := leadingCoeff_mul_coeff_pos_of_roots_neg hp hp_pos.ne_zero hroots hk
    rcases mul_pos_iff.mp h with ⟨_, hk_pos⟩ | ⟨hp_neg, _⟩
    · exact hk_pos.le
    · exact (not_lt_of_ge hp_pos.le hp_neg).elim
  · rw [coeff_eq_zero_of_natDegree_lt (by lia)]

private lemma roots_eq_of_strict_root_list
    {p : ℝ[X]} {rs : List ℝ} (hp : p ≠ 0)
    (hlen : rs.length = p.natDegree) (hsorted : rs.Pairwise (fun x y ↦ x < y))
    (hroot : ∀ r ∈ rs, p.IsRoot r) :
    p.Splits ∧ p.roots.Nodup ∧ (↑rs : Multiset ℝ) = p.roots := by
  have hsub : (↑rs : Multiset ℝ) ≤ p.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hsorted.imp ne_of_lt))]
    intro r hr
    exact (mem_roots hp).mpr (hroot r (Multiset.mem_coe.mp hr))
  have heq : (↑rs : Multiset ℝ) = p.roots := by
    apply Multiset.eq_of_le_of_card_le hsub
    simpa [Multiset.coe_card, hlen] using card_roots' p
  refine ⟨Polynomial.splits_iff_card_roots.mpr ?_, ?_, heq⟩
  · rw [← heq, Multiset.coe_card, hlen]
  · rw [← heq]
    exact Multiset.coe_nodup.mpr (hsorted.imp ne_of_lt)

private lemma exists_negative_root_list_of_endpoint_sign
    {f F : ℝ[X]} {m : ℕ}
    (hf_splits : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hf_degree : f.natDegree = m) (hf_nodup : f.roots.Nodup)
    (hf_neg : ∀ r ∈ f.roots, r < 0) (hF_zero : 0 < F.eval 0)
    (hsign : ∀ r, f.IsRoot r → F.eval r * f.derivative.eval r < 0) :
    ∃ rs : List ℝ, rs.length = m ∧ rs.Pairwise (fun x y ↦ x < y) ∧
      (∀ r ∈ rs, F.IsRoot r) ∧ ∀ r ∈ rs, r < 0 := by
  by_cases hm : m = 0
  · exact ⟨[], by simp [hm]⟩
  have hm_pos : 1 ≤ m := by lia
  have hder : Interlaces f.derivative f :=
    interlaces_derivative_of_pos_natDegree hf_pos.ne_zero hf_splits hf_pos (by lia)
  obtain ⟨_, hder_rr, _, roots, droots, hroots_sorted, _, hroots_eq,
    hdroots_eq, hinter⟩ := hder
  have hroots_len : roots.length = m := by
    rw [← Multiset.coe_card, hroots_eq, Polynomial.splits_iff_card_roots.mp hf_splits,
      hf_degree]
  have hroots_ne : roots ≠ [] := by grind
  have hconsecutive :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        roots = pre ++ r₁ :: r₂ :: rest → F.eval r₁ * F.eval r₂ < 0 := by
    intro pre r₁ r₂ rest heq
    have hr₁ : f.IsRoot r₁ := MaWang.isRoot_of_mem_sorted_roots_eq hroots_eq heq
    have heq₂ : roots = (pre ++ [r₁]) ++ r₂ :: rest := by simp_all
    have hr₂ : f.IsRoot r₂ := MaWang.isRoot_of_mem_sorted_roots_eq hroots_eq heq₂
    have hder_nonpos : f.derivative.eval r₁ * f.derivative.eval r₂ ≤ 0 :=
      MaWang.eval_mul_eval_nonpos_of_interlacing_consecutive
        hder_rr.2 hroots_sorted hdroots_eq hinter heq
    have h₁ := hsign r₁ hr₁
    have h₂ := hsign r₂ hr₂
    have hd₁ : f.derivative.eval r₁ ≠ 0 := by intro h; simp [h] at h₁
    have hd₂ : f.derivative.eval r₂ ≠ 0 := by intro h; simp [h] at h₂
    exact MaWang.mul_neg_of_mul_neg_of_mul_neg h₁ h₂
      (lt_of_le_of_ne hder_nonpos (mul_ne_zero hd₁ hd₂))
  obtain ⟨inner, hinner_len, hinner_inter, hinner_root, hinner_sorted⟩ :=
    MaWang.exists_roots_strictly_interlacing_of_consecutive_signs
      hroots_sorted hconsecutive
  let rmax := roots.getLast hroots_ne
  have hrmax_mem : rmax ∈ roots := List.getLast_mem hroots_ne
  have hrmax_root : f.IsRoot rmax := by
    apply (mem_roots hf_pos.ne_zero).mp
    simpa [hroots_eq] using Multiset.mem_coe.mpr hrmax_mem
  have hrmax_right : ∀ r, f.IsRoot r → r ≤ rmax := by
    intro r hr
    have hr_mem : r ∈ roots := Multiset.mem_coe.mp <| by
      simpa [hroots_eq] using (mem_roots hf_pos.ne_zero).mpr hr
    exact hroots_sorted.rel_getLast hr_mem
  have hrmax_count : f.roots.count rmax = 1 := by
    have hpos : 0 < f.roots.count rmax := Multiset.count_pos.mpr <| by
      simpa [hroots_eq] using Multiset.mem_coe.mpr hrmax_mem
    have hle : f.roots.count rmax ≤ 1 := Multiset.nodup_iff_count_le_one.mp hf_nodup rmax
    lia
  have hcountP : f.roots.countP (rmax < ·) = 0 := by
    rw [Multiset.countP_eq_zero]
    intro r hr
    exact not_lt_of_ge (hrmax_right r ((mem_roots hf_pos.ne_zero).mp hr))
  have hder_pos : 0 < f.derivative.eval rmax := by
    have h := deriv_at_root_sign hf_splits hf_pos rmax
      ((mem_roots hf_pos.ne_zero).mpr hrmax_root) hrmax_count
    simpa [hcountP] using h
  have hF_rmax : F.eval rmax < 0 := by nlinarith [hsign rmax hrmax_root]
  have hrmax_neg : rmax < 0 := hf_neg rmax ((mem_roots hf_pos.ne_zero).mpr hrmax_root)
  obtain ⟨u, hrmax_u, hu_zero, hu_root⟩ :=
    MaWang.exists_isRoot_between_of_eval_mul_neg hrmax_neg (by nlinarith)
  have hinner_lt_u : ∀ r ∈ inner, r < u := by
    intro r hr
    exact lt_of_le_of_lt
      (listInterlaces_all_le_getLast hroots_ne hroots_sorted hinner_inter r hr)
      hrmax_u
  refine ⟨inner ++ [u], ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]
    lia
  · rw [List.pairwise_append]
    refine ⟨hinner_sorted, by simp, ?_⟩
    intro r hr s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact hinner_lt_u r hr
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hinner_root r hr
    · simp only [List.mem_singleton] at hr
      subst r
      exact hu_root
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · have hr_le :=
        listInterlaces_all_le_getLast hroots_ne hroots_sorted hinner_inter r hr
      exact lt_of_le_of_lt hr_le hrmax_neg
    · simp only [List.mem_singleton] at hr
      subst r
      exact hu_zero

private lemma positive_coeffs_of_splits_of_pos_of_roots_neg
    {p : ℝ[X]} (hp : p.Splits) (hp_pos : HasPosLeadingCoeff p)
    (hroots : ∀ r ∈ p.roots, r < 0) :
    ∀ k ≤ p.natDegree, 0 < p.coeff k := by
  intro k hk
  have h := leadingCoeff_mul_coeff_pos_of_roots_neg hp hp_pos.ne_zero hroots hk
  rcases mul_pos_iff.mp h with ⟨_, hk_pos⟩ | ⟨hp_neg, _⟩
  · exact hk_pos
  · exact (not_lt_of_ge hp_pos.le hp_neg).elim

/-- A positive prospective coefficient forces the successor-degree branch of
the root-sign endpoint criterion. -/
theorem rootSignSuccessor_of_coeff_pos
    {f F : ℝ[X]} {m : ℕ}
    (hf_splits : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hf_degree : f.natDegree = m) (hf_nodup : f.roots.Nodup)
    (hf_neg : ∀ r ∈ f.roots, r < 0) (hF_degree : F.natDegree ≤ m + 1)
    (hF_zero : 0 < F.eval 0)
    (hsign : ∀ r, f.IsRoot r → F.eval r * f.derivative.eval r < 0)
    (htop : 0 < F.coeff (m + 1)) :
    F.natDegree = m + 1 ∧ HasPosLeadingCoeff F ∧ StrictInterl f F ∧
      F.Splits ∧ HasSimpleRoots F ∧ (∀ r ∈ F.roots, r < 0) ∧
      ∀ k ≤ F.natDegree, 0 < F.coeff k := by
  have hF_deg : F.natDegree = m + 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero hF_degree htop.ne'
  have hF_pos : HasPosLeadingCoeff F := by
    simpa [HasPosLeadingCoeff, leadingCoeff, hF_deg] using htop
  have hstrict : StrictInterl f F :=
    strictInterl_of_eval_mul_derivative_nonpos hf_pos hf_splits hf_nodup hF_pos
      (by lia) (by lia) fun r hr ↦ (hsign r hr).le
  have hinter : Interlaces f F := hstrict.toInterlaces (by lia)
  have hF_splits : F.Splits := hstrict.2.1.2
  have hno : ∀ r : ℝ, ¬ (f.IsRoot r ∧ F.IsRoot r) := by
    intro r hr
    have := hsign r hr.1
    simp [hr.2.eq_zero] at this
  have hF_simple : HasSimpleRoots F := (hstrict.hasSimpleRoots_of_no_common_root hno).2
  have hF_neg_root : ∀ r, F.IsRoot r → r < 0 :=
    roots_neg_of_interlaces_of_eval_zero_pos hinter hF_pos hF_zero fun r hr ↦
      hf_neg r ((mem_roots hf_pos.ne_zero).mpr hr)
  have hF_neg : ∀ r ∈ F.roots, r < 0 := fun r hr ↦
    hF_neg_root r ((mem_roots hF_pos.ne_zero).mp hr)
  exact ⟨hF_deg, hF_pos, hstrict, hF_splits, hF_simple, hF_neg,
    positive_coeffs_of_splits_of_pos_of_roots_neg hF_splits hF_pos hF_neg⟩

/-- A vanishing prospective coefficient forces the equal-degree branch of
the root-sign endpoint criterion. -/
theorem rootSignSameDegree_of_coeff_eq_zero
    {f F : ℝ[X]} {m : ℕ}
    (hf_splits : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hf_degree : f.natDegree = m) (hf_nodup : f.roots.Nodup)
    (hf_neg : ∀ r ∈ f.roots, r < 0) (hF_degree : F.natDegree ≤ m + 1)
    (hF_zero : 0 < F.eval 0)
    (hsign : ∀ r, f.IsRoot r → F.eval r * f.derivative.eval r < 0)
    (htop : F.coeff (m + 1) = 0) :
    F.natDegree = m ∧ HasPosLeadingCoeff F ∧ StrictInterl f F ∧
      F.Splits ∧ HasSimpleRoots F ∧ (∀ r ∈ F.roots, r < 0) ∧
      ∀ k ≤ F.natDegree, 0 < F.coeff k := by
  have hF_ne : F ≠ 0 := by
    intro hzero
    subst F
    simp at hF_zero
  have hF_le : F.natDegree ≤ m := by
    by_contra hle
    have heq : F.natDegree = m + 1 := by lia
    have : F.coeff (m + 1) ≠ 0 := by
      rw [← heq]
      exact leadingCoeff_ne_zero.mpr hF_ne
    exact this htop
  obtain ⟨rs, hrs_len, hrs_sorted, hrs_root, hrs_neg⟩ :=
    exists_negative_root_list_of_endpoint_sign hf_splits hf_pos hf_degree hf_nodup
      hf_neg hF_zero hsign
  have hrs_sub : (↑rs : Multiset ℝ) ≤ F.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hrs_sorted.imp ne_of_lt))]
    intro r hr
    exact (mem_roots hF_ne).mpr (hrs_root r (Multiset.mem_coe.mp hr))
  have hm_le : m ≤ F.natDegree := by
    have hcard := Multiset.card_le_card hrs_sub
    have hroot_card := card_roots' F
    simpa [Multiset.coe_card, hrs_len] using hcard.trans hroot_card
  have hF_deg : F.natDegree = m := by lia
  obtain ⟨hF_splits, hF_nodup, hrs_eq⟩ :=
    roots_eq_of_strict_root_list hF_ne (hrs_len.trans hF_deg.symm) hrs_sorted hrs_root
  have hF_neg : ∀ r ∈ F.roots, r < 0 := by
    intro r hr
    apply hrs_neg r
    exact Multiset.mem_coe.mp (hrs_eq.symm ▸ hr)
  have hprod := leadingCoeff_mul_coeff_pos_of_roots_neg
    hF_splits hF_ne hF_neg (k := 0) (Nat.zero_le _)
  have hcoeff_zero : F.coeff 0 = F.eval 0 := Polynomial.coeff_zero_eq_eval_zero F
  have hF_pos : HasPosLeadingCoeff F := by
    rw [hcoeff_zero] at hprod
    rcases mul_pos_iff.mp hprod with ⟨hpos, _⟩ | ⟨_, hneg⟩
    · exact hpos
    · exact (not_lt_of_ge hF_zero.le hneg).elim
  have hstrict : StrictInterl f F :=
    strictInterl_of_eval_mul_derivative_nonpos hf_pos hf_splits hf_nodup hF_pos
      (by lia) (by lia) fun r hr ↦ (hsign r hr).le
  exact ⟨hF_deg, hF_pos, hstrict, hF_splits,
    HasSimpleRoots.of_roots_nodup hF_ne hF_nodup, hF_neg,
    positive_coeffs_of_splits_of_pos_of_roots_neg hF_splits hF_pos hF_neg⟩

/-- A negative prospective coefficient forces one positive root in addition
to the `m` simple negative roots selected by the critical signs. -/
theorem rootSignSuccessor_of_coeff_neg
    {f F : ℝ[X]} {m : ℕ}
    (hf_splits : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hf_degree : f.natDegree = m) (hf_nodup : f.roots.Nodup)
    (hf_neg : ∀ r ∈ f.roots, r < 0) (hF_degree : F.natDegree ≤ m + 1)
    (hF_zero : 0 < F.eval 0)
    (hsign : ∀ r, f.IsRoot r → F.eval r * f.derivative.eval r < 0)
    (htop : F.coeff (m + 1) < 0) :
    F.natDegree = m + 1 ∧ F.leadingCoeff < 0 ∧ F.Splits ∧
      HasSimpleRoots F ∧
      ∃ rs : List ℝ, ∃ u : ℝ, rs.length = m ∧
        rs.Pairwise (fun x y ↦ x < y) ∧ (∀ r ∈ rs, r < 0) ∧ 0 < u ∧
        F.roots = (↑(rs ++ [u]) : Multiset ℝ) := by
  have hF_deg : F.natDegree = m + 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero hF_degree htop.ne
  have hF_lead : F.leadingCoeff < 0 := by
    simpa [leadingCoeff, hF_deg] using htop
  have hF_ne : F ≠ 0 := leadingCoeff_ne_zero.mp hF_lead.ne
  obtain ⟨rs, hrs_len, hrs_sorted, hrs_root, hrs_neg⟩ :=
    exists_negative_root_list_of_endpoint_sign hf_splits hf_pos hf_degree hf_nodup
      hf_neg hF_zero hsign
  have hdegree_pos : 0 < F.degree := natDegree_pos_iff_degree_pos.mp (by lia)
  obtain ⟨u, hu_nonneg, hu_root⟩ :=
    MaWang.exists_isRoot_ge_of_eval_nonneg_of_tendsto_atTop_atBot hF_zero.le
      (F.tendsto_atBot_of_leadingCoeff_nonpos hdegree_pos hF_lead.le)
  have hu_pos : 0 < u := lt_of_le_of_ne hu_nonneg fun hu ↦ by
    subst u
    exact hF_zero.ne' hu_root.eq_zero
  have hrs_lt_u : ∀ r ∈ rs, r < u := fun r hr ↦ (hrs_neg r hr).trans hu_pos
  have hcombined_sorted : (rs ++ [u]).Pairwise (fun x y ↦ x < y) := by
    rw [List.pairwise_append]
    refine ⟨hrs_sorted, by simp, ?_⟩
    intro r hr s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact hrs_lt_u r hr
  have hcombined_len : (rs ++ [u]).length = F.natDegree := by
    simp only [List.length_append, List.length_singleton]
    lia
  have hcombined_root : ∀ r ∈ rs ++ [u], F.IsRoot r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hrs_root r hr
    · simp only [List.mem_singleton] at hr
      subst r
      exact hu_root
  obtain ⟨hF_splits, hF_nodup, hroots_eq⟩ :=
    roots_eq_of_strict_root_list hF_ne hcombined_len hcombined_sorted hcombined_root
  exact ⟨hF_deg, hF_lead, hF_splits,
    HasSimpleRoots.of_roots_nodup hF_ne hF_nodup, rs, u, hrs_len, hrs_sorted,
    hrs_neg, hu_pos, hroots_eq.symm⟩

/-- Weak critical signs and a nonnegative prospective top coefficient force
the equal- or successor-degree negative-root branch. Repeated roots of the
output are allowed. -/
theorem rootSign_of_coeff_nonneg
    {f F : ℝ[X]} {m : ℕ}
    (hf_splits : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hf_degree : f.natDegree = m) (hf_nodup : f.roots.Nodup)
    (hf_neg : ∀ r ∈ f.roots, r < 0) (hF_degree : F.natDegree ≤ m + 1)
    (hF_zero : 0 < F.eval 0)
    (hsign : ∀ r, f.IsRoot r → F.eval r * f.derivative.eval r ≤ 0)
    (htop : 0 ≤ F.coeff (m + 1)) :
    F.natDegree = (if F.coeff (m + 1) = 0 then m else m + 1) ∧
      HasPosLeadingCoeff F ∧ StrictInterl f F ∧ F.Splits ∧
      (∀ r ∈ F.roots, r < 0) ∧ ∀ k ≤ F.natDegree, 0 < F.coeff k := by
  by_cases htop_zero : F.coeff (m + 1) = 0
  · have hf_nonneg :=
      hasNonnegCoeffs_of_splits_of_pos_of_roots_neg hf_splits hf_pos hf_neg
    have hfder_nonneg := hf_nonneg.derivative
    let d := f.derivative.eval 0
    have hd : 0 ≤ d := hfder_nonneg.eval_nonneg (x := 0) (le_refl 0)
    let eps := F.eval 0 / (2 * (d + 1))
    have hden : 0 < 2 * (d + 1) := by positivity
    have heps : 0 < eps := div_pos hF_zero hden
    have hepsd : eps * d < F.eval 0 := by
      dsimp only [eps]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    let G := F - C eps * f.derivative
    have hG_zero : 0 < G.eval 0 := by
      simp only [G, eval_sub, eval_mul, eval_C]
      linarith
    have hG_degree : G.natDegree ≤ m + 1 := by
      apply (natDegree_sub_le _ _).trans
      apply max_le hF_degree
      exact (natDegree_C_mul_le eps f.derivative).trans <|
        (natDegree_derivative_le f).trans (by lia)
    have hG_top : G.coeff (m + 1) = 0 := by
      have hcoeff : f.coeff (m + 2) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hf_degree]; lia)
      simp [G, coeff_sub, coeff_C_mul, coeff_derivative, htop_zero, hcoeff]
    have hder_ne : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0 :=
      fun _ hr ↦ eval_derivative_ne_zero_of_nodup hf_pos.ne_zero hf_nodup hr
    have hG_sign : ∀ r, f.IsRoot r → G.eval r * f.derivative.eval r < 0 := by
      intro r hr
      have hs := hsign r hr
      have hd_ne := hder_ne r hr
      simp only [G, eval_sub, eval_mul, eval_C]
      nlinarith [sq_pos_iff.mpr hd_ne]
    obtain ⟨hG_deg, hG_pos, _, hG_splits, _, hG_neg, hG_coeff⟩ :=
      rootSignSameDegree_of_coeff_eq_zero hf_splits hf_pos hf_degree hf_nodup
        hf_neg hG_degree hG_zero hG_sign hG_top
    have hder_coeff : (C eps * f.derivative).coeff m = 0 := by
      have hcoeff : f.coeff (m + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by rw [hf_degree]; lia)
      simp [coeff_C_mul, coeff_derivative, hcoeff]
    have hF_coeff : 0 < F.coeff m := by
      have h := hG_coeff m (by rw [hG_deg])
      simpa [G, coeff_sub, hder_coeff] using h
    have hF_le : F.natDegree ≤ m := by
      by_contra hle
      have heq : F.natDegree = m + 1 := by lia
      have hF_ne : F ≠ 0 := by
        intro hzero
        subst F
        simp at hF_zero
      have hlead_zero : F.leadingCoeff = 0 := by
        simpa [leadingCoeff, heq] using htop_zero
      exact (leadingCoeff_ne_zero.mpr hF_ne) hlead_zero
    have hF_deg : F.natDegree = m :=
      natDegree_eq_of_le_of_coeff_ne_zero hF_le hF_coeff.ne'
    have hF_pos : HasPosLeadingCoeff F := by
      simpa [HasPosLeadingCoeff, leadingCoeff, hF_deg] using hF_coeff
    have hstrict : StrictInterl f F :=
      strictInterl_of_eval_mul_derivative_nonpos hf_pos hf_splits hf_nodup hF_pos
        (by lia) (by lia) hsign
    have hF_splits : F.Splits := hstrict.2.1.2
    have hG_nonneg :=
      hasNonnegCoeffs_of_splits_of_pos_of_roots_neg hG_splits hG_pos hG_neg
    have hF_nonneg : HasNonnegCoeffs F := by
      have heq : F = G + C eps * f.derivative := by simp [G]
      rw [heq]
      exact hG_nonneg.add (hasNonnegCoeffs_C_mul heps.le hfder_nonneg)
    have hF_neg : ∀ r ∈ F.roots, r < 0 := by
      intro r hr
      have hr_le := roots_nonpos_of_hasNonnegCoeffs hF_nonneg r hr
      have hr_ne : r ≠ 0 := by
        intro hr_zero
        subst r
        have := (mem_roots hF_pos.ne_zero).mp hr
        exact hF_zero.ne' this.eq_zero
      exact lt_of_le_of_ne hr_le hr_ne
    refine ⟨by simp [htop_zero, hF_deg], hF_pos, hstrict, hF_splits, hF_neg, ?_⟩
    exact positive_coeffs_of_splits_of_pos_of_roots_neg hF_splits hF_pos hF_neg
  · have htop_pos : 0 < F.coeff (m + 1) := lt_of_le_of_ne htop (Ne.symm htop_zero)
    have hF_deg : F.natDegree = m + 1 :=
      natDegree_eq_of_le_of_coeff_ne_zero hF_degree htop_pos.ne'
    have hF_pos : HasPosLeadingCoeff F := by
      simpa [HasPosLeadingCoeff, leadingCoeff, hF_deg] using htop_pos
    have hstrict : StrictInterl f F :=
      strictInterl_of_eval_mul_derivative_nonpos hf_pos hf_splits hf_nodup hF_pos
        (by lia) (by lia) hsign
    have hinter : Interlaces f F := hstrict.toInterlaces (by lia)
    have hF_splits : F.Splits := hstrict.2.1.2
    have hF_neg_root : ∀ r, F.IsRoot r → r < 0 :=
      roots_neg_of_interlaces_of_eval_zero_pos hinter hF_pos hF_zero fun r hr ↦
        hf_neg r ((mem_roots hf_pos.ne_zero).mpr hr)
    have hF_neg : ∀ r ∈ F.roots, r < 0 := fun r hr ↦
      hF_neg_root r ((mem_roots hF_pos.ne_zero).mp hr)
    refine ⟨by simp [htop_zero, hF_deg], hF_pos, hstrict, hF_splits, hF_neg, ?_⟩
    exact positive_coeffs_of_splits_of_pos_of_roots_neg hF_splits hF_pos hF_neg

/-- A derivative term with a strictly negative multiplier, together with
nonpositive multipliers of preceding polynomials, supplies the strict critical
signs needed by the endpoint criterion. -/
theorem rootSign_derivativeLag
    {ι : Type*} (s : Finset ι) {f F u v : ℝ[X]} {w g : ι → ℝ[X]} {m : ℕ}
    (hF : F = u * f + v * f.derivative + ∑ i ∈ s, w i * g i)
    (hf_splits : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hf_degree : f.natDegree = m) (hf_nodup : f.roots.Nodup)
    (hf_neg : ∀ r ∈ f.roots, r < 0)
    (hg_interl : ∀ i ∈ s, StrictInterl (g i) f)
    (hg_pos : ∀ i ∈ s, HasPosLeadingCoeff (g i))
    (hv : ∀ r, f.IsRoot r → v.eval r < 0)
    (hw : ∀ i ∈ s, ∀ r, f.IsRoot r → (w i).eval r ≤ 0)
    (hF_degree : F.natDegree ≤ m + 1) (hF_zero : 0 < F.eval 0)
    (htop : 0 ≤ F.coeff (m + 1)) :
    F.natDegree = (if F.coeff (m + 1) = 0 then m else m + 1) ∧
      HasPosLeadingCoeff F ∧ StrictInterl f F ∧ F.Splits ∧
      HasSimpleRoots F ∧ (∀ r ∈ F.roots, r < 0) ∧
      ∀ k ≤ F.natDegree, 0 < F.coeff k := by
  classical
  have hder_ne : ∀ r, f.IsRoot r → f.derivative.eval r ≠ 0 :=
    fun _ hr ↦ eval_derivative_ne_zero_of_nodup hf_pos.ne_zero hf_nodup hr
  have hsign : ∀ r, f.IsRoot r → F.eval r * f.derivative.eval r < 0 := by
    intro r hr
    have hv_term : v.eval r * (f.derivative.eval r) ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (hv r hr) (sq_pos_iff.mpr (hder_ne r hr))
    have hsum :
        ∑ i ∈ s, (w i).eval r * (g i).eval r * f.derivative.eval r ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      rw [mul_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg (hw i hi r hr)
        ((hg_interl i hi).eval_mul_eval_derivative_nonneg (hg_pos i hi) hf_pos hr)
    calc
      F.eval r * f.derivative.eval r =
          v.eval r * (f.derivative.eval r) ^ 2 +
            ∑ i ∈ s, (w i).eval r * (g i).eval r * f.derivative.eval r := by
        rw [hF, eval_add, eval_add, eval_mul, hr.eq_zero, mul_zero, zero_add,
          eval_mul, eval_finsetSum, add_mul, Finset.sum_mul]
        simp only [eval_mul]
        ring
      _ < 0 := by linarith
  by_cases htop_zero : F.coeff (m + 1) = 0
  · obtain ⟨hdeg, hpos, hinterl, hsplits, hsimple, hneg, hcoeff⟩ :=
      rootSignSameDegree_of_coeff_eq_zero hf_splits hf_pos hf_degree hf_nodup
        hf_neg hF_degree hF_zero hsign htop_zero
    exact ⟨by simp [htop_zero, hdeg], hpos, hinterl, hsplits, hsimple, hneg, hcoeff⟩
  · have htop_pos : 0 < F.coeff (m + 1) := lt_of_le_of_ne htop (Ne.symm htop_zero)
    obtain ⟨hdeg, hpos, hinterl, hsplits, hsimple, hneg, hcoeff⟩ :=
      rootSignSuccessor_of_coeff_pos hf_splits hf_pos hf_degree hf_nodup hf_neg
        hF_degree hF_zero hsign htop_pos
    exact ⟨by simp [htop_zero, hdeg], hpos, hinterl, hsplits, hsimple, hneg, hcoeff⟩

/-- The normalized one-lag family from the endpoint criterion has the
displayed nonnegative prospective coefficient and is simple negative-rooted.
The polynomial in the conclusion is the expansion of
`((a + b X) f + c X (1 - X) f' - d (1 - X) g) / (a - d)`. -/
theorem normalizedDerivativeLag_rootSign
    {f g : ℝ[X]} {m : ℕ} {a b c d : ℝ}
    (hf_splits : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hf_degree : f.natDegree = m) (hf_nodup : f.roots.Nodup)
    (hf_neg : ∀ r ∈ f.roots, r < 0) (hf_zero : f.eval 0 = 1)
    (hgf : StrictInterl g f) (hg_pos : HasPosLeadingCoeff g)
    (hg_zero : g.eval 0 = 1) (hc : 0 < c) (hd : 0 ≤ d)
    (hb : c * (m : ℝ) ≤ b) (ha : d < a) :
    let F := C (a - d)⁻¹ *
      (((C c * X + C (-c) * X ^ 2) * f.derivative +
          (C a + C b * X) * f) + (C d * X * g - C d * g))
    F.coeff (m + 1) =
        (a - d)⁻¹ * ((b - c * (m : ℝ)) * f.leadingCoeff + d * g.coeff m) ∧
      F.natDegree = (if F.coeff (m + 1) = 0 then m else m + 1) ∧
      HasPosLeadingCoeff F ∧ StrictInterl f F ∧ F.Splits ∧
      HasSimpleRoots F ∧ (∀ r ∈ F.roots, r < 0) ∧
      ∀ k ≤ F.natDegree, 0 < F.coeff k := by
  let Q := (C c * X + C (-c) * X ^ 2) * f.derivative +
    (C a + C b * X) * f
  let R := C d * X * g - C d * g
  let H := Q + R
  let F := C (a - d)⁻¹ * H
  change F.coeff (m + 1) = _ ∧ F.natDegree = _ ∧ _
  have hag_pos : 0 < a - d := sub_pos.mpr ha
  have hinv_pos : 0 < (a - d)⁻¹ := inv_pos.mpr hag_pos
  have hg_degree : g.natDegree ≤ m := by
    rw [← hf_degree]
    exact hgf.natDegree_le
  have hg_top_nonneg : 0 ≤ g.coeff m := by
    by_cases hgm : g.natDegree = m
    · simpa [leadingCoeff, hgm] using hg_pos.le
    · rw [coeff_eq_zero_of_natDegree_lt]
      exact lt_of_le_of_ne hg_degree hgm
  have hQ_degree : Q.natDegree ≤ m + 1 := by
    dsimp only [Q]
    rw [← hf_degree]
    simpa using Polynomial.natDegree_quadratic_derivative_add_linear_mul_add_le
      f 0 c (-c) a b (Nat.zero_le _)
  have hXg_degree : (C d * X * g).natDegree ≤ m + 1 := by
    calc
      (C d * X * g).natDegree ≤ (C d * X).natDegree + g.natDegree :=
        natDegree_mul_le
      _ ≤ 1 + m := Nat.add_le_add
        ((natDegree_C_mul_le d X).trans natDegree_X_le) hg_degree
      _ = m + 1 := by lia
  have hCg_degree : (C d * g).natDegree ≤ m + 1 :=
    (natDegree_C_mul_le d g).trans (hg_degree.trans (Nat.le_add_right m 1))
  have hR_degree : R.natDegree ≤ m + 1 := by
    exact (natDegree_sub_le _ _).trans (max_le hXg_degree hCg_degree)
  have hH_degree : H.natDegree ≤ m + 1 := by
    exact (natDegree_add_le _ _).trans (max_le hQ_degree hR_degree)
  have hF_degree : F.natDegree ≤ m + 1 := by
    exact (natDegree_C_mul_le (a - d)⁻¹ H).trans hH_degree
  have hQ_top : Q.coeff (m + 1) =
      (b - c * (m : ℝ)) * f.leadingCoeff := by
    dsimp only [Q]
    rw [← hf_degree]
    have h := Polynomial.coeff_quadratic_derivative_add_linear_mul_add_natDegree_succ
      f 0 c (-c) a b (Nat.zero_le _)
    convert h using 1 <;> ring_nf
  have hg_above : g.coeff (m + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hg_degree (Nat.lt_succ_self m))
  have hXg_top : (C d * X * g).coeff (m + 1) = d * g.coeff m := by
    rw [mul_assoc, coeff_C_mul, Polynomial.coeff_X_mul g m]
  have hR_top : R.coeff (m + 1) = d * g.coeff m := by
    simp only [R, coeff_sub, hXg_top, coeff_C_mul, hg_above, mul_zero, sub_zero]
  have htop_formula : F.coeff (m + 1) =
      (a - d)⁻¹ * ((b - c * (m : ℝ)) * f.leadingCoeff + d * g.coeff m) := by
    simp only [F, H, coeff_C_mul, coeff_add, hQ_top, hR_top]
  have htop_nonneg : 0 ≤ F.coeff (m + 1) := by
    rw [htop_formula]
    exact mul_nonneg hinv_pos.le <| add_nonneg
      (mul_nonneg (sub_nonneg.mpr hb) hf_pos.le) (mul_nonneg hd hg_top_nonneg)
  have hF_zero : 0 < F.eval 0 := by
    simp only [F, H, Q, R, eval_mul, eval_C, eval_add, eval_sub, eval_X,
      eval_pow, hf_zero, hg_zero]
    norm_num
    exact mul_pos hinv_pos hag_pos
  have hsign : ∀ r, f.IsRoot r → F.eval r * f.derivative.eval r < 0 := by
    intro r hr
    have hr_mem := (mem_roots hf_pos.ne_zero).mpr hr
    have hr_neg := hf_neg r hr_mem
    have hder_ne := eval_derivative_ne_zero_of_nodup hf_pos.ne_zero hf_nodup hr
    have hgf_sign := hgf.eval_mul_eval_derivative_nonneg hg_pos hf_pos hr
    simp only [F, H, Q, R, eval_mul, eval_C, eval_add, eval_sub, eval_X,
      eval_pow, hr.eq_zero, mul_zero, add_zero]
    rw [mul_assoc]
    apply mul_neg_of_pos_of_neg hinv_pos
    calc
      ((c * r + -c * r ^ 2) * f.derivative.eval r +
          (d * r * g.eval r - d * g.eval r)) * f.derivative.eval r =
          c * r * (1 - r) * (f.derivative.eval r) ^ 2 +
            (-d * (1 - r)) * (g.eval r * f.derivative.eval r) := by ring
      _ < 0 := by
        have hder_term : c * r * (1 - r) * (f.derivative.eval r) ^ 2 < 0 := by
          have hcr : c * r < 0 := mul_neg_of_pos_of_neg hc hr_neg
          have hone : 0 < 1 - r := by linarith
          exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hcr hone)
            (sq_pos_iff.mpr hder_ne)
        have hlag_term :
            (-d * (1 - r)) * (g.eval r * f.derivative.eval r) ≤ 0 := by
          have hone : 0 ≤ 1 - r := by linarith
          exact mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd) hone) hgf_sign
        linarith
  by_cases htop_zero : F.coeff (m + 1) = 0
  · obtain ⟨hdeg, hpos, hinterl, hsplits, hsimple, hneg, hcoeff⟩ :=
      rootSignSameDegree_of_coeff_eq_zero hf_splits hf_pos hf_degree hf_nodup
        hf_neg hF_degree hF_zero hsign htop_zero
    have hdegree_if : F.natDegree =
        (if F.coeff (m + 1) = 0 then m else m + 1) := by
      simpa only [htop_zero, ↓reduceIte] using hdeg
    exact ⟨htop_formula, hdegree_if, hpos, hinterl, hsplits,
      hsimple, hneg, hcoeff⟩
  · have htop_pos : 0 < F.coeff (m + 1) :=
      lt_of_le_of_ne htop_nonneg (Ne.symm htop_zero)
    obtain ⟨hdeg, hpos, hinterl, hsplits, hsimple, hneg, hcoeff⟩ :=
      rootSignSuccessor_of_coeff_pos hf_splits hf_pos hf_degree hf_nodup hf_neg
        hF_degree hF_zero hsign htop_pos
    have hdegree_if : F.natDegree =
        (if F.coeff (m + 1) = 0 then m else m + 1) := by
      simpa only [htop_zero, ↓reduceIte] using hdeg
    exact ⟨htop_formula, hdegree_if, hpos, hinterl, hsplits,
      hsimple, hneg, hcoeff⟩

end RealRooted

