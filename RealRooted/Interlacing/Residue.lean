import RealRooted.Derivative
import RealRooted.Mathlib.Algebra.Polynomial.Splits.Derivative
import RealRooted.WagnerX.AffineFactors
import Mathlib.LinearAlgebra.Lagrange

/-!
# Lagrange residues for interlacing polynomials

Real-root signs, residue positivity, Lagrange interpolation at simple roots,
and common-root cofactor transport.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-! ## Derivative and evaluation signs -/

theorem eval_derivative_eq_sum_real {p : ℝ[X]} (hp : p.Splits) (x : ℝ) :
    p.derivative.eval x
      = p.leadingCoeff *
          (p.roots.map (fun r : ℝ =>
            ((p.roots.erase r).map (fun s : ℝ => x - s)).prod)).sum :=
  hp.eval_derivative x

theorem deriv_sum_collapse (M : Multiset ℝ) (s : ℝ) (hs : s ∈ M) (hcount : M.count s = 1) :
    (M.map (fun r : ℝ => ((M.erase r).map (fun t : ℝ => s - t)).prod)).sum
      = ((M.erase s).map (fun t : ℝ => s - t)).prod :=
  derivative_sum_collapse M s hs hcount

theorem eval_derivative_at_root {p : ℝ[X]} (hp : p.Splits) (s : ℝ)
    (hs : s ∈ p.roots) (hcount : p.roots.count s = 1) :
    p.derivative.eval s
      = p.leadingCoeff * ((p.roots.erase s).map (fun r : ℝ => s - r)).prod :=
  hp.eval_derivative_at_root_of_roots_count_one s hs hcount

theorem prod_sub_sign_pos (M : Multiset ℝ) (s : ℝ) (hs : s ∉ M) :
    0 < (M.map (fun r => s - r)).prod * (-1 : ℝ) ^ (M.countP (fun r => s < r)) := by
  induction M using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.countP_cons]
    have h_s_notin_t : s ∉ t := fun h_mem ↦ hs (Multiset.mem_cons_of_mem h_mem)
    have h_as_ne : a ≠ s := fun h_eq ↦ hs (h_eq ▸ Multiset.mem_cons_self a t)
    have h_ih := ih h_s_notin_t
    set P := (t.map (fun r => s - r)).prod * (-1 : ℝ) ^ (t.countP (fun r => s < r))
    by_cases h_lt : s < a
    · simp only [h_lt, if_true, pow_add, pow_one]
      have : (s - a) * (t.map (fun r ↦ s - r)).prod *
          ((-1 : ℝ) ^ t.countP (fun r ↦ s < r) * -1) = (a - s) * P := by ring
      simp_all
    · simp only [h_lt, if_false, Nat.add_zero]
      have h_as_lt : a < s := lt_of_le_of_ne (not_lt.mp h_lt) h_as_ne
      have : (s - a) * (t.map (fun r ↦ s - r)).prod *
          (-1 : ℝ) ^ t.countP (fun r ↦ s < r) = (s - a) * P := by ring
      simp_all

theorem deriv_at_root_sign {p : ℝ[X]} (hp : p.Splits) (hlc : 0 < p.leadingCoeff) (s : ℝ)
    (hs : s ∈ p.roots) (hcount : p.roots.count s = 1) :
    0 < p.derivative.eval s * (-1 : ℝ) ^ (p.roots.countP (fun r => s < r)) := by
  have h_s_M : s ∉ p.roots.erase s := by
    intro h
    rw [← Multiset.count_pos, Multiset.count_erase_self] at h
    lia
  have h_cnt : (p.roots.erase s).countP (fun r ↦ s < r)
      = p.roots.countP (fun r ↦ s < r) := by
    rw [← Multiset.cons_erase hs, Multiset.countP_cons]
    simp
  rw [hp.eval_derivative_at_root_of_roots_count_one s hs hcount, mul_assoc]
  have h_pos := prod_sub_sign_pos (p.roots.erase s) s h_s_M
  rw [h_cnt] at h_pos
  exact mul_pos hlc h_pos

theorem eval_sign {p : ℝ[X]} (hp : p.Splits) (hlc : 0 < p.leadingCoeff) (s : ℝ)
    (hs : s ∉ p.roots) :
    0 < p.eval s * (-1 : ℝ) ^ (p.roots.countP (fun r => s < r)) := by
  have hev : p.eval s = p.leadingCoeff * (p.roots.map (fun r => s - r)).prod := by
    conv_lhs => rw [hp.eq_prod_roots]
    simp [eval_multiset_prod, Multiset.map_map, Function.comp]
  rw [hev, mul_assoc]
  exact mul_pos hlc (prod_sub_sign_pos p.roots s hs)

/-! ## Strict interlacing ranks -/

private theorem countP_min_strict (a : ℝ) (l : List ℝ) (h : (a :: l).Pairwise (· < ·)) :
    (a :: l).countP (fun r ↦ decide (a < r)) = l.length := by simp_all

theorem countP_eq_interlaces_strict :
    ∀ (ss rs : List ℝ), ss.Pairwise (· < ·) → rs.Pairwise (· < ·) →
    ListInterlaces ss rs → ∀ x ∈ rs, x ∉ ss →
    (rs.countP (fun r => decide (x < r))) =
      (ss.countP (fun s => decide (x < s))) := by
  intro ss rs
  induction ss generalizing rs with
  | nil =>
    intro _ _ hint
    match rs with
    | [] => simp
    | [r] => simp
    | r₁ :: r₂ :: rest => simp [ListInterlaces] at hint
  | cons s ss ih =>
    intro hss_sorted hrs_sorted hint
    match rs with
    | [] => simp
    | [r] => simp [ListInterlaces] at hint
    | r₁ :: r₂ :: rest =>
      obtain ⟨h₁, h₂, htail⟩ := hint
      have hrs_sorted' := hrs_sorted
      rw [List.pairwise_cons] at hrs_sorted
      obtain ⟨hr₁_lt, hrs_tail_sorted⟩ := hrs_sorted
      rw [List.pairwise_cons] at hss_sorted
      obtain ⟨hs_lt, hss_tail_sorted⟩ := hss_sorted
      intro x hx hxnss
      simp only [List.mem_cons] at hx
      simp only [List.mem_cons, not_or] at hxnss
      obtain ⟨hxs, hxss⟩ := hxnss
      rcases hx with hxr₁ | hx₂
      · subst hxr₁
        have hr₁s : x < s := lt_of_le_of_ne h₁ hxs
        rw [countP_min_strict x (r₂ :: rest) hrs_sorted']
        have hcg : (s :: ss).countP (fun r => decide (x < r)) = (s :: ss).length := by
          apply List.countP_eq_length.mpr
          intro a ha; simp only [decide_eq_true_eq]
          rcases List.mem_cons.mp ha with rfl | hass
          · exact hr₁s
          · exact hr₁s.trans (hs_lt a hass)
        rw [hcg, List.length_cons]
        have hlen : (r₂ :: rest).length = ss.length + 1 := by
          have := listInterlaces_cons_length_eq htail
          simp [*]
        simp_all
      · have hxmem : x ∈ r₂ :: rest := List.mem_cons.mpr hx₂
        have hr₂x : r₂ ≤ x := by
          rcases hx₂ with rfl | hxrest
          · simp
          · exact le_of_lt (List.rel_of_pairwise_cons hrs_tail_sorted hxrest)
        have hxr₁' : ¬ x < r₁ := by linarith [hr₁_lt r₂ (by simp : r₂ ∈ r₂ :: rest)]
        have hxs' : ¬ x < s := by linarith
        simp [*]

theorem countP_eq_alternates_strict :
    ∀ (ss rs : List ℝ), ss.Pairwise (· < ·) → rs.Pairwise (· < ·) →
    ListAlternates ss rs → ∀ x ∈ rs, x ∉ ss →
    (rs.countP (fun r ↦ decide (x < r))) =
      (ss.countP (fun s ↦ decide (x < s))) := by
  intro ss rs hss hrs halt x hx hxnss
  match ss, rs with
  | [], [] => simp
  | [], r :: rs' => simp [ListAlternates] at halt
  | s :: ss', [] => simp [ListAlternates] at halt
  | s :: ss', r :: rs' =>
    obtain ⟨hsr, htail⟩ := halt
    rw [List.pairwise_cons] at hss hrs
    obtain ⟨hs_lt, hss'⟩ := hss
    obtain ⟨hr_lt, hrs'⟩ := hrs
    simp only [List.mem_cons, not_or] at hxnss
    obtain ⟨hxs, hxss'⟩ := hxnss
    have hrx : r ≤ x := by
      rcases List.mem_cons.mp hx with rfl | hxrs'
      · simp
      · exact le_of_lt (hr_lt x hxrs')
    have hxs' : ¬ x < s := by linarith [hsr]
    have h_eq := countP_eq_interlaces_strict ss' (r :: rs') hss'
      (by simp_all) htail x hx hxss'
    simp [*]

theorem prec_countP_eq {f g : ℝ[X]} (hpq : Prec g f)
    (hfnd : f.roots.Nodup) (hgnd : g.roots.Nodup)
    (x : ℝ) (hxf : x ∈ f.roots) (hxg : x ∉ g.roots) :
    f.roots.countP (fun r => x < r) = g.roots.countP (fun r => x < r) := by
  obtain ⟨⟨hg₀, hgs⟩, ⟨hf₀, hfs⟩, ss, rs, hss, hrs, hsseq, hrseq, hshape⟩ := hpq
  have hrs_strict : rs.Pairwise (· < ·) :=
    (hrs.sortedLE.sortedLT_of_nodup (by
      rw [← Multiset.coe_nodup, hrseq]
      exact hfnd)).pairwise
  have hss_strict : ss.Pairwise (· < ·) :=
    (hss.sortedLE.sortedLT_of_nodup (by
      rw [← Multiset.coe_nodup, hsseq]
      exact hgnd)).pairwise
  have hxrs : x ∈ rs := by rw [← Multiset.mem_coe, hrseq]; simp_all
  have hxss : x ∉ ss := by rw [← Multiset.mem_coe, hsseq]; simp [*]
  have hlist : rs.countP (fun r ↦ decide (x < r)) = ss.countP (fun s ↦ decide (x < s)) := by
    rcases hshape with ⟨_, hint⟩ | ⟨_, halt⟩
    · exact countP_eq_interlaces_strict ss rs hss_strict hrs_strict hint x hxrs hxss
    · exact countP_eq_alternates_strict ss rs hss_strict hrs_strict halt x hxrs hxss
  rw [← hrseq, ← hsseq, Multiset.coe_countP, Multiset.coe_countP]
  simp [*]

/-! ## Residue positivity -/

theorem residue_sign_pos {f g : ℝ[X]} (hpq : Prec g f)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff)
    (hfnd : f.roots.Nodup) (hgnd : g.roots.Nodup)
    (s : ℝ) (hsf : s ∈ f.roots) (hsg : s ∉ g.roots) :
    0 < g.eval s * f.derivative.eval s := by
  obtain ⟨⟨hg₀, hgs⟩, ⟨hf₀, hfs⟩, _⟩ := id hpq
  have hcount : f.roots.count s = 1 := Multiset.count_eq_one_of_mem hfnd hsf
  have hf' := deriv_at_root_sign hfs hflc s hsf hcount
  have hg := eval_sign hgs hglc s hsg
  have hcnt := prec_countP_eq hpq hfnd hgnd s hsf hsg
  rw [hcnt] at hf'
  set n := g.roots.countP (fun r ↦ s < r)
  set e := (-1 : ℝ) ^ n
  have he₂ : e * e = 1 := by
    simp only [e]
    rw [← pow_add]
    simp
  have h_pos : 0 < (g.eval s * e) * (f.derivative.eval s * e) := mul_pos hg hf'
  have h_eq : (g.eval s * e) * (f.derivative.eval s * e)
      = g.eval s * f.derivative.eval s * (e * e) := by ring
  rwa [h_eq, he₂, mul_one] at h_pos

theorem residue_nonneg {f g : ℝ[X]} (hpq : Prec g f)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff)
    (hfnd : f.roots.Nodup) (hgnd : g.roots.Nodup)
    (s : ℝ) (hsf : s ∈ f.roots) (hsg : s ∉ g.roots) :
    0 ≤ g.eval s / f.derivative.eval s := by
  have h_pos := residue_sign_pos hpq hflc hglc hfnd hgnd s hsf hsg
  rcases mul_pos_iff.mp h_pos with h | h
  · exact div_nonneg h.1.le h.2.le
  · exact div_nonneg_of_nonpos h.1.le h.2.le

/-! ## Lagrange interpolation -/

theorem eval_divByMonic_at_root {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) :
    (f /ₘ (X - C r)).eval r = f.derivative.eval r := by
  nth_rw 2 [← mul_divByMonic_eq_iff_isRoot.mpr hr]
  simp

theorem eval_divByMonic_at_other_root {f : ℝ[X]} {t s : ℝ}
    (ht : f.IsRoot t) (hs : f.IsRoot s) (hst : s ≠ t) : (f /ₘ (X - C t)).eval s = 0 := by
  have h_eval := congrArg (eval s) (mul_divByMonic_eq_iff_isRoot.mpr ht)
  rw [eval_mul, hs] at h_eval
  exact (mul_eq_zero.mp h_eval).resolve_left <| by
    simp only [eval_sub, eval_X, eval_C]
    exact sub_ne_zero.mpr hst

theorem derivative_eval_ne_zero_of_simple_root {f : ℝ[X]} {r : ℝ}
    (hr : f.IsRoot r) (hsimple : f.rootMultiplicity r = 1) : f.derivative.eval r ≠ 0 :=
  eval_derivative_ne_zero_of_rootMultiplicity_eq_one hr hsimple

noncomputable def lagInterp (f g : ℝ[X]) : ℝ[X] :=
  ∑ s ∈ f.roots.toFinset, C (g.eval s / f.derivative.eval s) * (f /ₘ (X - C s))

theorem eval_lagInterp_at_root {f g : ℝ[X]} (hnd : f.roots.Nodup)
    {sk : ℝ} (hsk : sk ∈ f.roots) :
    (lagInterp f g).eval sk = g.eval sk := by
  have hsk_root : f.IsRoot sk := isRoot_of_mem_roots hsk
  have h_mult : f.rootMultiplicity sk = 1 := by
    simpa [count_roots] using Multiset.count_eq_one_of_mem hnd hsk
  have : f.derivative.eval sk ≠ 0 := derivative_eval_ne_zero_of_simple_root hsk_root h_mult
  have : sk ∈ f.roots.toFinset := Multiset.mem_toFinset.mpr hsk
  rw [lagInterp, eval_finsetSum, Finset.sum_eq_single sk]
  · rw [eval_mul, eval_C, eval_divByMonic_at_root hsk_root]
    simp [*]
  · intro s hs hssk
    have hsroot : f.IsRoot s := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hs)
    rw [eval_mul, eval_divByMonic_at_other_root hsroot hsk_root (fun h ↦ hssk h.symm), mul_zero]
  · simp [*]

theorem lagInterp_degree_lt {f g : ℝ[X]} (hfs : f.Splits) (hnd : f.roots.Nodup)
    (h_deg₁ : 1 ≤ f.natDegree) :
    (lagInterp f g).degree < f.roots.toFinset.card := by
  rw [Multiset.toFinset_card_of_nodup hnd, card_roots_of_splits hfs, lagInterp]
  apply lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
  have : (⊥ : WithBot ℕ) < (f.natDegree : WithBot ℕ) := by simp
  rw [Finset.sup_lt_iff this]
  intro s hs
  have : (C (g.eval s / f.derivative.eval s) * (f /ₘ (X - C s))).degree
      ≤ (f /ₘ (X - C s)).degree := by
    apply le_trans (degree_mul_le _ _)
    calc (C (g.eval s / f.derivative.eval s)).degree + (f /ₘ (X - C s)).degree
        ≤ 0 + (f /ₘ (X - C s)).degree := by gcongr; exact degree_C_le
      _ = (f /ₘ (X - C s)).degree := by simp
  apply lt_of_le_of_lt this
  have : (f /ₘ (X - C s)).natDegree = f.natDegree - 1 := by
    rw [natDegree_divByMonic f (monic_X_sub_C s)]
    simp
  calc (f /ₘ (X - C s)).degree ≤ ((f /ₘ (X - C s)).natDegree : WithBot ℕ) :=
      degree_le_natDegree
    _ = ((f.natDegree - 1 : ℕ) : WithBot ℕ) := by simp [*]
    _ < (f.natDegree : WithBot ℕ) := by exact_mod_cast by lia

theorem lagInterp_eq_g {f g : ℝ[X]} (hfs : f.Splits) (hnd : f.roots.Nodup)
    (h_deg₁ : 1 ≤ f.natDegree) (hgdeg : g.degree < f.natDegree) :
    lagInterp f g = g := by
  have : f.roots.toFinset.card = f.natDegree := by
    rw [Multiset.toFinset_card_of_nodup hnd, card_roots_of_splits hfs]
  have h_deg_lt : (lagInterp f g).degree < f.roots.toFinset.card :=
    lagInterp_degree_lt hfs hnd h_deg₁
  apply eq_of_degrees_lt_of_eval_finset_eq f.roots.toFinset h_deg_lt
  · simp [*]
  · intro x hx
    exact eval_lagInterp_at_root hnd (Multiset.mem_toFinset.mp hx)

/-! ## Leading-term cancellation -/

theorem degree_sub_c₀_mul_lt {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree) (hflc : 0 < f.leadingCoeff) :
    (g - C (g.leadingCoeff / f.leadingCoeff) * f).degree < f.natDegree := by
  have hf : f.leadingCoeff ≠ 0 := hflc.ne'
  have hc : g.leadingCoeff / f.leadingCoeff ≠ 0 :=
    div_ne_zero (leadingCoeff_ne_zero.mpr hg₀) hf
  have h := degree_sub_lt (p := g) (q := C (g.leadingCoeff / f.leadingCoeff) * f)
    (by rw [degree_C_mul hc, degree_eq_natDegree hg₀, degree_eq_natDegree hf₀, hdeg])
    hg₀ (by simp [hf])
  rwa [degree_eq_natDegree hg₀, hdeg] at h

/-! ## Common-root cofactor transport -/

theorem prec_cofactor_of_common_root {f g : ℝ[X]} {r : ℝ}
    (hpq : Prec g f) (hrf : f.IsRoot r) (hrg : g.IsRoot r) :
    Prec (g /ₘ (X - C r)) (f /ₘ (X - C r)) := by
  have : (X - C r) * (f /ₘ (X - C r)) = f := mul_divByMonic_eq_iff_isRoot.mpr hrf
  have : (X - C r) * (g /ₘ (X - C r)) = g := mul_divByMonic_eq_iff_isRoot.mpr hrg
  apply prec_of_prec_mul_X_sub_C_both r
  simp [*]

theorem prec_of_prec_cofactor {f g : ℝ[X]} {r : ℝ}
    (hrf : f.IsRoot r) (hrg : g.IsRoot r)
    (h : Prec (g /ₘ (X - C r)) (f /ₘ (X - C r))) : Prec g f := by
  have hff : (X - C r) * (f /ₘ (X - C r)) = f := mul_divByMonic_eq_iff_isRoot.mpr hrf
  have hgg : (X - C r) * (g /ₘ (X - C r)) = g := mul_divByMonic_eq_iff_isRoot.mpr hrg
  have := prec_mul_X_sub_C_both r h
  simp_all

theorem leadingCoeff_divByMonic_X_sub_C {f : ℝ[X]} {r : ℝ} (hr : f.IsRoot r) :
    (f /ₘ (X - C r)).leadingCoeff = f.leadingCoeff := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · exact Polynomial.leadingCoeff_divByMonic_X_sub_C f
      (ne_of_gt (degree_pos_of_root hf hr)) r

end RealRooted
