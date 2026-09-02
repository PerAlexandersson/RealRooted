import RealRooted.HermiteBiehler.Basic
import RealRooted.HermiteBiehler.LogDerivative
import RealRooted.Interlacing.Multiplicity
import RealRooted.Interlacing.Residue

/-!
# Forward Hermite--Biehler theorem

This file proves upper-half-plane stability of the Hermite--Biehler polynomial
from proper position and sign-normalized leading coefficients. It also exposes
the multiset sign and partial-fraction helpers used by the converse theory.
-/

open Polynomial

noncomputable section

namespace RealRooted

theorem multiset_sum_im (s : Multiset ℂ) : s.sum.im = (s.map Complex.im).sum :=
  map_multiset_sum Complex.imAddGroupHom s

theorem multiset_sum_nonpos (s : Multiset ℝ) (h : ∀ x ∈ s, x ≤ 0) :
    s.sum ≤ 0 := by
  have := Multiset.sum_nonneg (s := s.map (fun x => -x))
    (by simpa using fun x hx => h x hx)
  rwa [Multiset.sum_map_neg, Multiset.map_id', neg_nonneg] at this

private theorem multiset_sum_neg (s : Multiset ℝ) (h_ne : s ≠ 0) (h : ∀ x ∈ s, x < 0) :
    s.sum < 0 := by
  simpa using Multiset.sum_lt_sum_of_nonempty (f := id) (g := fun _ => (0 : ℝ)) h_ne h

theorem multiset_sum_nonpos_eq_zero {s : Multiset ℝ} (h : ∀ x ∈ s, x ≤ 0)
    (hs : s.sum = 0) : ∀ x ∈ s, x = 0 := by
  have h0 : ∀ x ∈ s.map (fun x => -x), 0 ≤ x := by simpa using fun x hx => h x hx
  have hsum : (s.map (fun x => -x)).sum = 0 := by
    rw [Multiset.sum_map_neg, Multiset.map_id', hs, neg_zero]
  intro x hx
  have := Multiset.all_zero_of_le_zero_le_of_sum_eq_zero h0 hsum (-x)
    (Multiset.mem_map_of_mem _ hx)
  linarith

theorem logDeriv_complexify_im_neg {p : ℝ[X]} (hp : p.Splits) (hp₀ : p ≠ 0)
    (hdeg : 1 ≤ p.natDegree) {z : ℂ} (hz : 0 < z.im) :
    ((complexify p).derivative.eval z / (complexify p).eval z).im < 0 := by
  rw [logDeriv_complexify_eq_sum hp hp₀ hz, multiset_sum_im, Multiset.map_map]
  apply multiset_sum_neg
  · rw [Ne, Multiset.map_eq_zero, ← Multiset.card_eq_zero, card_roots_of_splits hp]
    lia
  · intro x hx
    simp only [Multiset.mem_map] at hx
    obtain ⟨r, -, rfl⟩ := hx
    simp only [Function.comp_apply]
    exact inv_sub_real_im_neg r hz

theorem im_ratio_sub_real_nonpos (z : ℂ) (r s : ℝ) (hz : 0 < z.im) (hrs : r ≤ s) :
    ((z - (r : ℂ)) / (z - (s : ℂ))).im ≤ 0 := by
  by_cases hne : z - (s : ℂ) = 0
  · simp [*]
  rw [Complex.div_im]
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.sub_re, Complex.ofReal_re]
  rw [div_sub_div_same]
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [hz, hrs]
  · exact Complex.normSq_nonneg _

theorem ratio_eq_I_of_hermiteBiehler_root {f g : ℝ[X]} {z : ℂ}
    (h : (hermiteBiehlerPolynomial f g).eval z = 0)
    (hf : (complexify f).eval z ≠ 0) :
    (complexify g).eval z / (complexify f).eval z = Complex.I := by
  rw [eval_hermiteBiehlerPolynomial] at h
  set F := (complexify f).eval z
  set G := (complexify g).eval z
  have h_I_sq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h_G : G = Complex.I * F := by
    have h_eq : G - Complex.I * F = 0 := by
      have h_step : G - Complex.I * F = -(Complex.I * (F + Complex.I * G)) := by
        rw [mul_add, ← mul_assoc, h_I_sq]; ring
      simp [*]
    exact sub_eq_zero.mp h_eq
  simp [*]

theorem im_real_mul_nonpos (c : ℝ) (w : ℂ) (hc : 0 ≤ c) (hw : w.im ≤ 0) :
    ((c : ℂ) * w).im ≤ 0 := by
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact mul_nonpos_of_nonneg_of_nonpos hc hw

theorem stable_of_im_ratio_nonpos {f g : ℝ[X]}
    (hf₀ : f ≠ 0) (hfs : f.Splits)
    (hratio : ∀ z : ℂ, 0 < z.im →
      ((complexify g).eval z / (complexify f).eval z).im ≤ 0) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) := by
  intro z hz hroot
  have hfz : (complexify f).eval z ≠ 0 :=
    eval_complexify_ne_zero_of_splits_of_im_pos hfs hf₀ hz
  have hI := ratio_eq_I_of_hermiteBiehler_root hroot hfz
  have hle := hratio z hz
  rw [hI, Complex.I_im] at hle
  norm_num at hle

private theorem im_ratio_deg1_deg1 (f g : ℝ[X]) (z : ℂ) (hz : 0 < z.im)
    (hfs : f.Splits) (hgs : g.Splits) (hlf : 0 < f.leadingCoeff) (hlg : 0 < g.leadingCoeff)
    (s r : ℝ) (hfr : f.roots = {s}) (hgr : g.roots = {r}) (hrs : r ≤ s) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  rw [eval_complexify_eq_prod hgs, eval_complexify_eq_prod hfs, hfr, hgr]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  rw [mul_div_mul_comm, ← Complex.ofReal_div]
  refine im_real_mul_nonpos _ _ ?_ (im_ratio_sub_real_nonpos z r s hz hrs)
  exact le_of_lt (div_pos hlg hlf)

private theorem im_ratio_deg1_deg0 (f g : ℝ[X]) (z : ℂ) (hz : 0 < z.im)
    (hfs : f.Splits) (hgs : g.Splits) (hlf : 0 < f.leadingCoeff) (hlg : 0 < g.leadingCoeff)
    (s : ℝ) (hfr : f.roots = {s}) (hgr : g.roots = 0) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  rw [eval_complexify_eq_prod hgs, eval_complexify_eq_prod hfs, hfr, hgr]
  simp only [Multiset.map_singleton, Multiset.prod_singleton, Multiset.map_zero,
    Multiset.prod_zero, mul_one]
  have h_div : (g.leadingCoeff : ℂ) / ((f.leadingCoeff : ℂ) * (z - (s : ℂ)))
      = ((g.leadingCoeff / f.leadingCoeff : ℝ) : ℂ) * (1 / (z - (s : ℂ))) := by
    have : (f.leadingCoeff : ℂ) ≠ 0 := by simp [hlf.ne']
    push_cast; field_simp
  rw [h_div]
  refine im_real_mul_nonpos _ _ ?_ (le_of_lt (inv_sub_real_im_neg s hz))
  exact le_of_lt (div_pos hlg hlf)

private theorem prec_roots_deg1 (f g : ℝ[X]) (hpq : Prec g f) (hd : f.natDegree = 1) :
    g.roots = 0 ∨ ∃ r s, f.roots = {s} ∧ g.roots = {r} ∧ r ≤ s := by
  obtain ⟨⟨hg₀, hgs⟩, ⟨hf₀, hfs⟩, ss, rs, hss, hrs, hsseq, hrseq, hshape⟩ := hpq
  have hfcard : f.roots.card = 1 := by rw [card_roots_of_splits hfs, hd]
  have hrslen : rs.length = 1 := by
    have : (rs : Multiset ℝ).card = 1 := by simp [*]
    simpa using this
  obtain ⟨s, hfr⟩ := Multiset.card_eq_one.mp hfcard
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · simp_all
  · right
    obtain ⟨r, h_ss_r⟩ := List.length_eq_one_iff.mp (by simp [*] : ss.length = 1)
    obtain ⟨s', h_rs_r⟩ := List.length_eq_one_iff.mp hrslen
    have h_s's : s' = s := by simp_all
    refine ⟨r, s, hfr, by simp_all, ?_⟩
    rw [h_ss_r, h_rs_r, h_s's] at halt
    simp only [ListAlternates] at halt
    simp [*]

theorem hermiteBiehlerForwardPos_of_natDegree_le_one {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (hpq : Prec g f)
    (hd : f.natDegree ≤ 1) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) := by
  obtain ⟨⟨hg₀, hgs⟩, ⟨hf₀, hfs⟩, _⟩ := id hpq
  unfold HasPosLeadingCoeff at hf hg
  rcases Nat.lt_or_ge f.natDegree 1 with hlt | hge
  · have hd₀ : f.natDegree = 0 := by lia
    have hgr : g.roots = 0 := by
      obtain ⟨_, _, ss, rs, _, _, hsseq, hrseq, hshape⟩ := hpq
      have hfcard : f.roots.card = 0 := by rw [card_roots_of_splits hfs, hd₀]
      simp_all
    intro z hz hroot
    rw [eval_hermiteBiehlerPolynomial, eval_complexify_eq_prod hfs, eval_complexify_eq_prod hgs,
      hgr] at hroot
    have hfr : f.roots = 0 := by rw [← Multiset.card_eq_zero, card_roots_of_splits hfs, hd₀]
    rw [hfr] at hroot
    simp only [Multiset.map_zero, Multiset.prod_zero, mul_one] at hroot
    have h_im :
        (((f.leadingCoeff : ℂ)) + Complex.I * (g.leadingCoeff : ℂ)).im = 0 := by
      simp [*]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_add] at h_im
    simp_all
  · have hd₁ : f.natDegree = 1 := by lia
    apply stable_of_im_ratio_nonpos hf₀ hfs
    intro z hz
    rcases prec_roots_deg1 f g hpq hd₁ with hgr | ⟨r, s, hfr, hgr, hrs⟩
    · obtain ⟨s, hfr⟩ := Multiset.card_eq_one.mp (by rw [card_roots_of_splits hfs, hd₁])
      exact im_ratio_deg1_deg0 f g z hz hfs hgs hf hg s hfr hgr
    · exact im_ratio_deg1_deg1 f g z hz hfs hgs hf hg s r hfr hgr hrs

theorem im_partialfraction_nonpos {f g : ℝ[X]} (z : ℂ) (hz : 0 < z.im) (c₀ : ℝ)
    (residue : ℝ → ℝ) (hres : ∀ s ∈ f.roots, 0 ≤ residue s)
    (h_id : (complexify g).eval z / (complexify f).eval z
        = (c₀ : ℂ) + (f.roots.map (fun s => (residue s : ℂ) / (z - (s : ℂ)))).sum) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  rw [h_id, Complex.add_im, Complex.ofReal_im, zero_add, multiset_sum_im, Multiset.map_map]
  apply multiset_sum_nonpos
  intro y hy
  simp only [Multiset.mem_map] at hy
  obtain ⟨s, hsf, rfl⟩ := hy
  simp only [Function.comp_apply]
  have h_div :
      (residue s : ℂ) / (z - (s : ℂ)) =
        (residue s : ℂ) * (1 / (z - (s : ℂ))) := by
    ring
  rw [h_div]
  exact im_real_mul_nonpos (residue s) _ (hres s hsf) (le_of_lt (inv_sub_real_im_neg s hz))

private theorem finset_sum_eq_multiset_map_sum (M : Multiset ℝ) (hnd : M.Nodup)
    (h : ℝ → ℂ) :
    ∑ s ∈ M.toFinset, h s = (M.map h).sum := by
  rw [Finset.sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]

private theorem finset_sum_div (s : Finset ℝ) (h : ℝ → ℂ) (c : ℂ) :
    (∑ x ∈ s, h x) / c = ∑ x ∈ s, h x / c := by
  rw [Finset.sum_div]

theorem eval_complexify_divByMonic {f : ℝ[X]} {s : ℝ} (hs : f.IsRoot s) {z : ℂ}
    (hzs : z - (s : ℂ) ≠ 0) :
    (complexify (f /ₘ (X - C s))).eval z = (complexify f).eval z / (z - (s : ℂ)) := by
  have : complexify f = (X - C (s : ℂ)) * complexify (f /ₘ (X - C s)) := by
    nth_rw 1 [← mul_divByMonic_eq_iff_isRoot.mpr hs]
    simp [complexify]
  simp [this, hzs]

theorem complexify_ratio_eq_partialfraction {f g : ℝ[X]} (hfs : f.Splits) (hnd : f.roots.Nodup)
    (h_deg₁ : 1 ≤ f.natDegree) (hgdeg : g.degree < f.natDegree)
    {z : ℂ} (hz : 0 < z.im) :
    (complexify g).eval z / (complexify f).eval z
      = (f.roots.map
          (fun s ↦ ((g.eval s / f.derivative.eval s : ℝ) : ℂ) / (z - (s : ℂ)))).sum := by
  have hf₀ : f ≠ 0 := by
    rintro rfl
    simp at h_deg₁
  have hfz : (complexify f).eval z ≠ 0 := eval_complexify_ne_zero_of_splits_of_im_pos hfs hf₀ hz
  have h_gi : complexify g = complexify (lagInterp f g) := by
    rw [lagInterp_eq_g hfs hnd h_deg₁ hgdeg]
  have h_ev : (complexify (lagInterp f g)).eval z
      = ∑ s ∈ f.roots.toFinset, ((g.eval s / f.derivative.eval s : ℝ) : ℂ) *
          (complexify (f /ₘ (X - C s))).eval z := by
    unfold lagInterp complexify
    rw [Polynomial.map_sum, eval_finsetSum]
    simp
  rw [h_gi, h_ev, finset_sum_div, ← finset_sum_eq_multiset_map_sum f.roots hnd]
  apply Finset.sum_congr rfl
  intro s hs
  have h_s_root : f.IsRoot s := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hs)
  have h_zs : z - (s : ℂ) ≠ 0 := by
    intro heq
    rw [sub_eq_zero] at heq
    simp_all
  rw [eval_complexify_divByMonic h_s_root h_zs]
  field_simp [hfz, h_zs]

theorem im_ratio_nonpos_of_distinct {f g : ℝ[X]} (hpq : Prec g f)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff)
    (hfnd : f.roots.Nodup) (hgnd : g.roots.Nodup)
    (hno_common : ∀ s ∈ f.roots, s ∉ g.roots)
    (h_deg₁ : 1 ≤ f.natDegree) (hgdeg : g.degree < f.natDegree)
    {z : ℂ} (hz : 0 < z.im) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  obtain ⟨-, ⟨-, hfs⟩, -⟩ := id hpq
  apply im_partialfraction_nonpos z hz 0 (fun s => g.eval s / f.derivative.eval s)
  · intro s hsf
    exact residue_nonneg hpq hflc hglc hfnd hgnd s hsf (hno_common s hsf)
  · rw [complexify_ratio_eq_partialfraction hfs hfnd h_deg₁ hgdeg hz]
    simp

theorem im_ratio_nonpos_of_distinct_eqdeg {f g : ℝ[X]} (hpq : Prec g f)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff)
    (hfnd : f.roots.Nodup) (hgnd : g.roots.Nodup)
    (hno_common : ∀ s ∈ f.roots, s ∉ g.roots)
    (h_deg₁ : 1 ≤ f.natDegree) (hgdeg : g.natDegree = f.natDegree)
    {z : ℂ} (hz : 0 < z.im) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  obtain ⟨⟨hg₀, -⟩, ⟨hf₀, hfs⟩, -⟩ := id hpq
  set c₀ := g.leadingCoeff / f.leadingCoeff with hc₀
  set g' := g - C c₀ * f with hg'
  have hg'deg : g'.degree < f.natDegree := degree_sub_c₀_mul_lt hf₀ hg₀ hgdeg hflc
  have hg'eval : ∀ s ∈ f.roots, g'.eval s = g.eval s := by simp [*]
  have hfz : (complexify f).eval z ≠ 0 := eval_complexify_ne_zero_of_splits_of_im_pos hfs hf₀ hz
  have hpf : (complexify g').eval z / (complexify f).eval z
      = (f.roots.map (fun s ↦
          ((g.eval s / f.derivative.eval s : ℝ) : ℂ) / (z - (s : ℂ)))).sum := by
    rw [complexify_ratio_eq_partialfraction hfs hfnd h_deg₁ hg'deg hz]
    congr 1
    apply Multiset.map_congr rfl
    simp_all
  have hgsplit : (complexify g).eval z
      = (complexify g').eval z + (c₀ : ℂ) * (complexify f).eval z := by
    rw [hg']
    unfold complexify
    simp
  have hid : (complexify g).eval z / (complexify f).eval z
      = (c₀ : ℂ) + (f.roots.map (fun s ↦
          ((g.eval s / f.derivative.eval s : ℝ) : ℂ) / (z - (s : ℂ)))).sum := by
    rw [hgsplit, add_div, mul_div_assoc, div_self hfz, mul_one, add_comm, hpf]
  exact im_partialfraction_nonpos z hz c₀ (fun s => g.eval s / f.derivative.eval s)
    (fun s hsf => residue_nonneg hpq hflc hglc hfnd hgnd s hsf (hno_common s hsf)) hid

theorem im_ratio_nonpos {f g : ℝ[X]} (hpq : Prec g f)
    (hflc : 0 < f.leadingCoeff) (hglc : 0 < g.leadingCoeff)
    (hfnd : f.roots.Nodup) (hgnd : g.roots.Nodup)
    (hno_common : ∀ s ∈ f.roots, s ∉ g.roots)
    (h_deg₁ : 1 ≤ f.natDegree)
    {z : ℂ} (hz : 0 < z.im) :
    ((complexify g).eval z / (complexify f).eval z).im ≤ 0 := by
  obtain ⟨⟨hg₀, hgs⟩, ⟨-, hfs⟩, ss, rs, -, -, hsseq, hrseq, hshape⟩ := id hpq
  have hgc : g.roots.card = g.natDegree := card_roots_of_splits hgs
  have hfc : f.roots.card = f.natDegree := card_roots_of_splits hfs
  rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩
  · have hdd : g.natDegree + 1 = f.natDegree := by
      rw [← hgc, ← hfc, ← hsseq, ← hrseq]
      simpa using hlen
    have hgdeg : g.degree < f.natDegree := by
      rw [degree_eq_natDegree hg₀]
      exact_mod_cast by lia
    exact im_ratio_nonpos_of_distinct hpq hflc hglc hfnd hgnd hno_common h_deg₁ hgdeg hz
  · have heq : g.natDegree = f.natDegree := by
      rw [← hgc, ← hfc, ← hsseq, ← hrseq]
      simpa using hlen
    exact im_ratio_nonpos_of_distinct_eqdeg hpq hflc hglc hfnd hgnd hno_common h_deg₁ heq hz

theorem hermiteBiehlerForwardPos_of_distinct {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (hpq : Prec g f)
    (hfnd : f.roots.Nodup) (hgnd : g.roots.Nodup)
    (hno_common : ∀ s ∈ f.roots, s ∉ g.roots) (h_deg₁ : 1 ≤ f.natDegree) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) := by
  obtain ⟨-, ⟨hf₀, hfs⟩, -⟩ := id hpq
  unfold HasPosLeadingCoeff at hf hg
  apply stable_of_im_ratio_nonpos hf₀ hfs
  intro z hz
  exact im_ratio_nonpos hpq hf hg hfnd hgnd hno_common h_deg₁ hz

theorem hermiteBiehlerPolynomial_factor_common_root {f g : ℝ[X]} {r : ℝ}
    (hrf : f.IsRoot r) (hrg : g.IsRoot r) :
    hermiteBiehlerPolynomial f g
      = (X - C (r : ℂ)) * hermiteBiehlerPolynomial (f /ₘ (X - C r)) (g /ₘ (X - C r)) := by
  have hff : f = (X - C r) * (f /ₘ (X - C r)) := (mul_divByMonic_eq_iff_isRoot.mpr hrf).symm
  have hgg : g = (X - C r) * (g /ₘ (X - C r)) := (mul_divByMonic_eq_iff_isRoot.mpr hrg).symm
  unfold hermiteBiehlerPolynomial complexify
  have hcf : (f.map Complex.ofRealHom)
      = (X - C (r : ℂ)) * ((f /ₘ (X - C r)).map Complex.ofRealHom) := by
    conv_lhs => rw [hff]
    simp
  have hcg : (g.map Complex.ofRealHom)
      = (X - C (r : ℂ)) * ((g /ₘ (X - C r)).map Complex.ofRealHom) := by
    conv_lhs => rw [hgg]
    simp
  rw [hcf, hcg]
  ring

theorem isUpperHalfPlaneStable_of_cofactor {f g : ℝ[X]} {r : ℝ}
    (hrf : f.IsRoot r) (hrg : g.IsRoot r)
    (hcof : IsUpperHalfPlaneStable
      (hermiteBiehlerPolynomial (f /ₘ (X - C r)) (g /ₘ (X - C r)))) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) := by
  rw [hermiteBiehlerPolynomial_factor_common_root hrf hrg]
  apply IsUpperHalfPlaneStable.mul ?_ hcof
  intro z hz
  simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
  intro h
  exact hz.ne' (by simpa using congrArg Complex.im h)

/-- Sign-normalized forward Hermite--Biehler bridge.

This is the minimal sign-stable form used in downstream plumbing:
positive leading coefficients on both inputs prevent the false counterexample.
-/
abbrev hermiteBiehlerForwardPosStatement : Prop :=
  ∀ {f g : ℝ[X]},
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    Prec g f →
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)

theorem hermiteBiehlerForwardPos_general {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (hpq : Prec g f) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) := by
  generalize hn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f g with
  | _ n ih =>
    subst hn
    by_cases h_deg_le : f.natDegree ≤ 1
    · exact hermiteBiehlerForwardPos_of_natDegree_le_one hf hg hpq h_deg_le
    · push Not at h_deg_le
      have h_deg₁ : 1 ≤ f.natDegree := by lia
      by_cases hcom : ∃ r, r ∈ f.roots ∧ r ∈ g.roots
      · obtain ⟨r, hrf, hrg⟩ := hcom
        have hrfroot : f.IsRoot r := isRoot_of_mem_roots hrf
        have hrgroot : g.IsRoot r := isRoot_of_mem_roots hrg
        apply isUpperHalfPlaneStable_of_cofactor hrfroot hrgroot
        have hf₁deg : (f /ₘ (X - C r)).natDegree < f.natDegree := by
          rw [natDegree_divByMonic f (monic_X_sub_C r), natDegree_X_sub_C]
          lia
        have hpq₁ : Prec (g /ₘ (X - C r)) (f /ₘ (X - C r)) :=
          prec_cofactor_of_common_root hpq hrfroot hrgroot
        have hf₁ : HasPosLeadingCoeff (f /ₘ (X - C r)) := by
          unfold HasPosLeadingCoeff at hf ⊢
          rw [leadingCoeff_divByMonic_X_sub_C hrfroot]
          exact hf
        have hg₁ : HasPosLeadingCoeff (g /ₘ (X - C r)) := by
          unfold HasPosLeadingCoeff at hg ⊢
          rw [leadingCoeff_divByMonic_X_sub_C hrgroot]
          exact hg
        exact ih (f /ₘ (X - C r)).natDegree hf₁deg hf₁ hg₁ hpq₁ rfl
      · push Not at hcom
        have hfnd : f.roots.Nodup := by
          by_contra hnd
          obtain ⟨r, hrf, hrg⟩ := exists_common_root_of_not_nodup hpq hnd
          simp_all
        have hgnd : g.roots.Nodup := by
          by_contra hnd
          obtain ⟨r, hrf, hrg⟩ := exists_common_root_of_not_nodup_g hpq hnd
          simp_all
        exact hermiteBiehlerForwardPos_of_distinct hf hg hpq hfnd hgnd
          (fun s hsf hsg ↦ hcom s hsf hsg) h_deg₁

theorem hermiteBiehlerForwardPos {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g) (h : Prec g f) :
    IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g) :=
  hermiteBiehlerForwardPos_general hf hg h

lemma hasPosLeadingCoeff_of_nonnegCoeffs_of_ne_zero {p : ℝ[X]}
    (hpnn : HasNonnegCoeffs p) (hp₀ : p ≠ 0) :
    HasPosLeadingCoeff p :=
  lt_of_le_of_ne (hpnn p.natDegree) (Ne.symm (leadingCoeff_ne_zero.mpr hp₀))

/-- Concrete obstruction to a sign-free forward Hermite--Biehler route:
`X - i` has the upper-half-plane root `i`. -/
theorem not_isUpperHalfPlaneStable_hermiteBiehlerPolynomial_X_neg_one :
    ¬ IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (X : ℝ[X]) (-(1 : ℝ[X]))) :=
  fun h => h Complex.I (by simp) (by simp [hermiteBiehlerPolynomial, complexify])

end RealRooted
