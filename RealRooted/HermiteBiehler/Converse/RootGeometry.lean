import RealRooted.HermiteBiehler.ConverseLowDegree
import RealRooted.HermiteBiehler.Forward
import Mathlib.Data.Complex.Basic

/-!
# Root geometry for the converse Hermite--Biehler theorem

This file proves that stability of the Hermite--Biehler polynomial forces both
real component polynomials to split. The proof compares conjugated root-product
norms and excludes nonreal roots of either component.
-/

open Polynomial

noncomputable section

namespace RealRooted

lemma norm_conj_sub_le {z w : ℂ} (hz : 0 < z.im) (hw : w.im ≤ 0) :
    ‖(starRingEnd ℂ) z - w‖ ≤ ‖z - w‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  apply Real.sqrt_le_sqrt
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  nlinarith

lemma norm_conj_sub_lt {z w : ℂ} (hz : 0 < z.im) (hw : w.im < 0) :
    ‖(starRingEnd ℂ) z - w‖ < ‖z - w‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  apply Real.sqrt_lt_sqrt (by positivity)
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  nlinarith

lemma multiset_prod_norm_conj_le {z : ℂ} (hz : 0 < z.im) (S : Multiset ℂ)
    (hS : ∀ w ∈ S, w.im ≤ 0) :
    ‖(S.map fun w => (starRingEnd ℂ) z - w).prod‖ ≤ ‖(S.map fun w => z - w).prod‖ := by
  induction S using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    have ha := hS a (Multiset.mem_cons_self a s)
    have hs : ∀ w ∈ s, w.im ≤ 0 := fun w hw => hS w (Multiset.mem_cons_of_mem hw)
    exact mul_le_mul (norm_conj_sub_le hz ha) (ih hs) (norm_nonneg _) (norm_nonneg _)

lemma multiset_prod_norm_conj_lt {z : ℂ} (hz : 0 < z.im) (S : Multiset ℂ)
    (hS : ∀ w ∈ S, w.im ≤ 0) {w₀ : ℂ} (hw₀ : w₀ ∈ S) (hneg : w₀.im < 0) :
    ‖(S.map fun w => (starRingEnd ℂ) z - w).prod‖ < ‖(S.map fun w => z - w).prod‖ := by
  obtain ⟨T, rfl⟩ : ∃ T, S = w₀ ::ₘ T :=
    ⟨S.erase w₀, (Multiset.cons_erase hw₀).symm⟩
  have hT : ∀ w ∈ T, w.im ≤ 0 := fun w hw => hS w (Multiset.mem_cons_of_mem hw)
  have hpos : 0 < ‖(T.map fun w => z - w).prod‖ := by
    rw [norm_pos_iff]
    refine Multiset.prod_ne_zero fun h => ?_
    obtain ⟨w, hw, hzw⟩ := Multiset.mem_map.1 h
    exact absurd (hT w hw) (by simp [sub_eq_zero.1 hzw] at hz ⊢; linarith)
  simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
  have h1 := norm_conj_sub_lt hz hneg
  have h2 := multiset_prod_norm_conj_le hz T hT
  nlinarith [norm_nonneg ((T.map fun w => (starRingEnd ℂ) z - w).prod),
    norm_nonneg ((starRingEnd ℂ) z - w₀)]

lemma eval_eq_prod_roots_complex (p : ℂ[X]) (x : ℂ) :
    p.eval x = p.leadingCoeff * (p.roots.map fun a => x - a).prod :=
  (IsAlgClosed.splits p).eval_eq_prod_roots x

lemma roots_real_of_stable_norm_eq {p : ℂ[X]} (hp : p ≠ 0)
    (hstab : IsUpperHalfPlaneStable p) {z : ℂ} (hz : 0 < z.im)
    (heq : ‖p.eval ((starRingEnd ℂ) z)‖ = ‖p.eval z‖) :
    ∀ w ∈ p.roots, w.im = 0 := by
  intro w₀ hw₀
  by_contra hne
  have hle : ∀ w ∈ p.roots, w.im ≤ 0 := fun w hw =>
    im_nonpos_of_stable_root hstab (isRoot_of_mem_roots hw)
  have hneg : w₀.im < 0 := lt_of_le_of_ne (hle w₀ hw₀) hne
  have :
      ‖(p.roots.map fun w ↦ starRingEnd ℂ z - w).prod‖ <
        ‖(p.roots.map fun w ↦ z - w).prod‖ :=
    multiset_prod_norm_conj_lt hz p.roots hle hw₀ hneg
  rw [eval_eq_prod_roots_complex p, eval_eq_prod_roots_complex p, norm_mul, norm_mul] at heq
  simp_all

lemma no_upper_root_left_of_stable {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hf : HasPosLeadingCoeff f)
    {z : ℂ} (hz : 0 < z.im) (hroot : (complexify f).eval z = 0) : False := by
  set h := hermiteBiehlerPolynomial f g with hh
  have hzim : z.im ≠ 0 := hz.ne'
  have : (complexify g).eval z ≠ 0 := fun hg₀ ↦
    no_common_nonreal_root_of_stable hstab hzim hroot hg₀
  have : h.eval z = Complex.I * (complexify g).eval z := by simp [*]
  have hhz : h.eval z ≠ 0 := by simp [*]
  have hne : h ≠ 0 := fun h_zero ↦ hhz (by rw [h_zero, eval_zero])
  have : h.eval ((starRingEnd ℂ) z) =
      Complex.I * (starRingEnd ℂ) ((complexify g).eval z) := by
    rw [hh, eval_hermiteBiehlerPolynomial, eval_complexify_conj, eval_complexify_conj,
      hroot, map_zero, zero_add]
  have heq : ‖h.eval ((starRingEnd ℂ) z)‖ = ‖h.eval z‖ := by simp_all
  have hroots : ∀ w ∈ h.roots, w.im = 0 :=
    roots_real_of_stable_norm_eq hne hstab hz heq
  set P : ℂ[X] := (h.roots.map fun r ↦ X - C r).prod with hP
  have hfac : h = C h.leadingCoeff * P := (IsAlgClosed.splits (k := ℂ) h).eq_prod_roots
  have hevalh : h.eval z = h.leadingCoeff * P.eval z := by
    conv_lhs => rw [hfac]
    simp
  have hevalhc : (h.map (starRingEnd ℂ)).eval z =
      (starRingEnd ℂ) h.leadingCoeff * P.eval z := by
    rw [map_conj_of_roots_real hroots, eval_mul, eval_C]
  have hsum : h + h.map (starRingEnd ℂ) = 2 * complexify f := by
    rw [hh, hermiteBiehler_map_conj, hermiteBiehlerPolynomial]
    ring
  have hzero : (h.leadingCoeff + (starRingEnd ℂ) h.leadingCoeff) * P.eval z = 0 := by
    have hev := congrArg (fun q : ℂ[X] ↦ q.eval z) hsum
    simp only [eval_add, eval_mul, eval_ofNat] at hev
    rw [hroot, mul_zero, hevalh, hevalhc] at hev
    rw [add_mul]
    exact hev
  have hPz : P.eval z ≠ 0 := by
    intro hP₀
    apply hhz
    rw [hevalh, hP₀, mul_zero]
  have hlceq : (starRingEnd ℂ) h.leadingCoeff = -h.leadingCoeff := by
    rcases mul_eq_zero.mp hzero with hc | hc
    · exact eq_neg_of_add_eq_zero_right hc
    · exact absurd hc hPz
  have hmapneg := map_conj_neg_of_roots_real hlceq hroots
  rw [hh] at hmapneg
  have hf₀ : f = 0 := f_eq_zero_of_hermiteBiehler_map_conj_neg hmapneg
  simp_all

lemma no_upper_root_right_of_stable {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    (hg : HasPosLeadingCoeff g)
    {z : ℂ} (hz : 0 < z.im) (hroot : (complexify g).eval z = 0) : False := by
  set h := hermiteBiehlerPolynomial f g with hh
  have hzim : z.im ≠ 0 := hz.ne'
  have : (complexify f).eval z ≠ 0 := fun hf₀ ↦
    no_common_nonreal_root_of_stable hstab hzim hf₀ hroot
  have : h.eval z = (complexify f).eval z := by simp [*]
  have hhz : h.eval z ≠ 0 := by simp [*]
  have hne : h ≠ 0 := fun h_zero ↦ hhz (by rw [h_zero, eval_zero])
  have : h.eval ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((complexify f).eval z) := by
    rw [hh, eval_hermiteBiehlerPolynomial, eval_complexify_conj, eval_complexify_conj,
      hroot, map_zero, mul_zero, add_zero]
  have heq : ‖h.eval ((starRingEnd ℂ) z)‖ = ‖h.eval z‖ := by simp_all
  have hroots : ∀ w ∈ h.roots, w.im = 0 :=
    roots_real_of_stable_norm_eq hne hstab hz heq
  set P : ℂ[X] := (h.roots.map fun r ↦ X - C r).prod with hP
  have hfac : h = C h.leadingCoeff * P := (IsAlgClosed.splits (k := ℂ) h).eq_prod_roots
  have hevalh : h.eval z = h.leadingCoeff * P.eval z := by
    conv_lhs => rw [hfac]
    simp
  have hevalhc : (h.map (starRingEnd ℂ)).eval z =
      (starRingEnd ℂ) h.leadingCoeff * P.eval z := by
    rw [map_conj_of_roots_real hroots, eval_mul, eval_C]
  have hdiff : h - h.map (starRingEnd ℂ) = 2 * C Complex.I * complexify g := by
    rw [hh, hermiteBiehler_map_conj, hermiteBiehlerPolynomial]
    ring
  have hzero : (h.leadingCoeff - (starRingEnd ℂ) h.leadingCoeff) * P.eval z = 0 := by
    have hev := congrArg (fun q : ℂ[X] ↦ q.eval z) hdiff
    simp only [eval_sub, eval_mul, eval_ofNat, eval_C] at hev
    rw [hroot, mul_zero, hevalh, hevalhc] at hev
    rw [sub_mul]
    exact hev
  have hPz : P.eval z ≠ 0 := by
    intro hP₀
    apply hhz
    rw [hevalh, hP₀, mul_zero]
  have hlceq : (starRingEnd ℂ) h.leadingCoeff = h.leadingCoeff := by
    rcases mul_eq_zero.mp hzero with hc | hc
    · exact (sub_eq_zero.mp hc).symm
    · exact absurd hc hPz
  have hmapself := map_conj_self_of_roots_real hlceq hroots
  rw [hh] at hmapself
  have hg₀ : g = 0 := g_eq_zero_of_hermiteBiehler_map_conj_self hmapself
  simp_all

theorem splits_of_stable {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    f.Splits ∧ g.Splits := by
  constructor
  · apply Polynomial.splits_of_all_roots_real
    intro z hz
    by_contra him
    rcases lt_or_gt_of_ne him with hlt | hgt
    · exact no_upper_root_left_of_stable hstab hf (by simp [*]) (complexify_conj_root hz)
    · exact no_upper_root_left_of_stable hstab hf hgt hz
  · apply Polynomial.splits_of_all_roots_real
    intro z hz
    by_contra him
    rcases lt_or_gt_of_ne him with hlt | hgt
    · exact no_upper_root_right_of_stable hstab hg (by simp [*]) (complexify_conj_root hz)
    · exact no_upper_root_right_of_stable hstab hg hgt hz

end RealRooted
