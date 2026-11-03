module

import Mathlib.Analysis.Complex.Polynomial.Basic
import RealRooted.HermiteBiehler.Forward
public import RealRooted.MaWang
public import RealRooted.HermiteBiehler.Basic
public import RealRooted.Basic.ProperPosition

/-!
# Degree shape of stable Hermite--Biehler pairs

This file proves the degree-shape bounds for a pair `f, g` with positive leading
coefficients and `f + i g` upper-half-plane stable, together with the conjugation
and root-sum lemmas used to derive them.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

theorem eval_hermiteBiehler_neg_conj (f g : ℝ[X]) (z : ℂ) :
    (hermiteBiehlerPolynomial f (-g)).eval (starRingEnd ℂ z)
      = starRingEnd ℂ ((hermiteBiehlerPolynomial f g).eval z) := by
  simp [hermiteBiehlerPolynomial, eval_complexify_conj]
  simp [complexify]

theorem no_common_nonreal_root_of_stable {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g))
    {z : ℂ} (hzim : z.im ≠ 0)
    (hf : (complexify f).eval z = 0) (hg : (complexify g).eval z = 0) : False := by
  rcases lt_or_gt_of_ne hzim with hneg | hpos
  · have hcf : (complexify f).eval (starRingEnd ℂ z) = 0 := complexify_conj_root hf
    have hcg : (complexify g).eval (starRingEnd ℂ z) = 0 := complexify_conj_root hg
    have : 0 < (starRingEnd ℂ z).im := by simp [*]
    apply hstab (starRingEnd ℂ z) this
    simp [*]
  · apply hstab z hpos
    simp [*]

lemma hermiteBiehler_coeff (f g : ℝ[X]) (n : ℕ) :
    (hermiteBiehlerPolynomial f g).coeff n
      = (f.coeff n : ℂ) + Complex.I * (g.coeff n : ℂ) := by
  simp [hermiteBiehlerPolynomial, complexify, coeff_map, mul_comm]

lemma im_nonpos_of_stable_root {p : ℂ[X]} (hstab : IsUpperHalfPlaneStable p)
    {w : ℂ} (hw : p.eval w = 0) : w.im ≤ 0 := by
  by_contra h
  exact hstab w (not_le.mp h) hw

private lemma hermiteBiehler_natDegree_of_coeff_ne_zero {f g : ℝ[X]} {d : ℕ}
    (hfd : f.natDegree = d) (hgd : g.natDegree = d)
    (hne : (f.coeff d : ℂ) + Complex.I * (g.coeff d : ℂ) ≠ 0) :
    (hermiteBiehlerPolynomial f g).natDegree = d ∧
      (hermiteBiehlerPolynomial f g).coeff d =
        (f.coeff d : ℂ) + Complex.I * (g.coeff d : ℂ) := by
  have hcoeff := hermiteBiehler_coeff f g d
  refine ⟨le_antisymm ?_ (le_natDegree_of_ne_zero (hcoeff.symm ▸ hne)), hcoeff⟩
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [hermiteBiehler_coeff, coeff_eq_zero_of_natDegree_lt (hfd.symm ▸ hn),
    coeff_eq_zero_of_natDegree_lt (hgd.symm ▸ hn)]
  simp

lemma hermiteBiehler_natDegree_of_posLead {f g : ℝ[X]} {d : ℕ}
    (hf : 0 < f.coeff d) (hfd : f.natDegree = d) (hgd : g.natDegree = d) :
    (hermiteBiehlerPolynomial f g).natDegree = d ∧
      (hermiteBiehlerPolynomial f g).coeff d
        = (f.coeff d : ℂ) + Complex.I * (g.coeff d : ℂ) := by
  apply hermiteBiehler_natDegree_of_coeff_ne_zero hfd hgd
  intro h
  apply hf.ne'
  simpa using congrArg Complex.re h

theorem hermiteBiehler_map_conj (f g : ℝ[X]) :
    (hermiteBiehlerPolynomial f g).map (starRingEnd ℂ)
      = complexify f - C Complex.I * complexify g := by
  have hcf : ∀ p : ℝ[X], (complexify p).map (starRingEnd ℂ) = complexify p := by
    intro p
    simp only [complexify, Polynomial.map_map]
    congr 1
    ext x
    simp
  simp only [hermiteBiehlerPolynomial, Polynomial.map_add, Polynomial.map_mul, map_C,
    Complex.conj_I, hcf, C_neg]
  ring

theorem map_conj_of_roots_real {p : ℂ[X]} (hroots : ∀ z ∈ p.roots, z.im = 0) :
    p.map (starRingEnd ℂ)
      = C ((starRingEnd ℂ) p.leadingCoeff) * (p.roots.map fun r => X - C r).prod := by
  have hsplits : p.Splits := IsAlgClosed.splits _
  conv_lhs => rw [hsplits.eq_prod_roots]
  rw [Polynomial.map_mul, map_C, Polynomial.map_multiset_prod, Multiset.map_map]
  congr 1
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun r hr => ?_)
  simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C]
  rw [Complex.conj_eq_iff_im.mpr (hroots r hr)]

theorem map_conj_self_of_roots_real {p : ℂ[X]}
    (hlc : (starRingEnd ℂ) p.leadingCoeff = p.leadingCoeff)
    (hroots : ∀ z ∈ p.roots, z.im = 0) :
    p.map (starRingEnd ℂ) = p := by
  have hsplits : p.Splits := IsAlgClosed.splits _
  rw [map_conj_of_roots_real hroots, hlc, ← hsplits.eq_prod_roots]

theorem map_conj_neg_of_roots_real {p : ℂ[X]}
    (hlc : (starRingEnd ℂ) p.leadingCoeff = -p.leadingCoeff)
    (hroots : ∀ z ∈ p.roots, z.im = 0) :
    p.map (starRingEnd ℂ) = -p := by
  have hsplits : p.Splits := IsAlgClosed.splits _
  rw [map_conj_of_roots_real hroots, hlc, map_neg, neg_mul, ← hsplits.eq_prod_roots]

theorem g_eq_zero_of_hermiteBiehler_map_conj_self {f g : ℝ[X]}
    (h : (hermiteBiehlerPolynomial f g).map (starRingEnd ℂ) = hermiteBiehlerPolynomial f g) :
    g = 0 := by
  rw [hermiteBiehler_map_conj, hermiteBiehlerPolynomial, sub_eq_add_neg] at h
  have h_cg : complexify g = 0 := by
    have h_neg : -(C Complex.I * complexify g) = C Complex.I * complexify g := add_left_cancel h
    rw [CharZero.neg_eq_self_iff, mul_eq_zero, C_eq_zero] at h_neg
    simpa using h_neg
  simpa [complexify] using h_cg

theorem f_eq_zero_of_hermiteBiehler_map_conj_neg {f g : ℝ[X]}
    (h : (hermiteBiehlerPolynomial f g).map (starRingEnd ℂ) = -hermiteBiehlerPolynomial f g) :
    f = 0 := by
  rw [hermiteBiehler_map_conj, hermiteBiehlerPolynomial, neg_add] at h
  have h_cf : complexify f = 0 := by
    have h_eq : complexify f = - complexify f := add_right_cancel h
    rwa [CharZero.eq_neg_self_iff] at h_eq
  simpa [complexify] using h_cf

lemma hermiteBiehler_natDegree_of_left_dominant {f g : ℝ[X]} (hf : f ≠ 0)
    (h : g.natDegree < f.natDegree) :
    (hermiteBiehlerPolynomial f g).natDegree = f.natDegree ∧
      (hermiteBiehlerPolynomial f g).leadingCoeff = (f.leadingCoeff : ℂ) := by
  have hcd : (hermiteBiehlerPolynomial f g).coeff f.natDegree = (f.leadingCoeff : ℂ) := by
    rw [hermiteBiehler_coeff, coeff_eq_zero_of_natDegree_lt h]
    simp [coeff_natDegree]
  have hdeg : (hermiteBiehlerPolynomial f g).natDegree = f.natDegree := by
    apply le_antisymm
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      rw [hermiteBiehler_coeff, coeff_eq_zero_of_natDegree_lt hn,
        coeff_eq_zero_of_natDegree_lt (h.trans hn)]
      simp
    · exact le_natDegree_of_ne_zero (hcd.symm ▸ by simp [hf])
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hcd]⟩

lemma hermiteBiehler_natDegree_of_right_dominant {f g : ℝ[X]} (hg : g ≠ 0)
    (h : f.natDegree < g.natDegree) :
    (hermiteBiehlerPolynomial f g).natDegree = g.natDegree ∧
      (hermiteBiehlerPolynomial f g).leadingCoeff = Complex.I * (g.leadingCoeff : ℂ) := by
  have hcd : (hermiteBiehlerPolynomial f g).coeff g.natDegree
      = Complex.I * (g.leadingCoeff : ℂ) := by
    rw [hermiteBiehler_coeff, coeff_eq_zero_of_natDegree_lt h]
    simp [coeff_natDegree]
  have hdeg : (hermiteBiehlerPolynomial f g).natDegree = g.natDegree := by
    apply le_antisymm
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      rw [hermiteBiehler_coeff, coeff_eq_zero_of_natDegree_lt (h.trans hn),
        coeff_eq_zero_of_natDegree_lt hn]
      simp
    · exact le_natDegree_of_ne_zero (hcd.symm ▸ by simp [hg])
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hcd]⟩

theorem roots_real_of_stable_sum_im_zero {p : ℂ[X]} (hstab : IsUpperHalfPlaneStable p)
    (hsum : p.roots.sum.im = 0) : ∀ z ∈ p.roots, z.im = 0 := by
  have hmap : ((p.roots.map Complex.im).sum : ℝ) = 0 := by
    rw [← multiset_sum_im]
    simp [*]
  have hnp : ∀ x ∈ p.roots.map Complex.im, x ≤ 0 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
    exact im_nonpos_of_stable_root hstab ((mem_roots'.mp hz).2)
  intro z hz
  exact multiset_sum_nonpos_eq_zero hnp hmap z.im (Multiset.mem_map_of_mem _ hz)

theorem natDegree_left_le_succ_of_stable {f g : ℝ[X]} (hf : HasPosLeadingCoeff f)
    (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    f.natDegree ≤ g.natDegree + 1 := by
  by_contra hcon
  obtain ⟨hdeg, hlead⟩ :=
    hermiteBiehler_natDegree_of_left_dominant (f := f) (g := g) hf.ne_zero (by lia)
  have hsplits : (hermiteBiehlerPolynomial f g).Splits := IsAlgClosed.splits _
  have hvieta := hsplits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have hglt : g.natDegree < f.natDegree - 1 := by lia
  have hnc : (hermiteBiehlerPolynomial f g).nextCoeff
      = ((f.coeff (f.natDegree - 1) : ℝ) : ℂ) := by
    rw [nextCoeff_of_natDegree_pos (by lia : 0 < (hermiteBiehlerPolynomial f g).natDegree),
      hdeg, hermiteBiehler_coeff, coeff_eq_zero_of_natDegree_lt hglt]
    simp
  rw [hnc, hlead] at hvieta
  have him : (hermiteBiehlerPolynomial f g).roots.sum.im = 0 := by
    have h1 := congrArg Complex.im hvieta
    simp only [Complex.ofReal_im, Complex.mul_im, Complex.neg_im,
      Complex.ofReal_re, zero_mul, add_zero, neg_mul, zero_eq_neg] at h1
    have : (0 : ℝ) < f.leadingCoeff := hf
    rcases mul_eq_zero.mp h1 with h' | h'
    · simp_all
    · simp [*]
  have hreal := roots_real_of_stable_sum_im_zero hstab him
  have hconj : (hermiteBiehlerPolynomial f g).map (starRingEnd ℂ)
      = hermiteBiehlerPolynomial f g :=
    map_conj_self_of_roots_real (by simp [*]) hreal
  exact hg.ne_zero (g_eq_zero_of_hermiteBiehler_map_conj_self hconj)

theorem natDegree_right_le_of_stable {f g : ℝ[X]} (hf : HasPosLeadingCoeff f)
    (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    g.natDegree ≤ f.natDegree := by
  by_contra hcon
  have hlt : f.natDegree < g.natDegree := by lia
  obtain ⟨hdeg, hlead⟩ := hermiteBiehler_natDegree_of_right_dominant hg.ne_zero hlt
  have hsplits : (hermiteBiehlerPolynomial f g).Splits := IsAlgClosed.splits _
  have hvieta := hsplits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have hnc : (hermiteBiehlerPolynomial f g).nextCoeff
      = ((f.coeff (g.natDegree - 1) : ℝ) : ℂ)
        + Complex.I * ((g.coeff (g.natDegree - 1) : ℝ) : ℂ) := by
    rw [nextCoeff_of_natDegree_pos (by lia : 0 < (hermiteBiehlerPolynomial f g).natDegree),
      hdeg, hermiteBiehler_coeff]
  rw [hnc, hlead] at hvieta
  have hre : f.coeff (g.natDegree - 1)
      = g.leadingCoeff * (hermiteBiehlerPolynomial f g).roots.sum.im := by
    have h1 := congrArg Complex.re hvieta
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      zero_mul, one_mul, mul_zero, zero_add, add_zero, sub_zero, zero_sub,
      neg_mul, neg_neg] at h1
    assumption
  have hsim : (hermiteBiehlerPolynomial f g).roots.sum.im ≤ 0 := by
    rw [multiset_sum_im]
    apply multiset_sum_nonpos
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
    exact im_nonpos_of_stable_root hstab ((mem_roots'.mp hz).2)
  rcases Nat.lt_or_ge (f.natDegree + 1) g.natDegree with hcase | hcase
  · have hfc : f.coeff (g.natDegree - 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by lia)
    have him : (hermiteBiehlerPolynomial f g).roots.sum.im = 0 := by
      rw [hfc] at hre
      have hg' : (0 : ℝ) < g.leadingCoeff := hg
      rcases mul_eq_zero.mp hre.symm with h' | h'
      · exact absurd h' (ne_of_gt hg')
      · exact h'
    have hreal := roots_real_of_stable_sum_im_zero hstab him
    have hconj : (hermiteBiehlerPolynomial f g).map (starRingEnd ℂ)
        = -hermiteBiehlerPolynomial f g := by
      apply map_conj_neg_of_roots_real _ hreal
      simp [*]
    exact hf.ne_zero (f_eq_zero_of_hermiteBiehler_map_conj_neg hconj)
  · have hdeq : g.natDegree - 1 = f.natDegree := by lia
    have hfc : f.coeff (g.natDegree - 1) = f.leadingCoeff := by simp [*]
    rw [hfc] at hre
    have : (0 : ℝ) < f.leadingCoeff := hf
    have : (0 : ℝ) < g.leadingCoeff := hg
    nlinarith [this, hre, hsim]

theorem natDegree_shape_of_stable {f g : ℝ[X]} (hf : HasPosLeadingCoeff f)
    (hg : HasPosLeadingCoeff g)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    g.natDegree ≤ f.natDegree ∧ f.natDegree ≤ g.natDegree + 1 :=
  ⟨natDegree_right_le_of_stable hf hg hstab,
    natDegree_left_le_succ_of_stable hf hg hstab⟩

end RealRooted
