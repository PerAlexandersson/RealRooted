import RealRooted.CommonInterleaver.SuccDegreeLowDegree
import RealRooted.HermiteBiehler.Forward
import RealRooted.Mathlib.Algebra.Polynomial.Degree.SmallDegree
import RealRooted.MaWang
import RealRooted.QuadraticRoot
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

/-!
# Low-degree converse Hermite--Biehler theorem

This file proves the converse Hermite--Biehler theorem through degree two. It
contains the quadratic and Vieta reductions, degree-shape bounds, and explicit
interlacing inequalities needed by the low-degree endpoint.
-/

open Polynomial

noncomputable section

namespace RealRooted

theorem splits_of_discrim_nonneg {a b c : ℝ} (ha : a ≠ 0)
    (h : 0 ≤ discrim a b c) :
    (C a * X ^ 2 + C b * X + C c).Splits := by
  exact quadraticPoly_splits_of_discrim_nonneg ha h

theorem eval_hermiteBiehler_neg_conj (f g : ℝ[X]) (z : ℂ) :
    (hermiteBiehlerPolynomial f (-g)).eval (starRingEnd ℂ z)
      = starRingEnd ℂ ((hermiteBiehlerPolynomial f g).eval z) := by
  simp [hermiteBiehlerPolynomial, eval_complexify_conj]
  simp [complexify]

theorem no_lower_root_hermiteBiehler_neg_of_stable {f g : ℝ[X]}
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    ∀ z : ℂ, z.im < 0 → (hermiteBiehlerPolynomial f (-g)).eval z ≠ 0 := by
  intro z hz hzero
  have hconj_im : 0 < (starRingEnd ℂ z).im := by simp [*]
  apply hstab (starRingEnd ℂ z) hconj_im
  have hthis := eval_hermiteBiehler_neg_conj f g (starRingEnd ℂ z)
  rw [Complex.conj_conj] at hthis
  rw [hthis] at hzero
  have := congrArg (starRingEnd ℂ) hzero
  rwa [Complex.conj_conj, map_zero] at this

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

lemma discrim_nonneg_of_im_nonpos
    {u₁ u₂ v₁ v₂ : ℝ} (hv₁ : v₁ ≤ 0) (hv₂ : v₂ ≤ 0) :
    0 ≤ (-(u₁ + u₂) + (v₁ + v₂)) ^ 2
      - 4 * (u₁ * u₂ - v₁ * v₂ - u₁ * v₂ - u₂ * v₁) := by
  nlinarith [sq_nonneg (u₁ - u₂ - v₁ + v₂),
    mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂]

lemma discrim_nonneg_of_im_nonpos'
    {u₁ u₂ v₁ v₂ : ℝ} (hv₁ : v₁ ≤ 0) (hv₂ : v₂ ≤ 0) :
    0 ≤ (-(u₁ + u₂) - (v₁ + v₂)) ^ 2
      - 4 * (u₁ * u₂ - v₁ * v₂ + u₁ * v₂ + u₂ * v₁) := by
  nlinarith [sq_nonneg (u₁ - u₂ + v₁ - v₂),
    mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂]

lemma hermiteBiehler_coeff (f g : ℝ[X]) (n : ℕ) :
    (hermiteBiehlerPolynomial f g).coeff n
      = (f.coeff n : ℂ) + Complex.I * (g.coeff n : ℂ) := by
  simp [hermiteBiehlerPolynomial, complexify, coeff_map, mul_comm]

lemma im_nonpos_of_stable_root {p : ℂ[X]} (hstab : IsUpperHalfPlaneStable p)
    {w : ℂ} (hw : p.eval w = 0) : w.im ≤ 0 := by
  by_contra h
  exact hstab w (not_le.mp h) hw

lemma hermiteBiehler_natDegree_of_monic {f g : ℝ[X]} {d : ℕ}
    (hf : f.Monic) (hg : g.Monic) (hfd : f.natDegree = d) (hgd : g.natDegree = d) :
    (hermiteBiehlerPolynomial f g).natDegree = d ∧
      (hermiteBiehlerPolynomial f g).coeff d = 1 + Complex.I := by
  have h_coeff : (hermiteBiehlerPolynomial f g).coeff d = 1 + Complex.I := by
    simp [hermiteBiehler_coeff, (by rw [← hfd]; exact hf : f.coeff d = 1),
      (by rw [← hgd]; exact hg : g.coeff d = 1)]
  have : (1 + Complex.I : ℂ) ≠ 0 := by
    intro h
    simpa using congrArg Complex.im h
  constructor
  · apply le_antisymm
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      rw [hermiteBiehler_coeff, coeff_eq_zero_of_natDegree_lt (hfd.symm ▸ hn),
        coeff_eq_zero_of_natDegree_lt (hgd.symm ▸ hn)]
      simp
    · exact le_natDegree_of_ne_zero (h_coeff.symm ▸ this)
  · simp [*]

lemma hermiteBiehler_factor_two {f g : ℝ[X]}
    (hf : f.Monic) (hg : g.Monic) (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2) :
    ∃ w₁ w₂ : ℂ,
      hermiteBiehlerPolynomial f g
        = C (1 + Complex.I) * ((X - C w₁) * (X - C w₂)) ∧
      (hermiteBiehlerPolynomial f g).roots = {w₁, w₂} := by
  obtain ⟨hdeg, hlead⟩ := hermiteBiehler_natDegree_of_monic hf hg hf₂ hg₂
  have h_splits : (hermiteBiehlerPolynomial f g).Splits := IsAlgClosed.splits _
  have : (hermiteBiehlerPolynomial f g).roots.card = 2 := by
    rw [splits_iff_card_roots.mp h_splits, hdeg]
  obtain ⟨w₁, w₂, hroots⟩ := Multiset.card_eq_two.mp this
  refine ⟨w₁, w₂, ?_, hroots⟩
  have : (hermiteBiehlerPolynomial f g).leadingCoeff = 1 + Complex.I := by
    rw [leadingCoeff, hdeg, hlead]
  rw [h_splits.eq_prod_roots, this, hroots]
  simp

theorem splits_of_stable_monic_two {f g : ℝ[X]}
    (hf : f.Monic) (hg : g.Monic) (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    f.Splits ∧ g.Splits := by
  obtain ⟨w₁, w₂, hfact, hroots⟩ := hermiteBiehler_factor_two hf hg hf₂ hg₂
  have hne : hermiteBiehlerPolynomial f g ≠ 0 := by
    intro h_zero
    simp_all
  have hv₁ : w₁.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  have hv₂ : w₂.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  have hpoly : hermiteBiehlerPolynomial f g
      = C (1 + Complex.I) * X ^ 2 + C ((1 + Complex.I) * (-(w₁ + w₂))) * X
        + C ((1 + Complex.I) * (w₁ * w₂)) := by
    rw [hfact]
    simp only [C_mul, C_add, C_neg]
    ring
  have hc₁ : (f.coeff 1 : ℂ) + Complex.I * (g.coeff 1 : ℂ)
      = (1 + Complex.I) * (-(w₁ + w₂)) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X_one]
    simp [*]
  have hc₀ : (f.coeff 0 : ℂ) + Complex.I * (g.coeff 0 : ℂ)
      = (1 + Complex.I) * (w₁ * w₂) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp
  have hb₁ : f.coeff 1 = -(w₁.re + w₂.re) + (w₁.im + w₂.im) := by
    have := congrArg Complex.re hc₁
    simp [Complex.add_re, Complex.mul_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    linarith
  have hb₂ : g.coeff 1 = -(w₁.re + w₂.re) - (w₁.im + w₂.im) := by
    have := congrArg Complex.im hc₁
    simp [Complex.add_re, Complex.mul_im, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    linarith
  have hcf : f.coeff 0 = w₁.re * w₂.re - w₁.im * w₂.im
      - (w₁.re * w₂.im + w₂.re * w₁.im) := by
    have := congrArg Complex.re hc₀
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im] at this
    linarith
  have hcg : g.coeff 0 = w₁.re * w₂.re - w₁.im * w₂.im
      + (w₁.re * w₂.im + w₂.re * w₁.im) := by
    have := congrArg Complex.im hc₀
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im] at this
    linarith
  have hdiscf : 0 ≤ discrim 1 (f.coeff 1) (f.coeff 0) := by
    rw [discrim, hb₁, hcf]
    have := discrim_nonneg_of_im_nonpos (u₁ := w₁.re) (u₂ := w₂.re) hv₁ hv₂
    nlinarith [this]
  have hdiscg : 0 ≤ discrim 1 (g.coeff 1) (g.coeff 0) := by
    rw [discrim, hb₂, hcg]
    have := discrim_nonneg_of_im_nonpos' (u₁ := w₁.re) (u₂ := w₂.re) hv₁ hv₂
    nlinarith [this]
  have hfexp : f = C 1 * X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) := by
    have h₂ : f.coeff 2 = 1 := by
      rw [← hf₂]
      exact hf
    simpa [h₂] using eq_X_sq_add_X_add_C_of_natDegree_le_two (p := f) (by lia)
  have hgexp : g = C 1 * X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := by
    have h₂ : g.coeff 2 = 1 := by
      rw [← hg₂]
      exact hg
    simpa [h₂] using eq_X_sq_add_X_add_C_of_natDegree_le_two (p := g) (by lia)
  constructor
  · rw [hfexp]
    exact splits_of_discrim_nonneg one_ne_zero hdiscf
  · rw [hgexp]
    exact splits_of_discrim_nonneg one_ne_zero hdiscg

lemma triangle_of_sq {A B t S : ℝ} (hA₀ : 0 ≤ A) (hB₀ : 0 ≤ B) (ht₀ : 0 ≤ t)
    (ht₂ : t ^ 2 = A ^ 2 + B ^ 2 - 2 * S) (hS₁ : S ≤ A * B) (hS₂ : -S ≤ A * B) :
    A - B ≤ t ∧ B - A ≤ t ∧ t ≤ A + B := by
  refine ⟨?_, ?_, ?_⟩ <;>
    nlinarith [sq_nonneg (A - B), sq_nonneg (A + B), sq_nonneg (t - (A - B)),
      sq_nonneg (t + (A - B)), sq_nonneg (t - (A + B))]

lemma interlace_core {u₁ u₂ v₁ v₂ b₁ b₂ c₁ c₂ : ℝ}
    (hv₁ : v₁ ≤ 0) (hv₂ : v₂ ≤ 0)
    (hb₁ : b₁ = -(u₁ + u₂) + (v₁ + v₂))
    (hb₂ : b₂ = -(u₁ + u₂) - (v₁ + v₂))
    (hc₁ : c₁ = u₁ * u₂ - v₁ * v₂ - (u₁ * v₂ + u₂ * v₁))
    (hc₂ : c₂ = u₁ * u₂ - v₁ * v₂ + (u₁ * v₂ + u₂ * v₁)) :
    (-b₂ - Real.sqrt (b₂ ^ 2 - 4 * c₂)) / 2 ≤
        (-b₁ - Real.sqrt (b₁ ^ 2 - 4 * c₁)) / 2 ∧
      (-b₁ - Real.sqrt (b₁ ^ 2 - 4 * c₁)) / 2 ≤
        (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * c₂)) / 2 ∧
      (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * c₂)) / 2 ≤
        (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * c₁)) / 2 := by
  have hvv : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  have hDf : b₁ ^ 2 - 4 * c₁ = (u₁ - u₂ - v₁ + v₂) ^ 2 + 8 * (v₁ * v₂) := by
    rw [hb₁, hc₁]
    ring
  have hDg : b₂ ^ 2 - 4 * c₂ = (u₁ - u₂ + v₁ - v₂) ^ 2 + 8 * (v₁ * v₂) := by
    rw [hb₂, hc₂]
    ring
  have hDf₀ : 0 ≤ b₁ ^ 2 - 4 * c₁ := by
    rw [hDf]
    positivity
  have hDg₀ : 0 ≤ b₂ ^ 2 - 4 * c₂ := by
    rw [hDg]
    positivity
  set A := Real.sqrt (b₁ ^ 2 - 4 * c₁) with hA
  set B := Real.sqrt (b₂ ^ 2 - 4 * c₂) with hB
  have hA₀ : 0 ≤ A := Real.sqrt_nonneg _
  have hB₀ : 0 ≤ B := Real.sqrt_nonneg _
  have hA₂ : A ^ 2 = b₁ ^ 2 - 4 * c₁ := Real.sq_sqrt hDf₀
  have hB₂ : B ^ 2 = b₂ ^ 2 - 4 * c₂ := Real.sq_sqrt hDg₀
  have hAB₀ : 0 ≤ A * B := mul_nonneg hA₀ hB₀
  have hprodsq : ((u₁ - u₂) ^ 2 - (v₁ - v₂) ^ 2) ^ 2 ≤ (A * B) ^ 2 := by
    have hABsq : (A * B) ^ 2 =
        (b₁ ^ 2 - 4 * c₁) * (b₂ ^ 2 - 4 * c₂) := by
      rw [mul_pow, hA₂, hB₂]
    rw [hABsq, hDf, hDg]
    nlinarith [mul_nonneg hvv (by positivity : (0 : ℝ) ≤ (u₁ - u₂) ^ 2 + (v₁ - v₂) ^ 2),
      sq_nonneg (v₁ * v₂)]
  have hle₁ : (u₁ - u₂) ^ 2 - (v₁ - v₂) ^ 2 ≤ A * B := by nlinarith [hprodsq, hAB₀]
  have hle₂ : -((u₁ - u₂) ^ 2 - (v₁ - v₂) ^ 2) ≤ A * B := by nlinarith [hprodsq, hAB₀]
  have hbb : 0 ≤ b₂ - b₁ := by
    rw [hb₁, hb₂]
    linarith
  have ht₂ : (b₂ - b₁) ^ 2
      = A ^ 2 + B ^ 2 - 2 * ((u₁ - u₂) ^ 2 - (v₁ - v₂) ^ 2) := by
    rw [hA₂, hB₂, hb₁, hb₂, hc₁, hc₂]
    ring
  obtain ⟨h₁, h₂, h₃⟩ := triangle_of_sq hA₀ hB₀ hbb ht₂ hle₁ hle₂
  refine ⟨by linarith, by linarith, by linarith⟩

lemma roots_monic_quadratic {b c : ℝ} (hd : 0 ≤ b ^ 2 - 4 * c) :
    (C 1 * X ^ 2 + C b * X + C c).roots
      = {(-b - Real.sqrt (b ^ 2 - 4 * c)) / 2, (-b + Real.sqrt (b ^ 2 - 4 * c)) / 2} := by
  have hs₂ : Real.sqrt (b ^ 2 - 4 * c) ^ 2 = b ^ 2 - 4 * c := Real.sq_sqrt hd
  apply (Polynomial.roots_quadratic_eq_pair_iff_of_ne_zero'
    (a := (1 : ℝ)) (b := b) (c := c) (ha := one_ne_zero)).2
  constructor
  · field_simp
    ring
  · field_simp
    nlinarith [hs₂]

lemma hermiteBiehler_vieta_two {f g : ℝ[X]}
    (hf : f.Monic) (hg : g.Monic) (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    ∃ u₁ u₂ v₁ v₂ : ℝ, v₁ ≤ 0 ∧ v₂ ≤ 0 ∧
      f.coeff 1 = -(u₁ + u₂) + (v₁ + v₂) ∧
      g.coeff 1 = -(u₁ + u₂) - (v₁ + v₂) ∧
      f.coeff 0 = u₁ * u₂ - v₁ * v₂ - (u₁ * v₂ + u₂ * v₁) ∧
      g.coeff 0 = u₁ * u₂ - v₁ * v₂ + (u₁ * v₂ + u₂ * v₁) := by
  obtain ⟨w₁, w₂, hfact, hroots⟩ := hermiteBiehler_factor_two hf hg hf₂ hg₂
  have hne : hermiteBiehlerPolynomial f g ≠ 0 := by
    intro h_zero
    simp_all
  have hv₁ : w₁.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  have hv₂ : w₂.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  have hpoly : hermiteBiehlerPolynomial f g
      = C (1 + Complex.I) * X ^ 2 + C ((1 + Complex.I) * (-(w₁ + w₂))) * X
        + C ((1 + Complex.I) * (w₁ * w₂)) := by
    rw [hfact]
    simp only [C_mul, C_add, C_neg]
    ring
  have hc₁ : (f.coeff 1 : ℂ) + Complex.I * (g.coeff 1 : ℂ)
      = (1 + Complex.I) * (-(w₁ + w₂)) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X_one]
    simp [*]
  have hc₀ : (f.coeff 0 : ℂ) + Complex.I * (g.coeff 0 : ℂ)
      = (1 + Complex.I) * (w₁ * w₂) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp
  refine ⟨w₁.re, w₂.re, w₁.im, w₂.im, hv₁, hv₂, ?_, ?_, ?_, ?_⟩
  · have := congrArg Complex.re hc₁
    simp [Complex.add_re, Complex.mul_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    linarith
  · have := congrArg Complex.im hc₁
    simp [Complex.add_re, Complex.mul_im, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    linarith
  · have := congrArg Complex.re hc₀
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im] at this
    linarith
  · have := congrArg Complex.im hc₀
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im] at this
    linarith

theorem prec_of_stable_monic_two {f g : ℝ[X]}
    (hf : f.Monic) (hg : g.Monic) (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    Prec g f := by
  obtain ⟨hfs, hgs⟩ := splits_of_stable_monic_two hf hg hf₂ hg₂ hstab
  obtain ⟨u₁, u₂, v₁, v₂, hv₁, hv₂, hb₁, hb₂, hcf, hcg⟩ :=
    hermiteBiehler_vieta_two hf hg hf₂ hg₂ hstab
  have hfexp : f = C 1 * X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) := by
    have h₂ : f.coeff 2 = 1 := by
      rw [← hf₂]
      exact hf
    simpa [h₂] using eq_X_sq_add_X_add_C_of_natDegree_le_two (p := f) (by lia)
  have hgexp : g = C 1 * X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := by
    have h₂ : g.coeff 2 = 1 := by
      rw [← hg₂]
      exact hg
    simpa [h₂] using eq_X_sq_add_X_add_C_of_natDegree_le_two (p := g) (by lia)
  set b₁ := f.coeff 1 with hb₁def
  set c₁ := f.coeff 0 with hc₁def
  set b₂ := g.coeff 1 with hb₂def
  set c₂ := g.coeff 0 with hc₂def
  have : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  have hDf₀ : 0 ≤ b₁ ^ 2 - 4 * c₁ := by
    have : b₁ ^ 2 - 4 * c₁ = (u₁ - u₂ - v₁ + v₂) ^ 2 + 8 * (v₁ * v₂) := by
      rw [hb₁, hcf]
      ring
    rw [this]
    positivity
  have hDg₀ : 0 ≤ b₂ ^ 2 - 4 * c₂ := by
    have : b₂ ^ 2 - 4 * c₂ = (u₁ - u₂ + v₁ - v₂) ^ 2 + 8 * (v₁ * v₂) := by
      rw [hb₂, hcg]
      ring
    rw [this]
    positivity
  have hfroots : f.roots = {(-b₁ - Real.sqrt (b₁ ^ 2 - 4 * c₁)) / 2,
      (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * c₁)) / 2} := by
    conv_lhs => rw [hfexp]
    exact roots_monic_quadratic hDf₀
  have hgroots : g.roots = {(-b₂ - Real.sqrt (b₂ ^ 2 - 4 * c₂)) / 2,
      (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * c₂)) / 2} := by
    conv_lhs => rw [hgexp]
    exact roots_monic_quadratic hDg₀
  obtain ⟨h₁, h₂, h₃⟩ := interlace_core hv₁ hv₂ hb₁ hb₂ hcf hcg
  have hA₀ : 0 ≤ Real.sqrt (b₁ ^ 2 - 4 * c₁) := Real.sqrt_nonneg _
  have hB₀ : 0 ≤ Real.sqrt (b₂ ^ 2 - 4 * c₂) := Real.sqrt_nonneg _
  refine ⟨⟨hg.ne_zero, hgs⟩, ⟨hf.ne_zero, hfs⟩,
    [(-b₂ - Real.sqrt (b₂ ^ 2 - 4 * c₂)) / 2, (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * c₂)) / 2],
    [(-b₁ - Real.sqrt (b₁ ^ 2 - 4 * c₁)) / 2, (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * c₁)) / 2],
    ?_, ?_, ?_, ?_, Or.inr ⟨rfl, ?_⟩⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
    linarith
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
    linarith
  · rw [hgroots]
    rfl
  · rw [hfroots]
    rfl
  · simp only [ListAlternates, ListInterlaces, and_true]
    exact ⟨h₁, h₂, h₃⟩

lemma discrim_nonneg_of_im_nonpos_f {a b u₁ u₂ v₁ v₂ : ℝ}
    (hv₁ : v₁ ≤ 0) (hv₂ : v₂ ≤ 0) :
    0 ≤ (-(a * (u₁ + u₂)) + b * (v₁ + v₂)) ^ 2
      - 4 * a * (a * (u₁ * u₂ - v₁ * v₂) - b * (u₁ * v₂ + u₂ * v₁)) := by
  have hvv := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  nlinarith [sq_nonneg (a * (u₁ - u₂) - b * (v₁ - v₂)),
    mul_nonneg (show 0 ≤ 4 * (a ^ 2 + b ^ 2) by positivity) hvv]

lemma discrim_nonneg_of_im_nonpos_g {a b u₁ u₂ v₁ v₂ : ℝ}
    (hv₁ : v₁ ≤ 0) (hv₂ : v₂ ≤ 0) :
    0 ≤ (-(a * (v₁ + v₂)) - b * (u₁ + u₂)) ^ 2
      - 4 * b * (a * (u₁ * v₂ + u₂ * v₁) + b * (u₁ * u₂ - v₁ * v₂)) := by
  have hvv := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  nlinarith [sq_nonneg (b * (u₁ - u₂) + a * (v₁ - v₂)),
    mul_nonneg (show 0 ≤ 4 * (a ^ 2 + b ^ 2) by positivity) hvv]

lemma hermiteBiehler_natDegree_of_posLead {f g : ℝ[X]} {d : ℕ}
    (hf : 0 < f.coeff d) (hfd : f.natDegree = d) (hgd : g.natDegree = d) :
    (hermiteBiehlerPolynomial f g).natDegree = d ∧
      (hermiteBiehlerPolynomial f g).coeff d
        = (f.coeff d : ℂ) + Complex.I * (g.coeff d : ℂ) := by
  have h_coeff : (hermiteBiehlerPolynomial f g).coeff d
      = (f.coeff d : ℂ) + Complex.I * (g.coeff d : ℂ) := hermiteBiehler_coeff f g d
  have : ((f.coeff d : ℂ) + Complex.I * (g.coeff d : ℂ)) ≠ 0 := by
    intro h
    have hre : f.coeff d = 0 := by simpa using congrArg Complex.re h
    exact hf.ne' hre
  constructor
  · apply le_antisymm
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro n hn
      rw [hermiteBiehler_coeff, coeff_eq_zero_of_natDegree_lt (hfd.symm ▸ hn),
        coeff_eq_zero_of_natDegree_lt (hgd.symm ▸ hn)]
      simp
    · exact le_natDegree_of_ne_zero (h_coeff.symm ▸ this)
  · simp [*]

lemma hermiteBiehler_factor_two_posLead {f g : ℝ[X]}
    (hf : 0 < f.coeff 2) (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2) :
    ∃ w₁ w₂ : ℂ,
      hermiteBiehlerPolynomial f g
        = C ((f.coeff 2 : ℂ) + Complex.I * (g.coeff 2 : ℂ))
          * ((X - C w₁) * (X - C w₂)) ∧
      (hermiteBiehlerPolynomial f g).roots = {w₁, w₂} := by
  obtain ⟨hdeg, hlead⟩ := hermiteBiehler_natDegree_of_posLead hf hf₂ hg₂
  have h_splits : (hermiteBiehlerPolynomial f g).Splits := IsAlgClosed.splits _
  have : (hermiteBiehlerPolynomial f g).roots.card = 2 := by
    rw [splits_iff_card_roots.mp h_splits, hdeg]
  obtain ⟨w₁, w₂, hroots⟩ := Multiset.card_eq_two.mp this
  refine ⟨w₁, w₂, ?_, hroots⟩
  have : (hermiteBiehlerPolynomial f g).leadingCoeff
      = (f.coeff 2 : ℂ) + Complex.I * (g.coeff 2 : ℂ) := by
    rw [leadingCoeff, hdeg, hlead]
  rw [h_splits.eq_prod_roots, this, hroots]
  simp

lemma hermiteBiehler_vieta_two_posLead {f g : ℝ[X]}
    (hf : 0 < f.coeff 2) (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    ∃ u₁ u₂ v₁ v₂ : ℝ, v₁ ≤ 0 ∧ v₂ ≤ 0 ∧
      f.coeff 1 = -(f.coeff 2 * (u₁ + u₂)) + g.coeff 2 * (v₁ + v₂) ∧
      g.coeff 1 = -(f.coeff 2 * (v₁ + v₂)) - g.coeff 2 * (u₁ + u₂) ∧
      f.coeff 0 =
        f.coeff 2 * (u₁ * u₂ - v₁ * v₂) -
          g.coeff 2 * (u₁ * v₂ + u₂ * v₁) ∧
      g.coeff 0 =
        f.coeff 2 * (u₁ * v₂ + u₂ * v₁) +
          g.coeff 2 * (u₁ * u₂ - v₁ * v₂) := by
  obtain ⟨w₁, w₂, hfact, hroots⟩ := hermiteBiehler_factor_two_posLead hf hf₂ hg₂
  have hne : hermiteBiehlerPolynomial f g ≠ 0 := by
    intro h_zero
    simp_all
  have hv₁ : w₁.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  have hv₂ : w₂.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  set L : ℂ := (f.coeff 2 : ℂ) + Complex.I * (g.coeff 2 : ℂ) with hL
  have hpoly : hermiteBiehlerPolynomial f g
      = C L * X ^ 2 + C (L * (-(w₁ + w₂))) * X + C (L * (w₁ * w₂)) := by
    rw [hfact]
    simp only [C_mul, C_add, C_neg]
    ring
  have hc₁ : (f.coeff 1 : ℂ) + Complex.I * (g.coeff 1 : ℂ) = L * (-(w₁ + w₂)) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp
  have hc₀ : (f.coeff 0 : ℂ) + Complex.I * (g.coeff 0 : ℂ) = L * (w₁ * w₂) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp
  refine ⟨w₁.re, w₂.re, w₁.im, w₂.im, hv₁, hv₂, ?_, ?_, ?_, ?_⟩
  · have := congrArg Complex.re hc₁
    simp [hL, Complex.add_re, Complex.mul_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    ring_nf at this ⊢
    assumption
  · have := congrArg Complex.im hc₁
    simp [hL, Complex.add_re, Complex.mul_im, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    ring_nf at this ⊢
    assumption
  · have := congrArg Complex.re hc₀
    simp [hL, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im] at this
    ring_nf at this ⊢
    assumption
  · have := congrArg Complex.im hc₀
    simp [hL, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im] at this
    ring_nf at this ⊢
    assumption

theorem splits_of_stable_two {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    f.Splits ∧ g.Splits := by
  have ha : 0 < f.coeff 2 := by rw [← hf₂]; exact hf
  have hb : 0 < g.coeff 2 := by rw [← hg₂]; exact hg
  obtain ⟨u₁, u₂, v₁, v₂, hv₁, hv₂, hb₁, hb₂, hcf, hcg⟩ :=
    hermiteBiehler_vieta_two_posLead ha hf₂ hg₂ hstab
  have hdiscf : 0 ≤ discrim (f.coeff 2) (f.coeff 1) (f.coeff 0) := by
    rw [discrim, hb₁, hcf]
    have := discrim_nonneg_of_im_nonpos_f (a := f.coeff 2) (b := g.coeff 2)
      (u₁ := u₁) (u₂ := u₂) hv₁ hv₂
    assumption
  have hdiscg : 0 ≤ discrim (g.coeff 2) (g.coeff 1) (g.coeff 0) := by
    rw [discrim, hb₂, hcg]
    have := discrim_nonneg_of_im_nonpos_g (a := f.coeff 2) (b := g.coeff 2)
      (u₁ := u₁) (u₂ := u₂) hv₁ hv₂
    assumption
  have hfexp : f = C (f.coeff 2) * X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) :=
    eq_X_sq_add_X_add_C_of_natDegree_le_two (by lia)
  have hgexp : g = C (g.coeff 2) * X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) :=
    eq_X_sq_add_X_add_C_of_natDegree_le_two (by lia)
  constructor
  · rw [hfexp]
    exact splits_of_discrim_nonneg (ne_of_gt ha) hdiscf
  · rw [hgexp]
    exact splits_of_discrim_nonneg (ne_of_gt hb) hdiscg

lemma interlace_core_abstract {a b b₁ b₂ c₁ c₂ p q K : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hK0 : 0 ≤ K)
    (hDf : b₁ ^ 2 - 4 * a * c₁ = p ^ 2 + K)
    (hDg : b₂ ^ 2 - 4 * b * c₂ = q ^ 2 + K)
    (ht0 : 0 ≤ a * b₂ - b * b₁)
    (ht2 : (a * b₂ - b * b₁) ^ 2
      = b ^ 2 * (p ^ 2 + K) + a ^ 2 * (q ^ 2 + K) - 2 * (a * b * (p * q))) :
    (-b₂ - Real.sqrt (b₂ ^ 2 - 4 * b * c₂)) / (2 * b)
        ≤ (-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a) ∧
      (-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a)
        ≤ (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * b * c₂)) / (2 * b) ∧
      (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * b * c₂)) / (2 * b)
        ≤ (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a) := by
  have hDf0 : 0 ≤ b₁ ^ 2 - 4 * a * c₁ := by rw [hDf]; positivity
  have hDg0 : 0 ≤ b₂ ^ 2 - 4 * b * c₂ := by rw [hDg]; positivity
  set A := Real.sqrt (b₁ ^ 2 - 4 * a * c₁) with hA
  set B := Real.sqrt (b₂ ^ 2 - 4 * b * c₂) with hB
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hA2 : A ^ 2 = p ^ 2 + K := by simp_all
  have hB2 : B ^ 2 = q ^ 2 + K := by simp_all
  have hA'0 : 0 ≤ b * A := mul_nonneg hb.le hA0
  have hB'0 : 0 ≤ a * B := mul_nonneg ha.le hB0
  have ht2' : (a * b₂ - b * b₁) ^ 2
      = (b * A) ^ 2 + (a * B) ^ 2 - 2 * (a * b * (p * q)) := by
    rw [mul_pow, mul_pow, hA2, hB2, ht2]
  have hprodsq : (a * b * (p * q)) ^ 2 ≤ (b * A * (a * B)) ^ 2 := by
    have hABsq : (b * A * (a * B)) ^ 2 = a ^ 2 * b ^ 2 * ((p ^ 2 + K) * (q ^ 2 + K)) := by
      have : (b * A * (a * B)) ^ 2 = b ^ 2 * a ^ 2 * (A ^ 2 * B ^ 2) := by ring
      rw [this, hA2, hB2]; ring
    have key : a ^ 2 * b ^ 2 * ((p ^ 2 + K) * (q ^ 2 + K)) - (a * b * (p * q)) ^ 2
        = (a ^ 2 * b ^ 2 * K) * (p ^ 2 + q ^ 2 + K) := by ring
    have hpos : 0 ≤ (a ^ 2 * b ^ 2 * K) * (p ^ 2 + q ^ 2 + K) := by positivity
    rw [hABsq]
    linarith [key, hpos]
  have hAB0 : 0 ≤ b * A * (a * B) := mul_nonneg hA'0 hB'0
  have hle1 : a * b * (p * q) ≤ b * A * (a * B) := by nlinarith [hprodsq, hAB0]
  have hle2 : -(a * b * (p * q)) ≤ b * A * (a * B) := by nlinarith [hprodsq, hAB0]
  obtain ⟨h₁, h₂, h₃⟩ := triangle_of_sq hA'0 hB'0 ht0 ht2' hle1 hle2
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by simp [*]) (by simp [*])]
    nlinarith [h₁]
  · rw [div_le_div_iff₀ (by simp [*]) (by simp [*])]
    nlinarith [h₃]
  · rw [div_le_div_iff₀ (by simp [*]) (by simp [*])]
    nlinarith [h₂]

lemma interlace_core_posLead {a b u₁ u₂ v₁ v₂ b₁ b₂ c₁ c₂ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hv₁ : v₁ ≤ 0) (hv₂ : v₂ ≤ 0)
    (hb₁ : b₁ = -(a * (u₁ + u₂)) + b * (v₁ + v₂))
    (hb₂ : b₂ = -(a * (v₁ + v₂)) - b * (u₁ + u₂))
    (hc₁ : c₁ = a * (u₁ * u₂ - v₁ * v₂) - b * (u₁ * v₂ + u₂ * v₁))
    (hc₂ : c₂ = a * (u₁ * v₂ + u₂ * v₁) + b * (u₁ * u₂ - v₁ * v₂)) :
    (-b₂ - Real.sqrt (b₂ ^ 2 - 4 * b * c₂)) / (2 * b)
        ≤ (-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a) ∧
      (-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a)
        ≤ (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * b * c₂)) / (2 * b) ∧
      (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * b * c₂)) / (2 * b)
        ≤ (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a) := by
  have : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  refine interlace_core_abstract (p := a * (u₁ - u₂) - b * (v₁ - v₂))
    (q := b * (u₁ - u₂) + a * (v₁ - v₂)) (K := 4 * (a ^ 2 + b ^ 2) * (v₁ * v₂))
    ha hb (by positivity) ?_ ?_ ?_ ?_
  · rw [hb₁, hc₁]; ring
  · rw [hb₂, hc₂]; ring
  · have htid : a * b₂ - b * b₁ = -((a ^ 2 + b ^ 2) * (v₁ + v₂)) := by
      rw [hb₁, hb₂]
      ring
    rw [htid]
    have hsum : v₁ + v₂ ≤ 0 := add_nonpos hv₁ hv₂
    nlinarith [sq_nonneg a, sq_nonneg b]
  · rw [hb₁, hb₂]; ring

theorem prec_of_stable_two {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hf₂ : f.natDegree = 2) (hg₂ : g.natDegree = 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    Prec g f := by
  obtain ⟨hfs, hgs⟩ := splits_of_stable_two hf hg hf₂ hg₂ hstab
  have ha : 0 < f.coeff 2 := by
    rw [← hf₂]
    exact hf
  have h_b_pos : 0 < g.coeff 2 := by
    rw [← hg₂]
    exact hg
  have h_f_ne : f ≠ 0 := fun h_zero => by simp [h_zero] at ha
  have h_g_ne : g ≠ 0 := fun h_zero => by simp [h_zero] at h_b_pos
  obtain ⟨u₁, u₂, v₁, v₂, hv₁, hv₂, hb₁, hb₂, h_cf, h_cg⟩ :=
    hermiteBiehler_vieta_two_posLead ha hf₂ hg₂ hstab
  have hfexp : f = C (f.coeff 2) * X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) :=
    eq_X_sq_add_X_add_C_of_natDegree_le_two (by lia)
  have hgexp : g = C (g.coeff 2) * X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) :=
    eq_X_sq_add_X_add_C_of_natDegree_le_two (by lia)
  set a := f.coeff 2
  set bb := g.coeff 2
  set b₁ := f.coeff 1
  set c₁ := f.coeff 0
  set b₂ := g.coeff 1
  set c₂ := g.coeff 0
  have hvv : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  have hDf₀ : 0 ≤ b₁ ^ 2 - 4 * a * c₁ := by
    have : b₁ ^ 2 - 4 * a * c₁
        = (a * (u₁ - u₂) - bb * (v₁ - v₂)) ^ 2 + 4 * (a ^ 2 + bb ^ 2) * (v₁ * v₂) := by
      rw [hb₁, h_cf]
      ring
    rw [this]
    positivity
  have hDg₀ : 0 ≤ b₂ ^ 2 - 4 * bb * c₂ := by
    have : b₂ ^ 2 - 4 * bb * c₂
        = (bb * (u₁ - u₂) + a * (v₁ - v₂)) ^ 2 + 4 * (a ^ 2 + bb ^ 2) * (v₁ * v₂) := by
      rw [hb₂, h_cg]
      ring
    rw [this]
    positivity
  have hfroots : f.roots = {(-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a),
      (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a)} := by
    conv_lhs => rw [hfexp]
    exact roots_quadratic_posLead ha hDf₀
  have hgroots : g.roots = {(-b₂ - Real.sqrt (b₂ ^ 2 - 4 * bb * c₂)) / (2 * bb),
      (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * bb * c₂)) / (2 * bb)} := by
    conv_lhs => rw [hgexp]
    exact roots_quadratic_posLead h_b_pos hDg₀
  obtain ⟨h₁, h₂, h₃⟩ :=
    interlace_core_posLead ha h_b_pos hv₁ hv₂ hb₁ hb₂ h_cf h_cg
  refine ⟨⟨h_g_ne, hgs⟩, ⟨h_f_ne, hfs⟩,
    [(-b₂ - Real.sqrt (b₂ ^ 2 - 4 * bb * c₂)) / (2 * bb),
      (-b₂ + Real.sqrt (b₂ ^ 2 - 4 * bb * c₂)) / (2 * bb)],
    [(-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a),
      (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a)],
    ?_, ?_, ?_, ?_, Or.inr ⟨rfl, ?_⟩⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
    linarith
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
    linarith
  · rw [hgroots]
    rfl
  · rw [hfroots]
    rfl
  · simp only [ListAlternates, ListInterlaces, and_true]
    exact ⟨h₁, h₂, h₃⟩

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

private lemma nonpos_le_of_sq_le_sq {W X : ℝ} (hW : W ≤ 0) (h : X ^ 2 ≤ W ^ 2) :
    W ≤ X ∧ W ≤ -X := by
  constructor <;> nlinarith [sq_nonneg (W - X), sq_nonneg (W + X)]

lemma interlace_core_two_one {a u₁ u₂ v₁ v₂ b₁ b₂ c₁ c₂ : ℝ} (ha : 0 < a)
    (hv₁ : v₁ ≤ 0) (hv₂ : v₂ ≤ 0) (hb₂_pos : 0 < b₂)
    (hb₁ : b₁ = -(a * (u₁ + u₂))) (hb₂ : b₂ = -(a * (v₁ + v₂)))
    (hc₁ : c₁ = a * (u₁ * u₂ - v₁ * v₂))
    (hc₂ : c₂ = a * (u₁ * v₂ + u₂ * v₁)) :
    (-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a) ≤ -c₂ / b₂ ∧
      -c₂ / b₂ ≤ (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a) := by
  have hvv : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  have hinner : 0 ≤ (u₁ - u₂) ^ 2 + 4 * (v₁ * v₂) := by
    nlinarith [sq_nonneg (u₁ - u₂)]
  have hd : b₁ ^ 2 - 4 * a * c₁ =
      a ^ 2 * ((u₁ - u₂) ^ 2 + 4 * (v₁ * v₂)) := by
    rw [hb₁, hc₁]
    ring
  have hD₀ : 0 ≤ b₁ ^ 2 - 4 * a * c₁ := by simp_all
  set t := Real.sqrt (b₁ ^ 2 - 4 * a * c₁) with ht
  have ht₀ : 0 ≤ t := Real.sqrt_nonneg _
  have ht₂ : t ^ 2 = a ^ 2 * ((u₁ - u₂) ^ 2 + 4 * (v₁ * v₂)) := by
    rw [ht, Real.sq_sqrt hD₀, hd]
  have hS : v₁ + v₂ < 0 := by
    by_contra hcon
    have hge : 0 ≤ a * (v₁ + v₂) := mul_nonneg ha.le (not_lt.mp hcon)
    rw [hb₂] at hb₂_pos; linarith
  have hW0 : t * (a * (v₁ + v₂)) ≤ 0 := by nlinarith [mul_nonneg ht₀ ha.le]
  have hWsq : (t * (a * (v₁ + v₂))) ^ 2 =
      a ^ 2 * ((u₁ - u₂) ^ 2 + 4 * (v₁ * v₂)) * (a ^ 2 * (v₁ + v₂) ^ 2) := by
    rw [mul_pow, ht₂]; ring
  have hdiff : (t * (a * (v₁ + v₂))) ^ 2 - (a ^ 2 * ((u₁ - u₂) * (v₁ - v₂))) ^ 2 =
      4 * (a ^ 2 * a ^ 2) * (v₁ * v₂) * ((u₁ - u₂) ^ 2 + (v₁ + v₂) ^ 2) := by
    rw [hWsq]; ring
  have hrhs :
      0 ≤
        4 * (a ^ 2 * a ^ 2) * (v₁ * v₂) *
          ((u₁ - u₂) ^ 2 + (v₁ + v₂) ^ 2) := by
    have h₁ : (0 : ℝ) ≤ 4 * (a ^ 2 * a ^ 2) := by positivity
    have h₂ : (0 : ℝ) ≤ (u₁ - u₂) ^ 2 + (v₁ + v₂) ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg h₁ hvv) h₂
  have hsq :
      (a ^ 2 * ((u₁ - u₂) * (v₁ - v₂))) ^ 2 ≤ (t * (a * (v₁ + v₂))) ^ 2 := by
    linarith
  obtain ⟨hle₁, hle₂⟩ := nonpos_le_of_sq_le_sq hW0 hsq
  constructor
  · rw [div_le_div_iff₀ (by simp [*]) hb₂_pos]
    rw [hb₁, hb₂, hc₂]
    nlinarith [hle₁]
  · rw [div_le_div_iff₀ hb₂_pos (by simp [*])]
    rw [hb₁, hb₂, hc₂]
    nlinarith [hle₂]

lemma hermiteBiehler_factor_two_left {f g : ℝ[X]} (h_f_ne : f ≠ 0)
    (hf₂ : f.natDegree = 2) (hgd : g.natDegree < 2) :
    ∃ w₁ w₂ : ℂ, hermiteBiehlerPolynomial f g =
        C ((f.coeff 2 : ℝ) : ℂ) * ((X - C w₁) * (X - C w₂)) ∧
      (hermiteBiehlerPolynomial f g).roots = {w₁, w₂} := by
  obtain ⟨hdeg, hlead⟩ :=
    hermiteBiehler_natDegree_of_left_dominant h_f_ne (show g.natDegree < f.natDegree by simp [*])
  rw [hf₂] at hdeg
  have hsplits : (hermiteBiehlerPolynomial f g).Splits := IsAlgClosed.splits _
  have hcard : (hermiteBiehlerPolynomial f g).roots.card = 2 := by
    rw [splits_iff_card_roots.mp hsplits, hdeg]
  obtain ⟨w₁, w₂, hroots⟩ := Multiset.card_eq_two.mp hcard
  refine ⟨w₁, w₂, ?_, hroots⟩
  have hlc : (hermiteBiehlerPolynomial f g).leadingCoeff = ((f.coeff 2 : ℝ) : ℂ) := by
    rw [hlead, Polynomial.leadingCoeff, hf₂]
  have := hsplits.eq_prod_roots
  rw [hlc, hroots] at this
  simp [*]

lemma hermiteBiehler_vieta_two_one {f g : ℝ[X]}
    (hf : 0 < f.coeff 2) (hf₂ : f.natDegree = 2) (hgd : g.natDegree < 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    ∃ u₁ u₂ v₁ v₂ : ℝ, v₁ ≤ 0 ∧ v₂ ≤ 0 ∧
      f.coeff 1 = -(f.coeff 2 * (u₁ + u₂)) ∧
      g.coeff 1 = -(f.coeff 2 * (v₁ + v₂)) ∧
      f.coeff 0 = f.coeff 2 * (u₁ * u₂ - v₁ * v₂) ∧
      g.coeff 0 = f.coeff 2 * (u₁ * v₂ + u₂ * v₁) := by
  have h_f_ne : f ≠ 0 := fun h_zero => by simp [h_zero] at hf
  obtain ⟨w₁, w₂, hfact, hroots⟩ := hermiteBiehler_factor_two_left h_f_ne hf₂ hgd
  have hne : hermiteBiehlerPolynomial f g ≠ 0 := by
    intro h_zero
    simp_all
  have hv₁ : w₁.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  have hv₂ : w₂.im ≤ 0 := by
    apply im_nonpos_of_stable_root hstab
    simp [*]
  set L : ℂ := ((f.coeff 2 : ℝ) : ℂ) with hL
  have hpoly : hermiteBiehlerPolynomial f g
      = C L * X ^ 2 + C (L * (-(w₁ + w₂))) * X + C (L * (w₁ * w₂)) := by
    rw [hfact]
    simp only [C_mul, C_add, C_neg]
    ring
  have hc₁ : (f.coeff 1 : ℂ) + Complex.I * (g.coeff 1 : ℂ) = L * (-(w₁ + w₂)) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp
  have hc₀ : (f.coeff 0 : ℂ) + Complex.I * (g.coeff 0 : ℂ) = L * (w₁ * w₂) := by
    rw [← hermiteBiehler_coeff, hpoly]
    simp
  refine ⟨w₁.re, w₂.re, w₁.im, w₂.im, hv₁, hv₂, ?_, ?_, ?_, ?_⟩
  · have := congrArg Complex.re hc₁
    simp [hL, Complex.add_re, Complex.mul_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    ring_nf at this ⊢
    assumption
  · have := congrArg Complex.im hc₁
    simp [hL, Complex.add_re, Complex.mul_im, Complex.add_im,
      Complex.neg_re, Complex.neg_im] at this
    ring_nf at this ⊢
    assumption
  · have := congrArg Complex.re hc₀
    simp [hL, Complex.add_re, Complex.mul_re, Complex.mul_im] at this
    assumption
  · have := congrArg Complex.im hc₀
    simp [hL, Complex.mul_re, Complex.mul_im, Complex.add_im] at this
    ring_nf at this ⊢
    assumption

theorem prec_of_stable_two_one {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hf₂ : f.natDegree = 2) (hg₁ : g.natDegree = 1)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) : Prec g f := by
  have ha : 0 < f.coeff 2 := by
    rw [← hf₂]
    exact hf
  have hb₂_pos : 0 < g.coeff 1 := by
    rw [← hg₁]
    exact hg
  have h_f_ne : f ≠ 0 := fun h_zero ↦ by simp [h_zero] at ha
  have h_g_ne : g ≠ 0 := fun h_zero ↦ by simp [h_zero] at hb₂_pos
  obtain ⟨u₁, u₂, v₁, v₂, hv₁, hv₂, hb₁, hb₂, hc₁, hc₂⟩ :=
    hermiteBiehler_vieta_two_one ha hf₂ (by simp [*]) hstab
  have hfexp : f = C (f.coeff 2) * X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) :=
    eq_X_sq_add_X_add_C_of_natDegree_le_two (by lia)
  have hgexp : g = C (g.coeff 1) * X + C (g.coeff 0) := by
    ext n
    rcases n with _ | _ | n
    · simp
    · simp
    · have h_lt : g.natDegree < n + 2 := by
        rw [hg₁]
        lia
      have hz : g.coeff (n + 2) = 0 := coeff_eq_zero_of_natDegree_lt h_lt
      simp [coeff_add, hz]
  set a := f.coeff 2
  set b₁ := f.coeff 1
  set c₁ := f.coeff 0
  set b₂ := g.coeff 1
  set c₂ := g.coeff 0
  have hvv : 0 ≤ v₁ * v₂ := mul_nonneg_of_nonpos_of_nonpos hv₁ hv₂
  have hDf₀ : 0 ≤ b₁ ^ 2 - 4 * a * c₁ := by
    have hdd : b₁ ^ 2 - 4 * a * c₁ = a ^ 2 * ((u₁ - u₂) ^ 2 + 4 * (v₁ * v₂)) := by
      rw [hb₁, hc₁]
      ring
    rw [hdd]
    exact mul_nonneg (sq_nonneg a) (by nlinarith [sq_nonneg (u₁ - u₂)])
  have hfroots : f.roots = {(-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a),
      (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a)} := by
    conv_lhs => rw [hfexp]
    exact roots_quadratic_posLead ha hDf₀
  have hb₂_ne : b₂ ≠ 0 := ne_of_gt hb₂_pos
  have hgfact : g = C b₂ * (X - C (-c₂ / b₂)) := by
    rw [hgexp, mul_sub, ← C_mul]
    have : b₂ * (-c₂ / b₂) = -c₂ := by field_simp
    rw [this, C_neg, sub_neg_eq_add]
  have hgroots : g.roots = {-c₂ / b₂} := by rw [hgfact, roots_C_mul _ hb₂_ne, roots_X_sub_C]
  have hfs : f.Splits := splits_of_card_roots (by rw [hfroots, hf₂]; simp)
  have hgs : g.Splits := splits_of_card_roots (by rw [hgroots, hg₁]; simp)
  obtain ⟨h₁, h₂⟩ := interlace_core_two_one ha hv₁ hv₂ hb₂_pos hb₁ hb₂ hc₁ hc₂
  refine ⟨⟨h_g_ne, hgs⟩, ⟨h_f_ne, hfs⟩,
    [-c₂ / b₂],
    [(-b₁ - Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a),
      (-b₁ + Real.sqrt (b₁ ^ 2 - 4 * a * c₁)) / (2 * a)],
    ?_, ?_, ?_, ?_, Or.inl ⟨rfl, ?_⟩⟩
  · simp
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
    linarith
  · rw [hgroots]
    simp
  · rw [hfroots]
    rfl
  · simp only [ListInterlaces, and_true]
    exact ⟨h₁, h₂⟩

theorem hermiteBiehlerConverse_of_natDegree_le_two {f g : ℝ[X]}
    (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (hdeg : f.natDegree ≤ 2)
    (hstab : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial f g)) :
    Prec g f ∨ Prec f g := by
  obtain ⟨hgle, hfle⟩ := natDegree_shape_of_stable hf hg hstab
  rcases Nat.lt_or_ge f.natDegree 2 with hflt | hfge
  · exact prec_or_revPrec_of_natDegree_le_one hg hf (by lia) (by lia)
  · have hf₂ : f.natDegree = 2 := by lia
    rcases Nat.lt_or_ge g.natDegree 2 with hglt | hgge
    · have hg₁ : g.natDegree = 1 := by lia
      exact Or.inl (prec_of_stable_two_one hf hg hf₂ hg₁ hstab)
    · have hg₂ : g.natDegree = 2 := by lia
      exact Or.inl (prec_of_stable_two hf hg hf₂ hg₂ hstab)

end RealRooted
