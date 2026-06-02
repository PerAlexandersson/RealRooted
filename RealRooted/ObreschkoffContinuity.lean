import RealRooted.RootContinuity
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Continuity bridge for positive combinations

This file records the local positive-combination hypotheses used by the
Obreschkoff continuity argument, without importing the heavier converse
development.
-/

open Polynomial

noncomputable section

namespace RealRooted

section

/-- Local hypothesis form of positive-combination real-rootedness used by the
continuity bridge file. This avoids importing the converse-development file and
keeps dependencies acyclic. -/
abbrev PosComboHyp (f g : ℝ[X]) : Prop :=
  ∀ {lam μ : ℝ}, 0 < lam → 0 < μ → ((C lam * f + C μ * g) ≠ 0 ∧
    (C lam * f + C μ * g).Splits)

namespace PosComboHyp

lemma comm {f g : ℝ[X]} (hfg : PosComboHyp f g) : PosComboHyp g f := by
  intro lam μ hlam hμ
  simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hfg hμ hlam

lemma isRealRooted_add_left {f g : ℝ[X]} (hfg : PosComboHyp f g)
    {lam : ℝ} (hlam : 0 < lam) :
    ((C lam * f + g) ≠ 0 ∧ (C lam * f + g).Splits) := by
  simpa [one_mul] using hfg (lam := lam) (μ := 1) hlam zero_lt_one

lemma isRealRooted_add_right {f g : ℝ[X]} (hfg : PosComboHyp f g)
    {μ : ℝ} (hμ : 0 < μ) :
    ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits) := by
  simpa [one_mul, add_comm] using hfg (lam := 1) (μ := μ) zero_lt_one hμ

/-- Root-continuity bridge for the left affine family under positive-combination
real-rootedness. This packages the local continuity step in the form needed by
Obreschkoff-style arguments. -/
theorem exists_root_near_left_family
    {f g : ℝ[X]} (hfg : PosComboHyp f g)
    {a t ε : ℝ}
    (ha : f.IsRoot a)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree)
    (ht : 0 < t)
    (hcoeff_bound : (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) < ε) :
    ∃ b : ℝ, (C t * f + g).IsRoot b ∧
      ‖a - b‖ < ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * max ‖a‖ 1 := by
  exact
    exists_real_root_near_in_left_family
      (ha := ha) hf_monic hg_monic hdeg ht hcoeff_bound
      (hfg.isRealRooted_add_left ht)

/-- Complex-root continuity bridge for the left affine family under
positive-combination real-rootedness. -/
theorem exists_complex_aroot_near_left_family
    {f g : ℝ[X]} (hfg : PosComboHyp f g)
    {z : ℂ} {t ε : ℝ}
    (hz : f.aeval z = 0)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree)
    (ht : 0 < t)
    (hcoeff_bound : (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) < ε) :
    ∃ w : ℂ, w ∈ (C t * f + g).aroots ℂ ∧
      ‖z - w‖ < ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * max ‖z‖ 1 := by
  exact
    RealRooted.exists_complex_aroot_near_in_left_family
      (hz := hz) hf_monic hg_monic hdeg ht hcoeff_bound
      (hfg.isRealRooted_add_left ht)

/-- Root continuity in the left affine family with an automatically chosen positive parameter.
Given `ε > 0`, this returns `t > 0` and a root of `C t * f + g` near the chosen root of `f`. -/
theorem exists_t_and_root_near_left_family
    {f g : ℝ[X]} (hfg : PosComboHyp f g)
    {a ε : ℝ}
    (ha : f.IsRoot a)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree)
    (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ∃ b : ℝ, (C t * f + g).IsRoot b ∧
      ‖a - b‖ < ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * max ‖a‖ 1 := by
  obtain ⟨t, ht, hcoeff_bound⟩ :=
    exists_t_pos_with_normalized_left_family_bound (f := f) (g := g) hε
  obtain ⟨b, hb_root, hb_dist⟩ :=
    exists_root_near_left_family
      (hfg := hfg) (ha := ha) hf_monic hg_monic hdeg ht hcoeff_bound
  exact ⟨t, ht, b, hb_root, hb_dist⟩

/-- Root-continuity bridge for the right affine family under positive-combination
real-rootedness. This is the `μ`-small perturbation form used when one studies
`f + C μ * g` near `f`. -/
theorem exists_root_near_right_family
    {f g : ℝ[X]} (hfg : PosComboHyp f g)
    {a μ ε : ℝ}
    (ha : f.IsRoot a)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree)
    (hμ : 0 < μ)
    (hcoeff_bound : (μ / (μ + 1)) * (coeffSumRange f + coeffSumRange g) < ε) :
    ∃ b : ℝ, (f + C μ * g).IsRoot b ∧
      ‖a - b‖ < ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * max ‖a‖ 1 := by
  let t : ℝ := μ⁻¹
  have ht : 0 < t := by
    simp only [inv_pos, t]
    positivity
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ
  have hμ1_ne : μ + 1 ≠ 0 := by linarith
  have hcoeff_bound_left : (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) < ε := by
    have hcalc : (t + 1)⁻¹ = μ / (μ + 1) := by
      unfold t
      field_simp [hμ_ne, hμ1_ne]
      ring
    simpa [hcalc] using hcoeff_bound
  obtain ⟨b, hb_left_root, hb_dist⟩ :=
    exists_root_near_left_family
      (hfg := hfg) (ha := ha) hf_monic hg_monic hdeg ht hcoeff_bound_left
  have hscale :
      f + C μ * g = C μ * (C t * f + g) := by
    ext n
    simp [t]
    field_simp [hμ_ne]
  have hb_right_root : (f + C μ * g).IsRoot b := by
    have hb_eval_left : (C t * f + g).eval b = 0 := by
      simpa [Polynomial.IsRoot.def] using hb_left_root
    have hb_eval_right : (f + C μ * g).eval b = 0 := by
      rw [hscale, eval_mul, eval_C]
      simp [hb_eval_left]
    simpa [Polynomial.IsRoot.def] using hb_eval_right
  exact ⟨b, hb_right_root, hb_dist⟩

/-- Complex-root continuity bridge for the right affine family under
positive-combination real-rootedness. This is the `μ`-small perturbation form
for `f + C μ * g` near complex roots of `f`. -/
theorem exists_complex_aroot_near_right_family
    {f g : ℝ[X]} (hfg : PosComboHyp f g)
    {z : ℂ} {μ ε : ℝ}
    (hz : f.aeval z = 0)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree)
    (hμ : 0 < μ)
    (hcoeff_bound : (μ / (μ + 1)) * (coeffSumRange f + coeffSumRange g) < ε) :
    ∃ w : ℂ, w ∈ (f + C μ * g).aroots ℂ ∧
      ‖z - w‖ < ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * max ‖z‖ 1 := by
  let t : ℝ := μ⁻¹
  have ht : 0 < t := by
    simp only [inv_pos, t]
    positivity
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ
  have hμ1_ne : μ + 1 ≠ 0 := by linarith
  have hcoeff_bound_left : (t + 1)⁻¹ * (coeffSumRange f + coeffSumRange g) < ε := by
    have hcalc : (t + 1)⁻¹ = μ / (μ + 1) := by
      unfold t
      field_simp [hμ_ne, hμ1_ne]
      ring
    simpa [hcalc] using hcoeff_bound
  obtain ⟨w, hw_left_root, hw_dist⟩ :=
    exists_complex_aroot_near_left_family
      (hfg := hfg) (hz := hz) hf_monic hg_monic hdeg ht hcoeff_bound_left
  have hscale :
      f + C μ * g = C μ * (C t * f + g) := by
    ext n
    simp [t]
    field_simp [hμ_ne]
  have hw_right_root : w ∈ (f + C μ * g).aroots ℂ := by
    simpa [hscale, Polynomial.aroots_C_mul _ hμ_ne] using hw_left_root
  exact ⟨w, hw_right_root, hw_dist⟩

/-- Root continuity in the right affine family with an automatically chosen
positive parameter. Given `ε > 0`, this returns `μ > 0` and a root of
`f + C μ * g` near the chosen root of `f`. -/
theorem exists_mu_and_root_near_right_family
    {f g : ℝ[X]} (hfg : PosComboHyp f g)
    {a ε : ℝ}
    (ha : f.IsRoot a)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree)
    (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ b : ℝ, (f + C μ * g).IsRoot b ∧
      ‖a - b‖ < ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * max ‖a‖ 1 := by
  obtain ⟨t, ht, b, hb_left_root, hb_dist⟩ :=
    exists_t_and_root_near_left_family
      (hfg := hfg) (ha := ha) hf_monic hg_monic hdeg hε
  refine ⟨t⁻¹, by positivity, b, ?_, hb_dist⟩
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hscale :
      f + C (t⁻¹) * g = C (t⁻¹) * (C t * f + g) := by
    ext n
    simp
    field_simp [ht_ne]
  have hb_eval_left : (C t * f + g).eval b = 0 := by
    simpa [Polynomial.IsRoot.def] using hb_left_root
  have hb_eval_right : (f + C (t⁻¹) * g).eval b = 0 := by
    rw [hscale, eval_mul, eval_C]
    simp [hb_eval_left]
  simpa [Polynomial.IsRoot.def] using hb_eval_right

/-- Right-family coefficient smallness can be achieved by choosing `μ > 0`
small enough. -/
theorem exists_mu_pos_with_normalized_right_family_bound
    (f g : ℝ[X]) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧
      (μ / (μ + 1)) * (coeffSumRange f + coeffSumRange g) < ε := by
  obtain ⟨t, ht, hbound⟩ :=
    exists_t_pos_with_normalized_left_family_bound (f := f) (g := g) hε
  refine ⟨t⁻¹, by positivity, ?_⟩
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hcalc : t⁻¹ / (t⁻¹ + 1) = (t + 1)⁻¹ := by
    field_simp [ht_ne]
    ring
  simpa [hcalc] using hbound

/-- In the equal-degree monic setting, positive-combination real-rootedness
forces every complex root of `f` to be real. -/
theorem im_eq_zero_of_aeval_zero_of_posComboRealRooted_monic_sameDegree
    {f g : ℝ[X]} (hfg : PosComboHyp f g)
    {z : ℂ}
    (hz : f.aeval z = 0)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree) :
    z.im = 0 := by
  by_contra hz_im_ne
  let δ : ℝ := |z.im| / 2
  let R : ℝ := max ‖z‖ 1
  have hδ_pos : 0 < δ := by
    unfold δ
    exact half_pos (abs_pos.mpr hz_im_ne)
  have hR_pos : 0 < R := by
    unfold R
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hf_deg_pos : 0 < f.natDegree := by
    by_contra hnot
    have hf_deg0 : f.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
    have hf_eq_one : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hf_monic hf_deg0
    have : (1 : ℂ) = 0 := by
      simp [hf_eq_one] at hz
    exact one_ne_zero this
  have hdeg_nat_ne : f.natDegree ≠ 0 := Nat.ne_of_gt hf_deg_pos
  let u : ℝ := δ / (2 * R)
  let ε : ℝ := (u ^ f.natDegree) / (f.natDegree + 1)
  have hu_nonneg : 0 ≤ u := by
    unfold u
    positivity
  have hu_pos : 0 < u := by
    unfold u
    positivity
  have hε_pos : 0 < ε := by
    unfold ε
    positivity
  obtain ⟨μ, hμ, hcoeff_bound⟩ :=
    exists_mu_pos_with_normalized_right_family_bound (f := f) (g := g) hε_pos
  obtain ⟨w, hw_root, hw_dist⟩ :=
    exists_complex_aroot_near_right_family
      (hfg := hfg) (hz := hz) hf_monic hg_monic hdeg hμ hcoeff_bound
  have hw_im_zero : w.im = 0 := by
    exact RealRooted.im_eq_zero_of_mem_aroots_of_isRealRooted
      (hfg.isRealRooted_add_right hμ) hw_root
  have hbound_eq :
      ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * R = δ / 2 := by
    have hmul :
        ((f.natDegree + 1 : ℝ) * ε) = u ^ f.natDegree := by
      unfold ε
      field_simp
    calc
      ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * R
          = (u ^ f.natDegree) ^ ((f.natDegree : ℝ)⁻¹) * R := by rw [hmul]
      _ = u * R := by rw [Real.pow_rpow_inv_natCast hu_nonneg hdeg_nat_ne]
      _ = δ / 2 := by
            unfold u
            field_simp [hR_pos.ne']
  have hdist_lt_delta : ‖z - w‖ < δ := by
    calc
      ‖z - w‖ < ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * max ‖z‖ 1 := hw_dist
      _ = ((f.natDegree + 1) * ε) ^ ((f.natDegree : ℝ)⁻¹) * R := by simp [R]
      _ = δ / 2 := hbound_eq
      _ < δ := by linarith [hδ_pos]
  have him_le : |z.im| ≤ ‖z - w‖ := by
    simpa [Complex.sub_im, hw_im_zero] using (Complex.abs_im_le_norm (z - w))
  have him_lt : |z.im| < δ := lt_of_le_of_lt him_le hdist_lt_delta
  have hhalf : |z.im| < |z.im| / 2 := by
    simpa [δ] using him_lt
  nlinarith [abs_pos.mpr hz_im_ne, hhalf]

/-- Equal-degree monic positive-combination real-rootedness implies `f` is
real-rooted. -/
theorem isRealRooted_left_of_posComboRealRooted_monic_sameDegree
    {f g : ℝ[X]} (hfg : PosComboHyp f g)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree) :
    (f ≠ 0 ∧ f.Splits) := by
  have hf_ne : f ≠ 0 := hf_monic.ne_zero
  have hroots_real :
      ∀ z ∈ (f.map (algebraMap ℝ ℂ)).roots, z ∈ (algebraMap ℝ ℂ).range := by
    intro z hz_mem
    have hmap_ne : f.map (algebraMap ℝ ℂ) ≠ 0 := by
      exact
        (Polynomial.map_ne_zero_iff (RingHom.injective (algebraMap ℝ ℂ))).2 hf_ne
    have hz_root : (f.map (algebraMap ℝ ℂ)).IsRoot z :=
      (Polynomial.mem_roots hmap_ne).1 hz_mem
    have hz_aeval : f.aeval z = 0 := by
      have hz_eval_map : (f.map (algebraMap ℝ ℂ)).eval z = 0 := by
        simpa [Polynomial.IsRoot.def] using hz_root
      simpa [eval₂_at_apply] using hz_eval_map
    have hz_im :
        z.im = 0 :=
      im_eq_zero_of_aeval_zero_of_posComboRealRooted_monic_sameDegree
        (hfg := hfg) (z := z) hz_aeval hf_monic hg_monic hdeg
    refine ⟨z.re, Complex.ext_iff.2 ?_⟩
    simp [hz_im]
  have hsplit : f.Splits := by
    exact
      Polynomial.Splits.of_splits_map (i := algebraMap ℝ ℂ)
        (IsAlgClosed.splits _) hroots_real
  exact ⟨hf_ne, hsplit⟩

/-- Symmetric right-side version of
`isRealRooted_left_of_posComboRealRooted_monic_sameDegree`. -/
theorem isRealRooted_right_of_posComboRealRooted_monic_sameDegree
    {f g : ℝ[X]} (hfg : PosComboHyp f g)
    (hf_monic : f.Monic) (hg_monic : g.Monic)
    (hdeg : g.natDegree = f.natDegree) :
    (g ≠ 0 ∧ g.Splits) := by
  simpa [eq_comm] using
    isRealRooted_left_of_posComboRealRooted_monic_sameDegree
      (hfg := hfg.comm) hg_monic hf_monic hdeg.symm

/-- Equal-degree positive-combination real-rootedness implies `f` is
real-rooted (without monicity assumptions). -/
theorem isRealRooted_left_of_posComboRealRooted_sameDegree
    {f g : ℝ[X]} (hfg : PosComboHyp f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) :
    (f ≠ 0 ∧ f.Splits) := by
  let f₀ : ℝ[X] := C f.leadingCoeff⁻¹ * f
  let g₀ : ℝ[X] := C g.leadingCoeff⁻¹ * g
  have hf_lc_ne : f.leadingCoeff ≠ 0 := ne_of_gt hf_pos
  have hg_lc_ne : g.leadingCoeff ≠ 0 := ne_of_gt hg_pos
  have hf₀_monic : f₀.Monic := by
    unfold f₀
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    field_simp [hf_lc_ne]
  have hg₀_monic : g₀.Monic := by
    unfold g₀
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    field_simp [hg_lc_ne]
  have hdeg₀ : g₀.natDegree = f₀.natDegree := by
    unfold f₀ g₀
    rw [natDegree_C_mul (inv_ne_zero hf_lc_ne),
      natDegree_C_mul (inv_ne_zero hg_lc_ne), hdeg]
  have hfg₀ : PosComboHyp f₀ g₀ := by
    intro lam μ hlam hμ
    have hlam' : 0 < lam * f.leadingCoeff⁻¹ := by
      exact mul_pos hlam (inv_pos.mpr hf_pos)
    have hμ' : 0 < μ * g.leadingCoeff⁻¹ := by
      exact mul_pos hμ (inv_pos.mpr hg_pos)
    have hbase :=
      hfg (lam := lam * f.leadingCoeff⁻¹) (μ := μ * g.leadingCoeff⁻¹) hlam' hμ'
    simpa [f₀, g₀, mul_assoc, mul_left_comm, mul_comm] using hbase
  have hf₀_rr : (f₀ ≠ 0 ∧ f₀.Splits) :=
    isRealRooted_left_of_posComboRealRooted_monic_sameDegree
      (hfg := hfg₀) hf₀_monic hg₀_monic hdeg₀
  have hf_scale : C f.leadingCoeff * f₀ = f := by
    unfold f₀
    ext n
    simp [hf_lc_ne]
  have hf_rr_scaled : ((C f.leadingCoeff * f₀) ≠ 0 ∧
    (C f.leadingCoeff * f₀).Splits) :=
    isRealRooted_C_mul hf₀_rr hf_lc_ne
  simpa [hf_scale] using hf_rr_scaled

/-- Symmetric right-side version of
`isRealRooted_left_of_posComboRealRooted_sameDegree`. -/
theorem isRealRooted_right_of_posComboRealRooted_sameDegree
    {f g : ℝ[X]} (hfg : PosComboHyp f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree) :
    (g ≠ 0 ∧ g.Splits) := by
  simpa [eq_comm] using
    isRealRooted_left_of_posComboRealRooted_sameDegree
      (hfg := hfg.comm) hg_pos hf_pos hdeg.symm

end PosComboHyp
end
end RealRooted
