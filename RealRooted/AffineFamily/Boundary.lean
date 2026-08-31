/-
# Affine-family boundary reductions

Degree control, boundary real-rootedness, and root-zero reductions for the
affine-family criterion. The parent module owns the later crossing and
Wronskian endgame.
-/
import RealRooted.ProductFamily
import RealRooted.AffineDerivative
import RealRooted.AffineFamily.Basic
import RealRooted.AffineFamily.PositiveFamily
import RealRooted.PosCombo
import RealRooted.SuccDegreeLeftEndpoint
import RealRooted.ObreschkoffConverse
import RealRooted.FolkloreLemma
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

open Polynomial

noncomputable section

namespace RealRooted

/-- Backward Wagner wrapper used in the affine-family endgame:
once the right-hand pair `(g, X * f)` is oriented, nonnegative coefficients
recover the original conclusion `Prec f g`. -/
private lemma affine_family_pair_data {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    {t : ℝ} (ht : 0 < t) :
    PosComboRealRooted (C t * f + g) (X * f) ∧
    HasNonnegCoeffs (C t * f + g) ∧
    HasNonnegCoeffs (X * f) ∧
    (C t * f + g) ≠ 0 ∧
    X * f ≠ 0 ∧
    HasPosLeadingCoeff (C t * f + g) ∧
    HasPosLeadingCoeff (X * f) := by
  have hCt_nonneg : HasNonnegCoeffs (C t * f) := nonnegCoeffs_C_mul ht.le hfnn
  have hsum_nonneg : HasNonnegCoeffs (C t * f + g) := hCt_nonneg.add hgnn
  have hXf_nonneg : HasNonnegCoeffs (X * f) := hfnn.X_mul
  have hCt_ne : C t * f ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr ht.ne') hf0
  have hsum_ne : C t * f + g ≠ 0 :=
    add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hCt_nonneg hgnn hg0
  have hXf_ne : X * f ≠ 0 := mul_ne_zero X_ne_zero hf0
  refine
    ⟨posComboRealRooted_of_affine_family (f := f) (g := g) haff (t := t) ht,
      hsum_nonneg, hXf_nonneg, hsum_ne, hXf_ne,
      hsum_nonneg.pos_leadingCoeff hsum_ne, (hfnn.pos_leadingCoeff hf0).X_mul⟩

/-- Closure lemma for a lower-degree right family:
if every `g + μ f` with `μ > 0` is real-rooted and `deg f < deg g`, then `g`
is already real-rooted. This is the clean boundary-`μ → 0` step that the
succ-degree affine-family branch needs. -/
protected theorem AffineFamily.isRealRooted_of_add_C_mul_right_family_of_natDegree_lt
    {f g : ℝ[X]}
    (hfamily : ∀ {μ : ℝ}, 0 < μ → ((g + C μ * f) ≠ 0 ∧ (g + C μ * f).Splits))
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : f.natDegree < g.natDegree) : (g ≠ 0 ∧ g.Splits) := by
  let f₀ : ℝ[X] := C f.leadingCoeff⁻¹ * f
  let g₀ : ℝ[X] := C g.leadingCoeff⁻¹ * g
  have hf_lc_ne : f.leadingCoeff ≠ 0 := ne_of_gt hf_pos
  have hg_lc_ne : g.leadingCoeff ≠ 0 := ne_of_gt hg_pos
  have hf₀_monic : f₀.Monic := by
    unfold f₀
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hg₀_monic : g₀.Monic := by
    unfold g₀
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hf₀_pos : HasPosLeadingCoeff f₀ := hasPosLeadingCoeff_of_monic hf₀_monic
  have hg₀_pos : HasPosLeadingCoeff g₀ := hasPosLeadingCoeff_of_monic hg₀_monic
  have hdeg₀ : f₀.natDegree < g₀.natDegree := by
    simp [f₀, g₀, natDegree_C_mul, hf_lc_ne, hg_lc_ne, hdeg]
  have hfamily₀ :
      ∀ {μ : ℝ}, 0 < μ → ((g₀ + C μ * f₀) ≠ 0 ∧ (g₀ + C μ * f₀).Splits) := by
    intro μ hμ
    have hμ' : 0 < μ * g.leadingCoeff / f.leadingCoeff :=
      div_pos (mul_pos hμ hg_pos) hf_pos
    have hbase : ((g + C (μ * g.leadingCoeff / f.leadingCoeff) * f) ≠ 0 ∧
      (g + C (μ * g.leadingCoeff / f.leadingCoeff) * f).Splits) :=
      hfamily hμ'
    have hscaled :
        ((C g.leadingCoeff⁻¹ *
            (g + C (μ * g.leadingCoeff / f.leadingCoeff) * f)) ≠ 0 ∧
          (C g.leadingCoeff⁻¹ *
              (g + C (μ * g.leadingCoeff / f.leadingCoeff) * f)).Splits) :=
      isRealRooted_C_mul hbase.1 hbase.2 (inv_ne_zero hg_lc_ne)
    have hEq :
        C g.leadingCoeff⁻¹ *
            (g + C (μ * g.leadingCoeff / f.leadingCoeff) * f) =
          g₀ + C μ * f₀ := by
      ext n
      simp [g₀, f₀]
      grind
    lia
  have hg₀_rr : (g₀ ≠ 0 ∧ g₀.Splits) := by
    have hroots_real :
        ∀ z ∈ (g₀.map (algebraMap ℝ ℂ)).roots, z ∈ (algebraMap ℝ ℂ).range := by
      intro z hz_mem
      have hmap_ne : g₀.map (algebraMap ℝ ℂ) ≠ 0 := by simp_all
      have hz_root : (g₀.map (algebraMap ℝ ℂ)).IsRoot z :=
        (Polynomial.mem_roots hmap_ne).1 hz_mem
      have hz_aeval : g₀.aeval z = 0 := by simp_all
      by_contra hz_range
      have hz_im_ne : z.im ≠ 0 := by
        intro hz_im
        apply hz_range
        refine ⟨z.re, ?_⟩
        apply Complex.ext <;> simp [hz_im]
      let δ : ℝ := |z.im| / 2
      let R : ℝ := max ‖z‖ 1
      have hδ_pos : 0 < δ := by grind
      have hR_pos : 0 < R := by grind
      have hg₀_deg_pos : 0 < g₀.natDegree := lt_of_le_of_lt (Nat.zero_le _) hdeg₀
      have hdeg_nat_ne : g₀.natDegree ≠ 0 := Nat.ne_of_gt hg₀_deg_pos
      let u : ℝ := δ / (2 * R)
      let ε : ℝ := (u ^ g₀.natDegree) / (g₀.natDegree + 1)
      have hu_nonneg : 0 ≤ u := by
        unfold u
        positivity
      have hu_pos : 0 < u := by
        unfold u
        positivity
      have hε_pos : 0 < ε := by
        unfold ε
        positivity
      let μ : ℝ := ε / (coeffSumRange f₀ + 1)
      have hcoeff_nonneg : 0 ≤ coeffSumRange f₀ := by
        unfold coeffSumRange
        exact Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hμ_pos : 0 < μ := by
        unfold μ
        positivity
      have hμ_bound : μ * coeffSumRange f₀ < ε := by
        unfold μ
        have hden_pos : 0 < coeffSumRange f₀ + 1 := by linarith
        have hfrac_lt_one : coeffSumRange f₀ / (coeffSumRange f₀ + 1) < 1 := by
          rw [div_lt_iff₀ hden_pos]
          linarith
        have hcalc :
            (ε / (coeffSumRange f₀ + 1)) * coeffSumRange f₀ =
              ε * (coeffSumRange f₀ / (coeffSumRange f₀ + 1)) := by
          grind
        simp_all
      have hcoeff :
          ∀ i : ℕ, ‖(g₀ + C μ * f₀).coeff i - g₀.coeff i‖ < ε := by
        intro i
        exact lt_of_le_of_lt
          (norm_coeff_sub_add_C_mul_le g₀ f₀ (μ := μ) (M := coeffSumRange f₀)
            hμ_pos.le (fun j => coeff_norm_le_coeffSumRange f₀ j) i)
          hμ_bound
      have hμf_deg_lt : (C μ * f₀).natDegree < g₀.natDegree := by
        simpa [natDegree_C_mul hμ_pos.ne'] using hdeg₀
      have hsum_deg : (g₀ + C μ * f₀).natDegree = g₀.natDegree :=
        natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hμf_deg_lt hg₀_pos
      have hsum_monic : (g₀ + C μ * f₀).Monic := by
        unfold Polynomial.Monic Polynomial.leadingCoeff
        rw [hsum_deg, coeff_add, coeff_eq_zero_of_natDegree_lt hμf_deg_lt,
          hg₀_monic.coeff_natDegree, add_zero]
      obtain ⟨w, hw_root, hw_dist⟩ :=
        exists_complex_aroot_near_of_isRealRooted_of_monic_of_coeff_close
          (f := g₀) (g := g₀ + C μ * f₀) (z := z) (ε := ε)
          hε_pos hz_aeval hg₀_monic hsum_monic hsum_deg hcoeff
            (hfamily₀ hμ_pos).2
      have hw_im_zero : w.im = 0 :=
        RealRooted.im_eq_zero_of_mem_aroots_of_isRealRooted
          (hfamily₀ hμ_pos).1 (hfamily₀ hμ_pos).2 hw_root
      have hbound_eq :
          ((g₀.natDegree + 1) * ε) ^ ((g₀.natDegree : ℝ)⁻¹) * R = δ / 2 := by
        have hmul :
            ((g₀.natDegree + 1 : ℝ) * ε) = u ^ g₀.natDegree := by
          grind
        calc
          ((g₀.natDegree + 1) * ε) ^ ((g₀.natDegree : ℝ)⁻¹) * R
              = (u ^ g₀.natDegree) ^ ((g₀.natDegree : ℝ)⁻¹) * R := by lia
          _ = u * R := by rw [Real.pow_rpow_inv_natCast hu_nonneg hdeg_nat_ne]
          _ = δ / 2 := by grind
      have hdist_lt_delta : ‖z - w‖ < δ := by grind
      have him_le : |z.im| ≤ ‖z - w‖ := by
        simpa [Complex.sub_im, hw_im_zero] using (Complex.abs_im_le_norm (z - w))
      grind
    have hsplit : g₀.Splits :=
      Polynomial.Splits.of_splits_map (i := algebraMap ℝ ℂ)
        (IsAlgClosed.splits _) hroots_real
    exact ⟨hg₀_monic.ne_zero, hsplit⟩
  have hg_scale : C g.leadingCoeff * g₀ = g := by
    unfold g₀
    ext n
    simp_all
  have hg_rr_scaled : ((C g.leadingCoeff * g₀) ≠ 0 ∧ (C g.leadingCoeff * g₀).Splits) :=
    isRealRooted_C_mul hg₀_rr.1 hg₀_rr.2 hg_lc_ne
  lia

/-- Boundary closure for a right family `g + μ f` when the perturbation has no
higher degree than the base polynomial. The equal-degree case is exactly the
existing positive-combination continuity theorem; the strict case is the new
lower-degree closure lemma above. -/
protected theorem AffineFamily.isRealRooted_of_add_C_mul_right_family_of_natDegree_le
    {f g : ℝ[X]}
    (hfamily : ∀ {μ : ℝ}, 0 < μ → ((g + C μ * f) ≠ 0 ∧ (g + C μ * f).Splits))
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : f.natDegree ≤ g.natDegree) : (g ≠ 0 ∧ g.Splits) := by
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact
      AffineFamily.isRealRooted_of_add_C_mul_right_family_of_natDegree_lt
        hfamily hf_pos hg_pos hlt
  · have hcombo : PosComboRealRooted g f := by
      rw [PosComboRealRooted.iff_add_right]
      grind
    exact
      PosComboRealRooted.isRealRooted_left_of_sameDegree
        (f := g) (g := f) hcombo hg_pos hf_pos heq

/-- In a positive-combination family, if the right summand has degree at least
that of the left summand, then the right summand is real-rooted. -/
theorem PosComboRealRooted.isRealRooted_right_of_natDegree_le {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : f.natDegree ≤ g.natDegree) :
    (g ≠ 0 ∧ g.Splits) :=
  AffineFamily.isRealRooted_of_add_C_mul_right_family_of_natDegree_le
    (fun {_} hμ => PosComboRealRooted.isRealRooted_add_right hfg.comm hμ)
    hf_pos hg_pos hdeg

/-- Symmetric form of
`PosComboRealRooted.isRealRooted_right_of_natDegree_le`. -/
theorem PosComboRealRooted.isRealRooted_left_of_natDegree_le {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree ≤ f.natDegree) :
    (f ≠ 0 ∧ f.Splits) := by
  simpa using
    PosComboRealRooted.isRealRooted_right_of_natDegree_le
      (PosComboRealRooted.comm hfg) hg_pos hf_pos hdeg

/-- In a positive-combination family, if the right summand has degree one more
than the left summand, then the right summand is real-rooted. -/
theorem PosComboRealRooted.isRealRooted_right_of_succDegree {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    (g ≠ 0 ∧ g.Splits) :=
  PosComboRealRooted.isRealRooted_right_of_natDegree_le hfg hf_pos hg_pos (by lia)

/-- In a positive-combination family, if the right summand has degree one more
than the left summand, then the left summand is real-rooted. -/
theorem PosComboRealRooted.isRealRooted_left_of_succDegree {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    (f ≠ 0 ∧ f.Splits) :=
  ⟨hf_pos.ne_zero, hfg.left_splits_of_succDegree hf_pos hg_pos hsucc⟩

/-- If the affine family has enough right-hand degree to dominate the `X * f`
perturbation, then the boundary member `C t * f + g` is already real-rooted.
This is the first compiled reduction from the two-parameter family to the
one-parameter boundary family. -/
protected lemma AffineFamily.isRealRooted_add_left_of_affine_family_of_natDegree_succ_le
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hdeg : f.natDegree + 1 ≤ g.natDegree)
    {t : ℝ} (ht : 0 < t) : ((C t * f + g) ≠ 0 ∧ (C t * f + g).Splits) := by
  obtain ⟨_, _, _, _, _, hsum_pos, hXf_pos⟩ :=
    affine_family_pair_data hfnn hgnn hf0 hg0 haff ht
  have hsum_deg : (C t * f + g).natDegree = g.natDegree := by
    have hCt_deg : (C t * f).natDegree = f.natDegree := by rw [natDegree_C_mul ht.ne']
    exact
      natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
        (by lia)
        (hgnn.pos_leadingCoeff hg0)
  apply AffineFamily.isRealRooted_of_add_C_mul_right_family_of_natDegree_le
  · intro s hs
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, left_distrib, right_distrib] using
      haff hs ht
  · lia
  · lia
  · simp_all

/-- In the degree-dominating branch `deg g ≥ deg f + 1`, the affine-family
hypothesis already forces `g` to be real-rooted by first passing to the
boundary family `C t * f + g` and then taking `t → 0`. -/
private lemma isRealRooted_right_of_affine_family_of_natDegree_succ_le
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hdeg : f.natDegree + 1 ≤ g.natDegree) : (g ≠ 0 ∧ g.Splits) :=
  AffineFamily.isRealRooted_of_add_C_mul_right_family_of_natDegree_le
    (by
      intro t ht
      simpa [add_comm] using
        AffineFamily.isRealRooted_add_left_of_affine_family_of_natDegree_succ_le
          hf0 hg0 hfnn hgnn haff hdeg ht)
    (hfnn.pos_leadingCoeff hf0)
    (hgnn.pos_leadingCoeff hg0)
    (by lia)

private lemma isRealRooted_pair_of_affine_family_succDegree
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hsucc : f.natDegree + 1 = g.natDegree)
    {t : ℝ} (ht : 0 < t) :
    ((C t * f + g) ≠ 0 ∧ (C t * f + g).Splits) ∧
      (f ≠ 0 ∧
      f.Splits) := by
  obtain ⟨hcombo, _, _, _, _, hsum_pos, hXf_pos⟩ :=
    affine_family_pair_data hfnn hgnn hf0 hg0 haff ht
  have hsum_deg : (C t * f + g).natDegree = g.natDegree := by
    have hCt_deg : (C t * f).natDegree = f.natDegree := by rw [natDegree_C_mul ht.ne']
    exact
      natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
        (by lia)
        (hgnn.pos_leadingCoeff hg0)
  have hXf_deg : (X * f).natDegree = g.natDegree := by simp_all
  have hdeg_same : (X * f).natDegree = (C t * f + g).natDegree := by lia
  have hsum_rr : ((C t * f + g) ≠ 0 ∧ (C t * f + g).Splits) :=
    PosComboRealRooted.isRealRooted_left_of_sameDegree
      hcombo hsum_pos hXf_pos hdeg_same
  have hXf_rr : ((X * f) ≠ 0 ∧ (X * f).Splits) :=
    PosComboRealRooted.isRealRooted_right_of_sameDegree
      hcombo hsum_pos hXf_pos hdeg_same
  exact ⟨hsum_rr, isRealRooted_of_X_mul hXf_rr.1 hXf_rr.2⟩

protected lemma AffineFamily.isRealRooted_right_of_affine_family_succDegree
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hsucc : f.natDegree + 1 = g.natDegree) : (g ≠ 0 ∧ g.Splits) :=
  isRealRooted_right_of_affine_family_of_natDegree_succ_le
    hf0 hg0 hfnn hgnn haff (by lia)

/-- Fix `s > 0`. Passing `t → 0` in the affine family shows that the boundary
member `g + s X f` is already real-rooted. This is the natural right-family
companion to `AffineFamily.isRealRooted_add_left_of_affine_family_of_natDegree_succ_le`,
but unlike that lemma it does not require any a priori degree comparison: the
`X * f` term always raises the left degree by one, so the boundary family is
automatically at least as large as `f` itself. -/
private lemma isRealRooted_add_X_mul_right_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    {s : ℝ} (hs : 0 < s) : ((g + C s * (X * f)) ≠ 0 ∧ (g + C s * (X * f)).Splits) := by
  have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hf0
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  have hXf_nonneg : HasNonnegCoeffs (X * f) := hfnn.X_mul
  have hXf_ne : X * f ≠ 0 := mul_ne_zero X_ne_zero hf0
  have hCsXf_nonneg : HasNonnegCoeffs (C s * (X * f)) :=
    nonnegCoeffs_C_mul hs.le hXf_nonneg
  have hCsXf_ne : C s * (X * f) ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hs.ne') hXf_ne
  have hbase_nonneg : HasNonnegCoeffs (g + C s * (X * f)) :=
    hgnn.add hCsXf_nonneg
  have hbase_ne : g + C s * (X * f) ≠ 0 :=
    add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hgnn hCsXf_nonneg hCsXf_ne
  have hXf_pos : HasPosLeadingCoeff (X * f) := hf_pos.X_mul
  have hCsXf_pos : HasPosLeadingCoeff (C s * (X * f)) :=
    hasPosLeadingCoeff_C_mul hs hXf_pos
  have hbase_pos : HasPosLeadingCoeff (g + C s * (X * f)) := by
    rcases lt_trichotomy g.natDegree (X * f).natDegree with hdeg | hdeg | hdeg
    · have hdeg' : g.natDegree < (C s * (X * f)).natDegree := by
        simpa [natDegree_C_mul hs.ne'] using hdeg
      exact hasPosLeadingCoeff_add_of_natDegree_lt_right hdeg' hCsXf_pos
    · have hdeg' : g.natDegree = (C s * (X * f)).natDegree := by
        simpa [natDegree_C_mul hs.ne'] using hdeg
      exact hasPosLeadingCoeff_add_of_same_natDegree hdeg' hg_pos hCsXf_pos
    · have hdeg' : (C s * (X * f)).natDegree < g.natDegree := by
        simpa [natDegree_C_mul hs.ne'] using hdeg
      exact hasPosLeadingCoeff_add_of_natDegree_lt_left hdeg' hg_pos
  have hbase_deg : f.natDegree ≤ (g + C s * (X * f)).natDegree := by
    rcases lt_trichotomy g.natDegree (X * f).natDegree with hdeg | hdeg | hdeg
    · have hsum_deg : (g + C s * (X * f)).natDegree = (C s * (X * f)).natDegree :=
        natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
          (by simpa [natDegree_C_mul hs.ne'] using hdeg) hCsXf_pos
      rw [hsum_deg, natDegree_C_mul hs.ne', natDegree_mul X_ne_zero hf0, natDegree_X]
      lia
    · have hsum_deg : (g + C s * (X * f)).natDegree = g.natDegree :=
        natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
          (by simpa [natDegree_C_mul hs.ne'] using hdeg) hg_pos hCsXf_pos
      simp_all
    · have hsum_deg : (g + C s * (X * f)).natDegree = g.natDegree :=
        natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff
          (by simpa [natDegree_C_mul hs.ne'] using hdeg) hg_pos
      rw [hsum_deg]
      have hXf_deg : (X * f).natDegree = f.natDegree + 1 := by simp_all
      lia
  apply AffineFamily.isRealRooted_of_add_C_mul_right_family_of_natDegree_le
  · intro t ht
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, left_distrib, right_distrib] using
      haff hs ht
  all_goals lia

/-- The affine-family hypothesis already implies that the fixed right-hand pair
`(g, X * f)` satisfies the restricted Obreschkoff condition: every strictly
positive combination `g + μ X f` is real-rooted. This is the honest boundary
package that remains after the earlier `t → 0` refactor. -/
protected lemma AffineFamily.posComboRealRooted_right_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    PosComboRealRooted g (X * f) := by
  refine PosComboRealRooted.of_add_right ?_
  intro s hs
  exact
    isRealRooted_add_X_mul_right_of_affine_family
      hf0 hg0 hfnn hgnn haff hs

/-- Data package for the fixed right-hand pair `(g, X * f)` extracted from the
affine family after taking the boundary `t → 0`. This is the natural target
pair for the eventual Wagner step `Prec g (X * f) → Prec f g`. -/
protected lemma AffineFamily.affine_family_right_pair_data {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    PosComboRealRooted g (X * f) ∧
    HasNonnegCoeffs g ∧
    HasNonnegCoeffs (X * f) ∧
    g ≠ 0 ∧
    X * f ≠ 0 ∧
    HasPosLeadingCoeff g ∧
    HasPosLeadingCoeff (X * f) := by
  have hXf_nonneg : HasNonnegCoeffs (X * f) := hfnn.X_mul
  have hXf_ne : X * f ≠ 0 := mul_ne_zero X_ne_zero hf0
  refine
    ⟨AffineFamily.posComboRealRooted_right_of_affine_family hf0 hg0 hfnn hgnn haff,
      hgnn, hXf_nonneg, hg0, hXf_ne,
      hgnn.pos_leadingCoeff hg0, (hfnn.pos_leadingCoeff hf0).X_mul⟩

/-! ## Degree control for the affine family

Before trying to orient the fixed right-hand pair `(g, X * f)`, it is useful to
rule out the large-gap regime `deg g ≥ deg f + 2`. The affine hypothesis gives
real-rootedness of every boundary member `C t * f + g` with `t > 0`; after
differentiating `deg f` times, this would force a positive constant-vs-degree-`≥ 2`
positive family, which is impossible.  This is the affine analogue of the
degree-closeness reduction already used in `ObreschkoffConverse`. -/

private lemma iterate_derivative_add :
    ∀ (n : ℕ) (p q : ℝ[X]),
      (derivative^[n]) (p + q) = (derivative^[n]) p + (derivative^[n]) q
  | 0, p, q => by simp
  | n + 1, p, q => by
      simp

private lemma iterate_derivative_C_mul (a : ℝ) :
    ∀ (n : ℕ) (p : ℝ[X]),
      (derivative^[n]) (C a * p) = C a * (derivative^[n]) p
  | 0, p => by simp
  | n + 1, p => by
      simp
protected lemma AffineFamily.isRealRooted_iterate_derivative_of_lt_natDegree
    {p : ℝ[X]} (hp_ne : p ≠ 0) (hp_splits : p.Splits) :
    ∀ {n : ℕ}, n < p.natDegree → (((derivative^[n]) p) ≠ 0 ∧ ((derivative^[n]) p).Splits)
  | 0, _ => by simp_all
  | n + 1, hn => by
      rw [Function.iterate_succ_apply']
      have hprev : (((derivative^[n]) p) ≠ 0 ∧ ((derivative^[n]) p).Splits) :=
        AffineFamily.isRealRooted_iterate_derivative_of_lt_natDegree
          hp_ne hp_splits (Nat.lt_of_succ_lt hn)
      have hnonzero :
          derivative ((derivative^[n]) p) ≠ 0 := by
        simpa [Function.iterate_succ_apply'] using
          (iterate_derivative_ne_zero_of_le_natDegree
            (p := p) (k := n + 1) hp_ne (Nat.le_of_lt hn))
      exact
        (derivative_eq_zero_or_ne_zero_and_splits hprev.2).elim
          (fun h0 => False.elim (hnonzero h0))
          id

/-- Packaged same-degree rightmost-factor reduction for later sign arguments:
from `Prec f g`, choose the rightmost root of `g`, factor it off, and retain a
genuine differ-by-1 `Interlaces` witness for the quotient against `f`, together
with the explicit rightmost-root bound. -/
theorem exists_rightmost_factor_interlaces_of_prec_sameDegree
    {f g : ℝ[X]}
    (hprec : Prec f g)
    (hdeg : f.natDegree = g.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree) :
    ∃ uR q,
      g = (X - C uR) * q ∧
      g.IsRoot uR ∧
      (∀ r ∈ g.roots, r ≤ uR) ∧
      Interlaces q f := by
  have hprec_keep : Prec f g := hprec
  obtain ⟨_, hg, _, _, _, _, _, _, _⟩ := hprec
  obtain ⟨uR, huR_root, huR_max⟩ :=
    exists_rightmost_root_of_isRealRooted hg.1 hg.2 hdeg_pos
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr huR_root
  exact
    ⟨uR, q, hq, huR_root, huR_max,
      interlaces_of_prec_sameDegree_rightmost_factor
        (f := f) (g := g) (q := q) (uR := uR)
        hprec_keep hdeg huR_max hq⟩

private lemma exists_strict_root_upper_bound_of_nonneg_of_not_isRoot_zero
    {p : ℝ[X]}
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p)
    (hnot0 : ¬ p.IsRoot 0) :
    ∃ c, (∀ r ∈ p.roots, r ≤ c) ∧ c < 0 := by
  by_cases hdeg0 : p.natDegree = 0
  · refine ⟨-1, ?_, by simp⟩
    intro r hr
    have hroots0 : p.roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [card_roots_of_splits hp_splits, hdeg0]
    simp_all
  · have hdeg_pos : 1 ≤ p.natDegree := by lia
    obtain ⟨c, hc_root, hc_top⟩ :=
      exists_rightmost_root_of_isRealRooted hp_ne hp_splits hdeg_pos
    have hc_le0 : c ≤ 0 :=
      roots_nonpos_of_nonneg_coeffs hp_splits hpnn c ((mem_roots hp_ne).mpr hc_root)
    have hc_ne0 : c ≠ 0 := by lia
    exact ⟨c, hc_top, lt_of_le_of_ne hc_le0 hc_ne0⟩

/-- A nonzero root of `X * f` is already a root of `f`. -/
lemma isRoot_of_X_mul_of_ne_zero
    {f : ℝ[X]} {r : ℝ}
    (hr : r ≠ 0) (hX : (X * f).IsRoot r) :
    f.IsRoot r := by
  simp_all

/-- If `g` has no common root with `f` and `0` is not a root of `g`, then `g`
has no common root with `X * f`. -/
theorem no_common_right_pair_of_no_common_of_not_isRoot_zero
    {f g : ℝ[X]}
    (hno_fg : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg0 : ¬ g.IsRoot 0) :
    ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r := by
  intro r hgr hXr
  simp_all

private lemma eq_zero_of_common_right_pair_of_no_common
    {f g : ℝ[X]} {r : ℝ}
    (hno_fg : ∀ x, g.IsRoot x → ¬ f.IsRoot x)
    (hgr : g.IsRoot r) (hXr : (X * f).IsRoot r) :
    r = 0 := by
  simp_all

/-- Common roots of the right pair `(g, X * f)` are exactly the zero root of
`g` or common roots of `(g, f)`. -/
theorem common_right_pair_iff_root_zero_or_common_fg
    {f g : ℝ[X]} :
    (∃ r, g.IsRoot r ∧ (X * f).IsRoot r) ↔
      g.IsRoot 0 ∨ ∃ r, g.IsRoot r ∧ f.IsRoot r := by
  constructor
  · intro h
    rcases h with ⟨r, hgr, hXr⟩
    by_cases hr0 : r = 0
    · lia
    · right
      exact ⟨r, hgr, isRoot_of_X_mul_of_ne_zero hr0 hXr⟩
  · intro h
    rcases h with hg0 | hcommon
    · exact ⟨0, hg0, by simp [Polynomial.IsRoot.def]⟩
    · rcases hcommon with ⟨r, hgr, hfr⟩
      refine ⟨r, hgr, ?_⟩
      simp_all

private lemma no_common_of_right_pair_root_zero_reduction
    {f g qg : ℝ[X]}
    (hg : g = X * qg)
    (hno_fg : ∀ r, g.IsRoot r → ¬ f.IsRoot r) :
    ∀ r, qg.IsRoot r → ¬ f.IsRoot r := by
  simp_all

/-- If `g` has nonnegative coefficients and no common root with `X * f`, then
every real root of `g` is strictly negative. -/
theorem roots_strictly_neg_of_nonneg_of_no_common_right_pair
    {f g : ℝ[X]}
    (hg_ne : g ≠ 0) (hg_splits : g.Splits) (hgnn : HasNonnegCoeffs g)
    (hno : ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r) :
    ∀ r ∈ g.roots, r < 0 := by
  intro r hr
  have hr_le : r ≤ 0 := roots_nonpos_of_nonneg_coeffs hg_splits hgnn r hr
  have hr_root : g.IsRoot r := (mem_roots hg_ne).mp hr
  have hr_ne : r ≠ 0 := by simp_all
  grind

/-- The distinguished root `0` of `X * f` lies strictly to the right of every
root of `g` when `g` is nonnegative and has no common root with `X * f`. -/
theorem exists_strict_right_root_of_X_mul_of_no_common
    {f g : ℝ[X]}
    (hg_ne : g ≠ 0) (hg_splits : g.Splits) (hgnn : HasNonnegCoeffs g)
    (hno : ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r) :
    ∃ uR, (X * f).IsRoot uR ∧ ∀ r ∈ g.roots, r < uR := by
  refine ⟨0, by simp [Polynomial.IsRoot.def], ?_⟩
  intro r hr
  exact roots_strictly_neg_of_nonneg_of_no_common_right_pair hg_ne hg_splits hgnn hno r hr

/-- Convenience form of `exists_strict_right_root_of_X_mul_of_no_common` from
no common roots of `(g, f)` and `¬ g.IsRoot 0`. -/
theorem exists_strict_right_root_of_X_mul_of_no_common_fg_of_not_isRoot_zero
    {f g : ℝ[X]}
    (hg_ne : g ≠ 0) (hg_splits : g.Splits) (hgnn : HasNonnegCoeffs g)
    (hno_fg : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg0 : ¬ g.IsRoot 0) :
    ∃ uR, (X * f).IsRoot uR ∧ ∀ r ∈ g.roots, r < uR :=
  exists_strict_right_root_of_X_mul_of_no_common hg_ne hg_splits hgnn
    (no_common_right_pair_of_no_common_of_not_isRoot_zero hno_fg hg0)

/-- In the no-common-roots regime for the affine right-hand pair `(g, X * f)`,
any future Obreschkoff alternative is automatically oriented the correct way:
the distinguished root `0` of `X * f` sits strictly to the right of all roots
of `g`. -/
private lemma prec_right_pair_of_prec_or_revPrec_of_no_common
    {f g : ℝ[X]}
    (h : Prec g (X * f) ∨ Prec (X * f) g)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits) (hgnn : HasNonnegCoeffs g)
    (hno : ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r) :
    Prec g (X * f) := by
  obtain ⟨c, hc_le, hc_lt0⟩ :=
    exists_strict_root_upper_bound_of_nonneg_of_not_isRoot_zero hg_ne hg_splits hgnn (by
      intro hg0
      exact hno 0 hg0 (by simp [Polynomial.IsRoot.def]))
  exact
    PosComboRealRooted.revPrec_of_prec_or_revPrec_of_root_asymmetry
      (f := g) (g := X * f) (c := c) (r := 0)
      h hc_le (by simp [Polynomial.IsRoot.def]) (by lia)

/-- Orientation wrapper for the affine right pair under no-common `f/g` and
`g(0) ≠ 0`: once an Obreschkoff alternative for `(g, X*f)` is available, the
right direction is forced. -/
private lemma prec_right_pair_of_prec_or_revPrec_of_no_common_fg_of_not_isRoot_zero
    {f g : ℝ[X]}
    (h : Prec g (X * f) ∨ Prec (X * f) g)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits) (hgnn : HasNonnegCoeffs g)
    (hno_fg : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg0 : ¬ g.IsRoot 0) :
    Prec g (X * f) :=
  prec_right_pair_of_prec_or_revPrec_of_no_common h hg_ne hg_splits hgnn
    (no_common_right_pair_of_no_common_of_not_isRoot_zero hno_fg hg0)

/-- Public orientation selector for the right-hand pair `(g, X * f)` in the
nonnegative-coefficient regime: if an Obreschkoff alternative is known and the
pair has no common root, then the distinguished root `0` of `X * f` forces the
orientation `g ≺ X * f`. -/
theorem prec_right_pair_of_prec_or_revPrec_of_no_common_nonneg
    {f g : ℝ[X]}
    (h : Prec g (X * f) ∨ Prec (X * f) g)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits) (hgnn : HasNonnegCoeffs g)
    (hno : ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r) :
    Prec g (X * f) :=
  prec_right_pair_of_prec_or_revPrec_of_no_common h hg_ne hg_splits hgnn hno

end RealRooted
