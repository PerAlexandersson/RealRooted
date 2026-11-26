/-
# Affine-family criterion for interlacing

Has2x2InterlacingProperty definition, affine-family criterion
(Brändén Lemma 7.8.4), bridge from combo results to StrictInterl.
The remaining live theorem here is `strictInterl_of_affine_family_nonneg`.
-/
module

public import RealRooted.ProductFamily
public import RealRooted.AffineDerivative
public import RealRooted.AffineFamily.Basic
public import RealRooted.AffineFamily.PositiveFamily
public import RealRooted.AffineFamily.Boundary
public import RealRooted.AffineFamily.LowDegree
public import RealRooted.AffineFamily.RootCrossing
public import RealRooted.AffineFamily.Wronskian
import RealRooted.PosCombo
public import RealRooted.SuccDegreeLeftEndpoint
public import RealRooted.ObreschkoffConverse
import RealRooted.FolkloreLemma
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import RealRooted.ObreschkoffConverse.Derivative
import RealRooted.ObreschkoffConverse.Forward
import RealRooted.ObreschkoffConverse.Converse
import RealRooted.WagnerX.AffineFactors
import RealRooted.Derivative.Interlacing
import RealRooted.Linear
public import RealRooted.AissenSchoenbergWhitneyBase
import RealRooted.Basic.PolynomialFacts

public section

open Polynomial

noncomputable section

namespace RealRooted

private lemma affine_family_common_root_reduction_data
    {f g : ℝ[X]} {r : ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hrf : f.IsRoot r) (hrg : g.IsRoot r) :
    ∃ qf qg,
      f = (X - C r) * qf ∧
      g = (X - C r) * qg ∧
      HasNonnegCoeffs qf ∧
      HasNonnegCoeffs qg ∧
      qf ≠ 0 ∧
      qg ≠ 0 ∧
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * qf) + qg) ≠ 0 ∧ (((C s * X + C t) * qf) + qg).Splits) := by
  obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hrf
  obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hrg
  have hqf_ne : qf ≠ 0 := by grind
  have hqg_ne : qg ≠ 0 := by grind
  have hqf_rr : (qf ≠ 0 ∧ qf.Splits) :=
    isRealRooted_of_dvd hf_ne hf_splits hqf_ne ⟨X - C r, by grind⟩
  have hqg_rr : (qg ≠ 0 ∧ qg.Splits) :=
    isRealRooted_of_dvd hg_ne hg_splits hqg_ne ⟨X - C r, by grind⟩
  have hqf_pos : HasPosLeadingCoeff qf :=
    hasPosLeadingCoeff_of_X_sub_C_mul (by simpa [hqf] using hfnn.pos_leadingCoeff hf_ne)
  have hqg_pos : HasPosLeadingCoeff qg :=
    hasPosLeadingCoeff_of_X_sub_C_mul (by simpa [hqg] using hgnn.pos_leadingCoeff hg_ne)
  have hqf_nonneg : HasNonnegCoeffs qf :=
    hasNonnegCoeffs_of_dvd_of_hasPosLeadingCoeff
      hf_ne hfnn hqf_ne hqf_rr.2 hqf_pos ⟨X - C r, by grind⟩
  have hqg_nonneg : HasNonnegCoeffs qg :=
    hasNonnegCoeffs_of_dvd_of_hasPosLeadingCoeff
      hg_ne hgnn hqg_ne hqg_rr.2 hqg_pos ⟨X - C r, by grind⟩
  refine ⟨qf, qg, hqf, hqg, hqf_nonneg, hqg_nonneg, hqf_ne, hqg_ne, ?_⟩
  intro s t hs ht
  have hbase := haff hs ht
  have hfactor : (C s * X + C t) * f + g =
      (X - C r) * ((C s * X + C t) * qf + qg) := by
    rw [hqf, hqg]
    ring
  rw [hfactor] at hbase
  exact ⟨right_ne_zero_of_mul hbase.1, splits_X_sub_C_mul_iff.mp hbase.2⟩

private lemma natDegree_shifted_pair_eq_succ_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    (g + X * f).natDegree = f.natDegree + 1 := by
  have hdeg_right : g.natDegree ≤ f.natDegree + 1 :=
    AffineFamily.natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
  have hXf_pos : HasPosLeadingCoeff (X * f) :=
    (hfnn.pos_leadingCoeff hf0).X_mul
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  rcases lt_or_eq_of_le hdeg_right with hlt | heq
  · have hg_lt : g.natDegree < (X * f).natDegree := by simp_all
    have hsum_deg : (g + X * f).natDegree = (X * f).natDegree :=
      Polynomial.natDegree_add_eq_right_of_natDegree_lt hg_lt
    simp_all
  · have hg_eq : g.natDegree = (X * f).natDegree := by simp_all
    have hsum_deg : (g + X * f).natDegree = (X * f).natDegree :=
      natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
        hg_eq hg_pos hXf_pos |>.trans hg_eq
    lia

private lemma strictInterl_of_strictInterl_shifted_pair_sameDegree
    {f g : ℝ[X]}
    (h : StrictInterl f (g + X * f))
    (hf0 : f ≠ 0)
    (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : g.natDegree = f.natDegree) :
    StrictInterl f g := by
  have hshift_deg : (g + X * f).natDegree = f.natDegree + 1 := by
    have hXf : (X * f).natDegree = f.natDegree + 1 := by simp [hf0]
    rw [natDegree_add_eq_right_of_natDegree_lt (by lia), hXf]
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hshift_lc : (g + X * f).leadingCoeff = f.leadingCoeff := by
    rw [leadingCoeff, hshift_deg, coeff_add, coeff_X_mul,
      coeff_eq_zero_of_natDegree_lt (by lia), zero_add, coeff_natDegree]
  let a := f.leadingCoeff⁻¹
  have ha : a ≠ 0 := inv_ne_zero hlc
  have hf_monic : (C a * f).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
  have hshift_monic : (C a * (g + X * f)).Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [hshift_lc]
    exact inv_mul_cancel₀ hlc
  have hscaled := (h.C_mul_left ha).C_mul_right ha
  have hinterl := strictInterl_sub_X_mul_right hscaled hshift_monic hf_monic
    (by simp only [natDegree_C_mul ha, hshift_deg])
    (by simpa only [roots_C_mul _ ha] using
      roots_nonpos_of_hasNonnegCoeffs (hgnn.add hfnn.X_mul))
    (by simpa only [roots_C_mul _ ha] using roots_nonpos_of_hasNonnegCoeffs hfnn)
  have hsub : C a * (g + X * f) - X * (C a * f) = C a * g := by ring
  rw [hsub] at hinterl
  have hstrict := hinterl.toStrictInterl_of_ne
    (mul_ne_zero (C_ne_zero.mpr ha) hf0) (mul_ne_zero (C_ne_zero.mpr ha) hg0)
  simpa only [← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul] using
    (hstrict.C_mul_left (inv_ne_zero ha)).C_mul_right (inv_ne_zero ha)

private lemma strictInterl_right_pair_of_strictInterl_shifted_pair_sameDegree
    {f g : ℝ[X]}
    (h : StrictInterl f (g + X * f))
    (hf0 : f ≠ 0)
    (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : g.natDegree = f.natDegree) :
    StrictInterl g (X * f) :=
  strictInterl_mul_X_of_strictInterl_of_nonneg
    (strictInterl_of_strictInterl_shifted_pair_sameDegree h hf0 hg0 hfnn hgnn hdeg)
    hfnn hgnn

private lemma shifted_affine_family_of_affine_family
    {f g : ℝ[X]}
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    ∀ {s t : ℝ}, 0 < s → 0 < t →
      ((((C s * X + C t) * f) + (g + X * f)) ≠ 0 ∧
        (((C s * X + C t) * f) + (g + X * f)).Splits) := by
  intro s t hs ht
  have hbase :
      ((((C (s + 1) * X + C t) * f) + g) ≠ 0 ∧ (((C (s + 1) * X + C t) * f) + g).Splits) :=
    haff (by grind) ht
  grind

/-- The successor-degree converse reduces both common-root factors by induction,
then uses the all-combinations criterion for the coprime pair. -/
private lemma strictInterl_of_affine_family_succ
    {f g : ℝ[X]} (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (haff : ∀ {s t : ℝ}, 0 < s → 0 < t →
      ((C s * X + C t) * f + g) ≠ 0 ∧ ((C s * X + C t) * f + g).Splits)
    (hsucc : g.natDegree = f.natDegree + 1) : StrictInterl f g := by
  generalize hn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f g with
  | ind n ih =>
      have hXf := AffineFamily.isRealRooted_X_mul_of_affine_family
        hf0 hg0 hfnn hgnn haff
      have hf := isRealRooted_of_X_mul hXf.1 hXf.2
      have hg := AffineFamily.isRealRooted_right_of_affine_family_succDegree
        hf0 hg0 hfnn hgnn haff hsucc.symm
      by_cases hcommon : ∃ r, f.IsRoot r ∧ g.IsRoot r
      · obtain ⟨r, hfr, hgr⟩ := hcommon
        obtain ⟨qf, qg, hqf, hqg, hqfnn, hqgnn, hqf0, hqg0, hqaff⟩ :=
          affine_family_common_root_reduction_data hf0 hf.2 hg0 hg.2 hfnn hgnn
            haff hfr hgr
        have hdegree : f.natDegree = qf.natDegree + 1 := by
          rw [hqf, natDegree_mul (X_sub_C_ne_zero r) hqf0, natDegree_X_sub_C]
          lia
        have hqsucc : qg.natDegree = qf.natDegree + 1 := by
          rw [hqg, natDegree_mul (X_sub_C_ne_zero r) hqg0, natDegree_X_sub_C] at hsucc
          lia
        have hq := ih qf.natDegree (by lia) hqf0 hqg0 hqfnn hqgnn hqaff hqsucc rfl
        rw [hqf, hqg]
        exact hq.mul_common_factor (X_sub_C_ne_zero r) (.X_sub_C r)
      · have hall := AffineFamily.allComboRealRooted_of_affine_family_succDegree
          hf0 hg0 hfnn hgnn haff hXf hsucc (by grind)
        exact StrictInterl.forward_of_orientation_of_succDegree hsucc
          (strictInterl_of_allComboRealRooted hf0 hf.2 hg0 hg.2 hall.comm
            (Or.inl hsucc.symm))

/-- Converse affine-family step used in Brändén 7.8.5:
if all positive affine combinations `((C s * X + C t) * f) + g` are real-rooted
and both `f, g` are nonzero with nonnegative coefficients, then `f ≪ g`.

This is exactly the remaining local blocker in the forward matrix argument. -/
theorem strictInterl_of_affine_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    :
    StrictInterl f g := by
  rcases AffineFamily.natDegree_cases_of_affine_family hf0 hg0 hfnn hgnn haff with
    hsame | hsucc
  · have hshift_nn := hgnn.add hfnn.X_mul
    have hshift_ne := add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
      hgnn hfnn.X_mul (mul_ne_zero X_ne_zero hf0)
    exact strictInterl_of_strictInterl_shifted_pair_sameDegree
      (strictInterl_of_affine_family_succ hf0 hshift_ne hfnn hshift_nn
        (shifted_affine_family_of_affine_family haff)
        (natDegree_shifted_pair_eq_succ_of_affine_family hf0 hg0 hfnn hgnn haff))
      hf0 hg0 hfnn hgnn hsame
  · exact strictInterl_of_affine_family_succ hf0 hg0 hfnn hgnn haff hsucc

/-- Right-pair form of the affine-family converse. This is the degree-free
public API: the affine-family hypothesis gives `f ≪ g`, and nonnegative
coefficients transport this to `g ≪ X * f`. -/
theorem strictInterl_right_pair_of_affine_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    StrictInterl g (X * f) :=
  strictInterl_mul_X_of_strictInterl_of_nonneg
    (strictInterl_of_affine_family_nonneg hf0 hg0 hfnn hgnn haff)
    hfnn hgnn

/-- Closed affine-segment wrapper for `strictInterl_of_affine_family_nonneg`.

For each positive affine factor `sX+t`, assume the two endpoint polynomials
`(sX+t)P0+H0` and `(sX+t)P1+H1` are positively compatible, and assume the
endpoints themselves are real-rooted.  Then every convex interpolation
`Pβ=(1-β)P0+βP1`, `Hβ=(1-β)H0+βH1` satisfies `Pβ ≪ Hβ`, provided the
usual nonzero and nonnegative-coefficient hypotheses for Branden's affine
criterion hold. -/
theorem strictInterl_of_affine_segment_endpoints_nonneg
    {P0 P1 H0 H1 : ℝ[X]} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hPβ0 : C (1 - β) * P0 + C β * P1 ≠ 0)
    (hHβ0 : C (1 - β) * H0 + C β * H1 ≠ 0)
    (hPβnn : HasNonnegCoeffs (C (1 - β) * P0 + C β * P1))
    (hHβnn : HasNonnegCoeffs (C (1 - β) * H0 + C β * H1))
    (hendpoint :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        PosComboRealRooted
          (((C s * X + C t) * P0) + H0)
          (((C s * X + C t) * P1) + H1))
    (hleft :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * P0) + H0) ≠ 0 ∧ (((C s * X + C t) * P0) + H0).Splits))
    (hright :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * P1) + H1) ≠ 0 ∧ (((C s * X + C t) * P1) + H1).Splits)) :
    StrictInterl (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) := by
  refine strictInterl_of_affine_family_nonneg hPβ0 hHβ0 hPβnn hHβnn ?_
  intro s t hs ht
  have hseg :
      ((C (1 - β) * (((C s * X + C t) * P0) + H0) +
          C β * (((C s * X + C t) * P1) + H1)) ≠ 0 ∧
        (C (1 - β) * (((C s * X + C t) * P0) + H0) +
            C β * (((C s * X + C t) * P1) + H1)).Splits) :=
    PosComboRealRooted.isRealRooted_closed_segment
      (hendpoint hs ht) (hleft hs ht).1 (hleft hs ht).2 (hright hs ht).1 (hright hs ht).2 hβ0 hβ1
  grind

/-- Variant of `strictInterl_of_affine_segment_endpoints_nonneg` where endpoint
real-rootedness is recovered from positive-combination real-rootedness plus
equal degree and positive leading coefficients at every affine specialization. -/
theorem strictInterl_of_affine_segment_endpoints_sameDegree_nonneg
    {P0 P1 H0 H1 : ℝ[X]} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hPβ0 : C (1 - β) * P0 + C β * P1 ≠ 0)
    (hHβ0 : C (1 - β) * H0 + C β * H1 ≠ 0)
    (hPβnn : HasNonnegCoeffs (C (1 - β) * P0 + C β * P1))
    (hHβnn : HasNonnegCoeffs (C (1 - β) * H0 + C β * H1))
    (hendpoint :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        PosComboRealRooted
          (((C s * X + C t) * P0) + H0)
          (((C s * X + C t) * P1) + H1))
    (hleft_pos :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        HasPosLeadingCoeff (((C s * X + C t) * P0) + H0))
    (hright_pos :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        HasPosLeadingCoeff (((C s * X + C t) * P1) + H1))
    (hdeg :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        (((C s * X + C t) * P1) + H1).natDegree =
          (((C s * X + C t) * P0) + H0).natDegree) :
    StrictInterl (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) := by
  refine strictInterl_of_affine_family_nonneg hPβ0 hHβ0 hPβnn hHβnn ?_
  intro s t hs ht
  have hseg :
      ((C (1 - β) * (((C s * X + C t) * P0) + H0) +
          C β * (((C s * X + C t) * P1) + H1)) ≠ 0 ∧
        (C (1 - β) * (((C s * X + C t) * P0) + H0) +
            C β * (((C s * X + C t) * P1) + H1)).Splits) :=
    PosComboRealRooted.isRealRooted_closed_segment_of_sameDegree
      (hendpoint hs ht) (hleft_pos hs ht) (hright_pos hs ht) (hdeg hs ht) hβ0 hβ1
  grind

/--
ASW/PF version of `strictInterl_of_affine_segment_endpoints_nonneg`.

For every positive affine factor `sX+t`, it is enough to prove Polya-frequency
for the coefficient sequence of each nonzero endpoint pencil `F0 + z F1`,
`z>=0`. ASW turns this Toeplitz-total-nonnegativity input into endpoint
`PosComboRealRooted`; the preceding affine-segment wrapper then gives the
directed segment relation.
-/
theorem strictInterl_of_affine_segment_endpoint_pf_nonneg
    {P0 P1 H0 H1 : ℝ[X]} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hPβ0 : C (1 - β) * P0 + C β * P1 ≠ 0)
    (hHβ0 : C (1 - β) * H0 + C β * H1 ≠ 0)
    (hPβnn : HasNonnegCoeffs (C (1 - β) * P0 + C β * P1))
    (hHβnn : HasNonnegCoeffs (C (1 - β) * H0 + C β * H1))
    (hpencil_ne :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        ((((C s * X + C t) * P0) + H0) +
          C z * (((C s * X + C t) * P1) + H1)) ≠ 0)
    (hpencil_pf :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        IsPolyaFreqSeq
          (fun n =>
            ((((C s * X + C t) * P0) + H0) +
              C z * (((C s * X + C t) * P1) + H1)).coeff n))
    (hleft :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * P0) + H0) ≠ 0 ∧ (((C s * X + C t) * P0) + H0).Splits))
    (hright :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * P1) + H1) ≠ 0 ∧ (((C s * X + C t) * P1) + H1).Splits)) :
    StrictInterl (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) := by
  refine strictInterl_of_affine_segment_endpoints_nonneg hβ0 hβ1 hPβ0 hHβ0 hPβnn hHβnn ?_
    hleft hright
  intro s t hs ht
  exact PosComboRealRooted.of_aissenSchoenbergWhitney_right_pencil
    (f := (((C s * X + C t) * P0) + H0))
    (g := (((C s * X + C t) * P1) + H1))
    (fun {z} hz => hpencil_ne hs ht hz)
    (fun {z} hz => hpencil_pf hs ht hz)

/--
Same-degree ASW/PF endpoint wrapper.  This is the version to use when endpoint
real-rootedness should be recovered from positive compatibility plus equal
degree and positive leading coefficients.
-/
theorem strictInterl_of_affine_segment_endpoint_pf_sameDegree_nonneg
    {P0 P1 H0 H1 : ℝ[X]} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hPβ0 : C (1 - β) * P0 + C β * P1 ≠ 0)
    (hHβ0 : C (1 - β) * H0 + C β * H1 ≠ 0)
    (hPβnn : HasNonnegCoeffs (C (1 - β) * P0 + C β * P1))
    (hHβnn : HasNonnegCoeffs (C (1 - β) * H0 + C β * H1))
    (hpencil_ne :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        ((((C s * X + C t) * P0) + H0) +
          C z * (((C s * X + C t) * P1) + H1)) ≠ 0)
    (hpencil_pf :
      ∀ {s t z : ℝ}, 0 < s → 0 < t → 0 ≤ z →
        IsPolyaFreqSeq
          (fun n =>
            ((((C s * X + C t) * P0) + H0) +
              C z * (((C s * X + C t) * P1) + H1)).coeff n))
    (hleft_pos :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        HasPosLeadingCoeff (((C s * X + C t) * P0) + H0))
    (hright_pos :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        HasPosLeadingCoeff (((C s * X + C t) * P1) + H1))
    (hdeg :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        (((C s * X + C t) * P1) + H1).natDegree =
          (((C s * X + C t) * P0) + H0).natDegree) :
    StrictInterl (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) := by
  refine strictInterl_of_affine_segment_endpoints_sameDegree_nonneg hβ0 hβ1 hPβ0 hHβ0 hPβnn
    hHβnn ?_ hleft_pos hright_pos hdeg
  intro s t hs ht
  exact PosComboRealRooted.of_aissenSchoenbergWhitney_right_pencil
    (f := (((C s * X + C t) * P0) + H0))
    (g := (((C s * X + C t) * P1) + H1))
    (fun {z} hz => hpencil_ne hs ht hz)
    (fun {z} hz => hpencil_pf hs ht hz)

/-- Branden's affine-family converse immediately upgrades to the full
Obreschkoff all-combinations conclusion in the nonnegative-coefficient regime:
once `strictInterl_of_affine_family_nonneg` gives `f ≪ g`, every real linear
combination of `f` and `g` is real-rooted. -/
theorem allComboRealRooted_of_affine_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_strictInterl
    (strictInterl_of_affine_family_nonneg hf0 hg0 hfnn hgnn haff)

/-- A nonnegative affine family already orients the shifted pair:
`f ≺ g + X * f`. This is the public corrected replacement for the earlier
false attempt to orient every boundary pair `(C t * f + g, X * f)`. -/
theorem strictInterl_shifted_pair_of_affine_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    StrictInterl f (g + X * f) := by
  have hshift_nonneg : HasNonnegCoeffs (g + X * f) :=
    hgnn.add hfnn.X_mul
  have hshift_ne : g + X * f ≠ 0 :=
    add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
      hgnn hfnn.X_mul (mul_ne_zero X_ne_zero hf0)
  exact
    strictInterl_of_affine_family_nonneg
      hf0 hshift_ne hfnn hshift_nonneg
      (shifted_affine_family_of_affine_family haff)

/-- Same-degree affine families recover the fixed right pair `(g, X * f)` via
the shifted-pair seam. This is the honest same-degree boundary theorem that
survives the linear counterexample to the stronger false bridge. -/
theorem strictInterl_right_pair_of_affine_family_nonneg_sameDegree
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hdeg : g.natDegree = f.natDegree) :
    StrictInterl g (X * f) :=
  strictInterl_right_pair_of_strictInterl_shifted_pair_sameDegree
    (strictInterl_shifted_pair_of_affine_family_nonneg hf0 hfnn hgnn haff)
    hf0 hg0 hfnn hgnn hdeg

/-- Symmetric degree closeness for positive-combination real-rooted pairs with
nonnegative coefficients. -/
theorem natDegree_close_of_posComboRealRooted_of_nonnegCoeffs
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    f.natDegree ≤ g.natDegree + 1 ∧
      g.natDegree ≤ f.natDegree + 1 := by
  constructor
  · simpa using
      AffineFamily.natDegree_right_le_succ_of_posComboRealRooted_nonneg
        (f := g) (g := f) (PosComboRealRooted.comm hfg) hg0 hf0 hgnn hfnn
  · exact
      AffineFamily.natDegree_right_le_succ_of_posComboRealRooted_nonneg
        (f := f) (g := g) hfg hf0 hg0 hfnn hgnn

lemma isRealRooted_affine_factor {s t : ℝ} (hs : 0 < s) :
    ((C s * X + C t) ≠ 0 ∧ (C s * X + C t).Splits) := by
  have hEq : C s * (X - C (-t / s)) = C s * X + C t := by
    calc
      C s * (X - C (-t / s))
          = C s * X - C s * C (-t / s) := by grind
      _ = C s * X - C (s * (-t / s)) := by simp
      _ = C s * X - C (-t) := by grind
      _ = C s * X + C t := by simp
  rw [← hEq]
  exact isRealRooted_C_mul
    (isRealRooted_X_sub_C (-t / s)).1 (isRealRooted_X_sub_C (-t / s)).2 hs.ne'

lemma affine_family_of_zero_left {g : ℝ[X]} (hg_ne : g ≠ 0) (hg_splits : g.Splits) :
    ∀ {s t : ℝ}, 0 < s → 0 < t →
      ((((C s * X + C t) * (0 : ℝ[X])) + g) ≠ 0 ∧
        (((C s * X + C t) * (0 : ℝ[X])) + g).Splits) := by
  simp [*]

lemma affine_family_of_zero_right {f : ℝ[X]} (hf_ne : f ≠ 0) (hf_splits : f.Splits) :
    ∀ {s t : ℝ}, 0 < s → 0 < t →
      ((((C s * X + C t) * f) + (0 : ℝ[X])) ≠ 0 ∧
        (((C s * X + C t) * f) + (0 : ℝ[X])).Splits) := by
  intro s t hs ht
  simpa using isRealRooted_mul (isRealRooted_affine_factor (t := t) hs).1
    (isRealRooted_affine_factor (t := t) hs).2 hf_ne hf_splits

lemma hasNonnegCoeffs_affine_linear {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasNonnegCoeffs (C a * X + C b) := by
  have hCb : HasNonnegCoeffs (C b) := by rintro (_ | n) <;> simp [hb]
  exact (hasNonnegCoeffs_C_mul ha hasNonnegCoeffs_X).add hCb

/-- If two nonzero polynomials have nonnegative coefficients and every
positive affine combination `(s X + t) f + g` splits, then `f ≪ g`. -/
theorem strictInterl_of_forall_affine_mul_add_splits {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) (hf : HasNonnegCoeffs f) (hg : HasNonnegCoeffs g)
    (haff : ∀ s t : ℝ, 0 < s → 0 < t → ((C s * X + C t) * f + g).Splits) :
    StrictInterl f g := by
  refine strictInterl_of_affine_family_nonneg hf0 hg0 hf hg fun {s t} hs ht ↦
    ⟨?_, haff s t hs ht⟩
  intro h0
  have hcoeff := congrArg (AddMonoidAlgebra.coeff · g.natDegree) h0
  simp only [coeff_add, coeff_zero] at hcoeff
  have hprod := (hasNonnegCoeffs_affine_linear hs.le ht.le).mul hf g.natDegree
  have hlead : 0 < g.coeff g.natDegree := hg.pos_leadingCoeff hg0
  linarith

lemma interl_one_affine_linear {a b : ℝ} (ha : 0 < a) :
    Interl (1 : ℝ[X]) (C a * X + C b) := by
  have hInter : Interlaces (1 : ℝ[X]) (C a * X + C b) := by
    refine interlaces_one_linear ?_
    grind
  exact hInter.toStrictInterl.toInterl

end RealRooted
