/-
# Affine-family criterion for interlacing

Has2x2InterlacingProperty definition, affine-family criterion
(Brändén Lemma 7.8.4), bridge from combo results to Prec.
The remaining live theorem here is `prec_of_affine_family_nonneg`.
-/
import RealRooted.ProductFamily
import RealRooted.AffineDerivative
import RealRooted.AffineFamily.Basic
import RealRooted.AffineFamily.PositiveFamily
import RealRooted.AffineFamily.Boundary
import RealRooted.AffineFamily.RootCrossing
import RealRooted.AffineFamily.Wronskian
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

private lemma affine_family_common_root_reduction_data
    {f g : ℝ[X]} {r : ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
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
      HasPosLeadingCoeff qf ∧
      HasPosLeadingCoeff qg ∧
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
    hasPosLeadingCoeff_of_X_sub_C_mul (by simpa [hqf] using hf_pos)
  have hqg_pos : HasPosLeadingCoeff qg :=
    hasPosLeadingCoeff_of_X_sub_C_mul (by simpa [hqg] using hg_pos)
  have hqf_nonneg : HasNonnegCoeffs qf :=
    hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
      hf_ne hf_splits hfnn hqf_ne hqf_rr.2 hqf_pos ⟨X - C r, by grind⟩
  have hqg_nonneg : HasNonnegCoeffs qg :=
    hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
      hg_ne hg_splits hgnn hqg_ne hqg_rr.2 hqg_pos ⟨X - C r, by grind⟩
  refine ⟨qf, qg, hqf, hqg, hqf_nonneg, hqg_nonneg, hqf_ne, hqg_ne, hqf_pos, hqg_pos, ?_⟩
  intro s t hs ht
  have hbase : ((((C s * X + C t) * ((X - C r) * qf)) + ((X - C r) * qg)) ≠ 0 ∧
    (((C s * X + C t) * ((X - C r) * qf)) + ((X - C r) * qg)).Splits) := by grind
  have hEq :
      (((C s * X + C t) * ((X - C r) * qf)) + ((X - C r) * qg))
        = (X - C r) * (((C s * X + C t) * qf) + qg) := by
    grind
  have hsum_ne : (((C s * X + C t) * qf) + qg) ≠ 0 := by grind
  exact
    isRealRooted_of_dvd hbase.1 hbase.2 hsum_ne
      ⟨X - C r, by
        grind
      ⟩

private lemma prec_right_pair_of_common_root_factor
    {f g qf qg : ℝ[X]} {r : ℝ}
    (hf : f = (X - C r) * qf)
    (hg : g = (X - C r) * qg)
    (hprec_q : Prec qg (X * qf)) :
    Prec g (X * f) := by
  have hprec_mul : Prec ((X - C r) * qg) ((X - C r) * (X * qf)) :=
    prec_mul_common_factor (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hprec_q
  grind

/-- A positive constant cannot remain on the right of a degree-`≥ 2`
nonnegative real-rooted polynomial in a `PosComboRealRooted` family. This is
the affine positive-family analogue of the constant-vs-degree-gap obstruction
from the full Obreschkoff converse. -/
private theorem not_posComboRealRooted_right_const_of_natDegree_ge_two
    {c : ℝ} {p : ℝ[X]}
    (hc : 0 < c)
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p)
    (hdeg : 2 ≤ p.natDegree) :
    ¬ PosComboRealRooted p (C c) := by
  intro hpc
  obtain ⟨t, ht, hbad⟩ :=
    exists_pos_shift_not_isRealRooted_of_isRealRooted_of_natDegree_ge_two
      hp_splits (hpnn.pos_leadingCoeff hp_ne) hdeg
  have hcombo_t : ((p + C (t / c) * C c) ≠ 0 ∧ (p + C (t / c) * C c).Splits) :=
    PosComboRealRooted.isRealRooted_add_right hpc (by simp_all)
  have hrewrite : p + C (t / c) * C c = p + C t := by
    calc
      p + C (t / c) * C c = p + C ((t / c) * c) := by simp
      _ = p + C t := by grind
  grind

/-- A degree gap of at least `2` is incompatible with a positive left family
`C μ * f + g` once both summands have nonnegative coefficients. -/
private theorem not_degree_gap_ge_two_of_add_left_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfamily :
      ∀ {μ : ℝ}, 0 < μ → ((C μ * f + g) ≠ 0 ∧ (C μ * f + g).Splits))
    (hgap : f.natDegree + 2 ≤ g.natDegree) :
    False := by
  let n : ℕ := f.natDegree
  let fN : ℝ[X] := (derivative^[n]) f
  let gN : ℝ[X] := (derivative^[n]) g
  have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hf0
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  have hfamilyN :
      ∀ {μ : ℝ}, 0 < μ → ((gN + C μ * fN) ≠ 0 ∧ (gN + C μ * fN).Splits) := by
    intro μ hμ
    have hbase : ((C μ * f + g) ≠ 0 ∧ (C μ * f + g).Splits) := hfamily hμ
    have hbase_deg : (C μ * f + g).natDegree = g.natDegree := by
      have hμf_deg : (C μ * f).natDegree = f.natDegree := by rw [natDegree_C_mul hμ.ne']
      have hμf_lt : (C μ * f).natDegree < g.natDegree := by lia
      exact
        natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
          hμf_lt
          hg_pos
    have hn_lt : n < (C μ * f + g).natDegree := by lia
    have hder :
        (((derivative^[n]) (C μ * f + g)) ≠ 0 ∧ ((derivative^[n]) (C μ * f + g)).Splits) :=
      AffineFamily.isRealRooted_iterate_derivative_of_lt_natDegree hbase.1 hbase.2 hn_lt
    have hEq :
        (derivative^[n]) (C μ * f + g) = gN + C μ * fN := by
      calc
        (derivative^[n]) (C μ * f + g)
            = (derivative^[n]) (C μ * f) + (derivative^[n]) g := by simp
        _ = C μ * (derivative^[n]) f + (derivative^[n]) g := by simp
        _ = gN + C μ * fN := by grind
    lia
  have hfN_deg : fN.natDegree = 0 := by
    dsimp [fN, n]
    simpa using natDegree_iterate_derivative_eq_sub hf0 (le_rfl : f.natDegree ≤ f.natDegree)
  have hfN_ne : fN ≠ 0 := by
    dsimp [fN, n]
    exact iterate_derivative_ne_zero_of_le_natDegree hf0 (le_rfl : f.natDegree ≤ f.natDegree)
  have hfN_nonneg : HasNonnegCoeffs fN := by
    dsimp [fN, n]
    exact hfnn.iterate_derivative n
  have hfN_C : fN = C (fN.coeff 0) := eq_C_of_natDegree_eq_zero hfN_deg
  have hfN_coeff_pos : 0 < fN.coeff 0 := by
    have hfN_pos : 0 < fN.leadingCoeff := hfN_nonneg.pos_leadingCoeff hfN_ne
    rw [hfN_C] at hfN_pos
    simpa using hfN_pos
  have hgN_nonneg : HasNonnegCoeffs gN := by
    dsimp [gN, n]
    exact hgnn.iterate_derivative n
  have hgN_deg : gN.natDegree = g.natDegree - n := by
    dsimp [gN, n]
    exact natDegree_iterate_derivative_eq_sub hg0 (by lia)
  have hgN_deg_ge2 : 2 ≤ gN.natDegree := by lia
  have hgN_ne : gN ≠ 0 := by
    dsimp [gN, n]
    exact iterate_derivative_ne_zero_of_le_natDegree hg0 (by lia)
  have hgN_pos : HasPosLeadingCoeff gN := hgN_nonneg.pos_leadingCoeff hgN_ne
  have hgN_rr : (gN ≠ 0 ∧ gN.Splits) := by
    have hdegN : fN.natDegree < gN.natDegree := by lia
    apply AffineFamily.isRealRooted_of_add_C_mul_right_family_of_natDegree_lt
    · intro μ hμ
      simpa [add_comm] using hfamilyN hμ
    · exact hfN_nonneg.pos_leadingCoeff hfN_ne
    all_goals lia
  have hposComboN : PosComboRealRooted gN fN :=
    PosComboRealRooted.of_add_right hfamilyN
  have hposComboC : PosComboRealRooted gN (C (fN.coeff 0)) := by lia
  exact
    not_posComboRealRooted_right_const_of_natDegree_ge_two
      (p := gN) (c := fN.coeff 0) hfN_coeff_pos hgN_rr.1 hgN_rr.2 hgN_nonneg hgN_deg_ge2
      hposComboC

/-- Affine-family corollary of the positive-family degree-gap obstruction. -/
private theorem not_degree_gap_ge_two_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hgap : f.natDegree + 2 ≤ g.natDegree) :
    False := by
  refine
    not_degree_gap_ge_two_of_add_left_family_nonneg
      hf0 hg0 hfnn hgnn ?_ hgap
  intro μ hμ
  exact
    AffineFamily.isRealRooted_add_left_of_affine_family_of_natDegree_succ_le
      hf0 hg0 hfnn hgnn haff (by lia) hμ

/-- Degree control for Brändén's affine-family converse. -/
private theorem natDegree_right_le_succ_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    g.natDegree ≤ f.natDegree + 1 := by
  by_contra hdeg
  exact
    not_degree_gap_ge_two_of_affine_family
      hf0 hg0 hfnn hgnn haff (by lia)

/-- Positive-combination degree control with nonnegative coefficients. This is
the fixed-pair version of the same constant-vs-degree-`≥ 2` obstruction and is
what the affine theorem ultimately wants for the pair `(g, X * f)`. -/
private theorem natDegree_right_le_succ_of_posComboRealRooted_nonneg
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    g.natDegree ≤ f.natDegree + 1 := by
  by_contra hdeg
  refine
    not_degree_gap_ge_two_of_add_left_family_nonneg
      hf0 hg0 hfnn hgnn ?_ (by lia)
  intro μ hμ
  exact PosComboRealRooted.isRealRooted_add_left hfg hμ

private lemma natDegree_cases_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 := by
  have hdeg_right : g.natDegree ≤ f.natDegree + 1 :=
    natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
  have hpair₀ :
      PosComboRealRooted g (X * f) ∧
      HasNonnegCoeffs g ∧
      HasNonnegCoeffs (X * f) ∧
      g ≠ 0 ∧
      X * f ≠ 0 ∧
      HasPosLeadingCoeff g ∧
      HasPosLeadingCoeff (X * f) :=
    AffineFamily.affine_family_right_pair_data hfnn hgnn hf0 hg0 haff
  rcases hpair₀ with
    ⟨hpos_pair, hg_nonneg_pair, hXf_nonneg_pair, hg_ne_pair,
      hXf_ne_pair, hg_pos_pair, hXf_pos_pair⟩
  have hdeg_pair_hi : (X * f).natDegree ≤ g.natDegree + 1 :=
    natDegree_right_le_succ_of_posComboRealRooted_nonneg
      hpos_pair hg_ne_pair hXf_ne_pair hg_nonneg_pair hXf_nonneg_pair
  rw [natDegree_mul X_ne_zero hf0, natDegree_X] at hdeg_pair_hi
  lia

private lemma natDegree_cases_right_pair_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    g.natDegree = (X * f).natDegree ∨
      (X * f).natDegree = g.natDegree + 1 := by
  have hpair₀ :
      PosComboRealRooted g (X * f) ∧
      HasNonnegCoeffs g ∧
      HasNonnegCoeffs (X * f) ∧
      g ≠ 0 ∧
      X * f ≠ 0 ∧
      HasPosLeadingCoeff g ∧
      HasPosLeadingCoeff (X * f) :=
    AffineFamily.affine_family_right_pair_data hfnn hgnn hf0 hg0 haff
  rcases hpair₀ with
    ⟨hpos_pair, hg_nonneg_pair, hXf_nonneg_pair, hg_ne_pair,
      hXf_ne_pair, _, _⟩
  have hdeg_right : g.natDegree ≤ f.natDegree + 1 :=
    natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
  have hdeg_pair_lo : g.natDegree ≤ (X * f).natDegree := by simp_all
  have hdeg_pair_hi : (X * f).natDegree ≤ g.natDegree + 1 :=
    natDegree_right_le_succ_of_posComboRealRooted_nonneg
      hpos_pair hg_ne_pair hXf_ne_pair hg_nonneg_pair hXf_nonneg_pair
  lia

private lemma right_pair_root_zero_reduction_data
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hg_root0 : g.IsRoot 0) :
    ∃ qg,
      g = X * qg ∧
      HasNonnegCoeffs qg ∧
      qg ≠ 0 ∧
      HasPosLeadingCoeff qg ∧
      PosComboRealRooted qg f ∧
      qg.natDegree ≤ f.natDegree ∧
      f.natDegree ≤ qg.natDegree + 1 := by
  have hpair₀ :
      PosComboRealRooted g (X * f) ∧
      HasNonnegCoeffs g ∧
      HasNonnegCoeffs (X * f) ∧
      g ≠ 0 ∧
      X * f ≠ 0 ∧
      HasPosLeadingCoeff g ∧
      HasPosLeadingCoeff (X * f) :=
    AffineFamily.affine_family_right_pair_data hfnn hgnn hf0 hg0 haff
  rcases hpair₀ with
    ⟨hpos_pair, hg_nonneg_pair, hXf_nonneg_pair, hg_ne_pair,
      hXf_ne_pair, _, _⟩
  obtain ⟨qg, hqg₀⟩ := dvd_iff_isRoot.mpr hg_root0
  have hqg : g = X * qg := by grind
  have hqg_ne : qg ≠ 0 := by simp_all
  have hqg_nonneg : HasNonnegCoeffs qg := by
    intro n
    have hcoeff := hg_nonneg_pair (n + 1)
    simp_all
  have hqg_pos : HasPosLeadingCoeff qg := hqg_nonneg.pos_leadingCoeff hqg_ne
  have hpos_q : PosComboRealRooted qg f := by
    have hX_pair : PosComboRealRooted (X * qg) (X * f) := by lia
    intro lam μ hlam hμ
    have hEq :
        C lam * (X * qg) + C μ * (X * f) = X * (C lam * qg + C μ * f) := by
      ring
    have hrr : ((X * (C lam * qg + C μ * f)) ≠ 0 ∧ (X * (C lam * qg + C μ * f)).Splits) := by
      simpa [hEq] using hX_pair hlam hμ
    have hcombo_ne : C lam * qg + C μ * f ≠ 0 := by grind
    exact isRealRooted_of_dvd hrr.1 hrr.2 hcombo_ne ⟨X, by grind⟩
  have hdeg_right : g.natDegree ≤ f.natDegree + 1 :=
    natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
  have hdeg_q_lo : qg.natDegree ≤ f.natDegree := by simp_all
  have hdeg_q_hi : f.natDegree ≤ qg.natDegree + 1 := by
    have hdeg_pair_hi : (X * f).natDegree ≤ g.natDegree + 1 :=
      natDegree_right_le_succ_of_posComboRealRooted_nonneg
        hpos_pair hg_ne_pair hXf_ne_pair hg_nonneg_pair hXf_nonneg_pair
    simp_all
  grind

private lemma right_pair_root_zero_affine_line_data
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hg_root0 : g.IsRoot 0) :
    ∃ qg,
      g = X * qg ∧
      HasNonnegCoeffs qg ∧
      qg ≠ 0 ∧
      HasPosLeadingCoeff qg ∧
      PosComboRealRooted qg f ∧
      qg.natDegree ≤ f.natDegree ∧
      f.natDegree ≤ qg.natDegree + 1 ∧
      (∀ {s t : ℝ}, 0 < s → 0 < t →
        ((X * (C s * f + qg) + C t * f) ≠ 0 ∧ (X * (C s * f + qg) + C t * f).Splits)) := by
  obtain ⟨qg, hqg, hqg_nonneg, hqg_ne, hqg_pos, hpos_q, hdeg_q_lo, hdeg_q_hi⟩ :=
    right_pair_root_zero_reduction_data hf0 hg0 hfnn hgnn haff hg_root0
  refine ⟨qg, hqg, hqg_nonneg, hqg_ne, hqg_pos, hpos_q, hdeg_q_lo, hdeg_q_hi, ?_⟩
  grind

/-- If `r < 0` is a root of the succ-degree affine right-hand polynomial `g`,
specializing the affine family to the line `t = -s r` factors out `X - C r`
and leaves a same-degree positive-combination family for the quotient `qg`. -/
private lemma neg_root_quotient_posCombo_data_of_affine_family_succDegree
    {f g : ℝ[X]} {r : ℝ}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hgr : g.IsRoot r) (hr_neg : r < 0) :
    ∃ qg,
      g = (X - C r) * qg ∧
      qg ≠ 0 ∧ (qg ≠ 0 ∧ qg.Splits) ∧
      HasPosLeadingCoeff qg ∧
      qg.natDegree = f.natDegree ∧
      PosComboRealRooted qg f := by
  have hg_rr : (g ≠ 0 ∧ g.Splits) :=
    AffineFamily.isRealRooted_right_of_affine_family_succDegree
      hf0 hg0 hfnn hgnn haff hsucc.symm
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hgr
  have hqg_ne : qg ≠ 0 := by simp_all
  have hqg_rr : (qg ≠ 0 ∧ qg.Splits) :=
    isRealRooted_of_dvd hg_rr.1 hg_rr.2 hqg_ne (by simp_all)
  have hqg_pos : HasPosLeadingCoeff qg :=
    hasPosLeadingCoeff_of_X_sub_C_mul (by simpa [hqg] using hg_pos)
  have hqg_deg : qg.natDegree = f.natDegree := by
    rw [hqg, natDegree_mul (X_sub_C_ne_zero r) hqg_ne, natDegree_X_sub_C] at hsucc
    lia
  have hpos_q_left : PosComboRealRooted f qg := by
    refine PosComboRealRooted.of_add_left ?_
    intro s hs
    have hbase :
        ((((C s * X + C (-s * r)) * f) + g) ≠ 0 ∧ (((C s * X + C (-s * r)) * f) + g).Splits) :=
      haff hs (by nlinarith)
    have hlin : C s * (X - C r) = C s * X + C (-s * r) := by grind
    have hEq :
        (((C s * X + C (-s * r)) * f) + g) =
          (X - C r) * (C s * f + qg) := by
      grind
    have hcombo_ne : C s * f + qg ≠ 0 := by grind
    exact
      isRealRooted_of_dvd hbase.1 hbase.2 hcombo_ne
        ⟨X - C r, by
          grind
        ⟩
  exact ⟨qg, hqg, hqg_ne, hqg_rr, hqg_pos, hqg_deg, hpos_q_left.comm⟩

/-- In the succ-degree affine branch with `g(0) ≠ 0`, the rightmost root of
`g` is strictly negative. Factoring it out gives a same-degree quotient pair
`(qg, f)` with positive-combination real-rootedness. -/
private lemma rightmost_neg_root_quotient_posCombo_data_of_affine_family_succDegree
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hg_root0 : ¬ g.IsRoot 0) :
    ∃ r qg,
      g.IsRoot r ∧
      r < 0 ∧
      g = (X - C r) * qg ∧
      qg ≠ 0 ∧ (qg ≠ 0 ∧ qg.Splits) ∧
      HasPosLeadingCoeff qg ∧
      qg.natDegree = f.natDegree ∧
      (∀ u ∈ qg.roots, u ≤ r) ∧
      PosComboRealRooted qg f := by
  have hg_rr : (g ≠ 0 ∧ g.Splits) :=
    AffineFamily.isRealRooted_right_of_affine_family_succDegree
      hf0 hg0 hfnn hgnn haff hsucc.symm
  have hdeg_pos : 1 ≤ g.natDegree := by lia
  obtain ⟨r, hgr, hr_top⟩ := exists_rightmost_root_of_isRealRooted hg_rr.1 hg_rr.2 hdeg_pos
  have hr_le : r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hg_rr.2 hgnn r ((mem_roots hg_rr.1).mpr hgr)
  have hr_neg : r < 0 := by grind
  obtain ⟨qg, hqg, hqg_ne, hqg_rr, hqg_pos, hqg_deg, hpos_q⟩ :=
    neg_root_quotient_posCombo_data_of_affine_family_succDegree
      hf0 hg0 hfnn hgnn haff hsucc hgr hr_neg
  have hqg_le : ∀ u ∈ qg.roots, u ≤ r := by simp_all
  grind

private lemma prec_right_pair_sameDegree_of_sign_data
    {f g : ℝ[X]}
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hgnn : HasNonnegCoeffs g)
    (hXf_pos : HasPosLeadingCoeff (X * f))
    (hdeg : (X * f).natDegree = g.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hno : ∀ r, g.IsRoot r → ¬ (X * f).IsRoot r)
    (hsign :
      let rs := g.roots.sort (· ≤ ·)
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        (X * f).eval r₁ * (X * f).eval r₂ < 0) :
    Prec g (X * f) := by
  have hright :
      let rs := g.roots.sort (· ≤ ·)
      ∃ uR, (X * f).IsRoot uR ∧ ∀ r ∈ rs, r < uR := by
    simpa using exists_strict_right_root_of_X_mul_of_no_common hg_ne hg_splits hgnn hno
  exact
    PosComboRealRooted.prec_same_of_root_sign_data
      (f := g) (g := X * f) hg_ne hg_splits hXf_pos hdeg hdeg_pos hsign hright

private lemma prec_right_pair_succDegree_no_common_of_sign_data
    {f g : ℝ[X]}
    (hf0 : f ≠ 0)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hgnn : HasNonnegCoeffs g)
    (hXf_pos : HasPosLeadingCoeff (X * f))
    (hsucc : g.natDegree = f.natDegree + 1)
    (hno_fg : ∀ r, g.IsRoot r → ¬ f.IsRoot r)
    (hg_root0 : ¬ g.IsRoot 0)
    (hsign :
      let rs := g.roots.sort (· ≤ ·)
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        (X * f).eval r₁ * (X * f).eval r₂ < 0) :
    Prec g (X * f) := by
  have hdeg : (X * f).natDegree = g.natDegree := by simp_all
  have hdeg_pos : 1 ≤ g.natDegree := by lia
  exact
    prec_right_pair_sameDegree_of_sign_data
      hg_ne hg_splits hgnn hXf_pos hdeg hdeg_pos
      (no_common_right_pair_of_no_common_of_not_isRoot_zero hno_fg hg_root0)
      hsign

private lemma prec_right_pair_sameDegree_no_common_of_end_sign_data
    {f g : ℝ[X]}
    (hf0 : f ≠ 0)
    (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hXf_pos : HasPosLeadingCoeff (X * f))
    (hsame : g.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ g.natDegree)
    (hsign :
      let rs := g.roots.sort (· ≤ ·)
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        (X * f).eval r₁ * (X * f).eval r₂ < 0)
    (hright_sign :
      let rs := g.roots.sort (· ≤ ·)
      ∀ hrs_ne : rs ≠ [], (X * f).eval (rs.getLast hrs_ne) < 0)
    (hparity :
      (Even g.natDegree ∧
        let rs := g.roots.sort (· ≤ ·)
        0 < (X * f).eval rs.head!) ∨
      (Odd g.natDegree ∧
        let rs := g.roots.sort (· ≤ ·)
        (X * f).eval rs.head! < 0)) :
    Prec g (X * f) := by
  let rs := g.roots.sort (· ≤ ·)
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_eq : (↑rs : Multiset ℝ) = g.roots := Multiset.sort_eq ..
  have hn : 1 ≤ rs.length := by
    have hrs_len : rs.length = g.natDegree := by
      rw [show rs = g.roots.sort (· ≤ ·) by lia, Multiset.length_sort,
        card_roots_of_splits hg_splits]
    lia
  have hrs_ne : rs ≠ [] := by grind
  have hdeg : (X * f).natDegree = g.natDegree + 1 := by simp_all
  rcases hparity with ⟨hpar, hleft_sign⟩ | ⟨hpar, hleft_sign⟩
  · exact
      prec_of_strict_signs_of_endSigns_even
        (f := g) (F := X * f) (rs := rs)
        hg_ne hg_splits hXf_pos hrs_sorted hrs_eq hdeg hn hpar
        (by grind)
        (by lia)
        (by lia)
  · exact
      prec_of_strict_signs_of_endSigns_odd
        (f := g) (F := X * f) (rs := rs)
        hg_ne hg_splits hXf_pos hrs_sorted hrs_eq hdeg hn hpar
        (by grind)
        (by lia)
        (by lia)

/-- In the linear left-hand branch of the affine converse, the right polynomial
must be nonpositive at the unique root of `f`. Otherwise, after translating
that root to `0` and choosing a suitable affine slice, one gets a quadratic
with positive leading coefficient and negative discriminant, contradicting the
real-rooted affine hypothesis. -/
private lemma mul_C_mul_X_mul_C_mul_X (s a : ℝ) :
    (C s * X) * (C a * X) = C (s * a) * X ^ 2 := by
  grind

private lemma add_quadratic_quadratic (u v w z c : ℝ) :
    C u * X ^ 2 + C v * X + (C w * X ^ 2 + C z * X + C c)
      = C (u + w) * X ^ 2 + C (v + z) * X + C c := by
  grind

private lemma eval_nonpos_at_root_of_degree_one_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hf_deg1 : f.natDegree = 1) :
    ∀ r, f.IsRoot r → g.eval r ≤ 0 := by
  intro r hfr
  have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_degree_one hf_deg1
  have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hf0
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  have hr_nonpos : r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hf_rr.2 hfnn r ((mem_roots hf_rr.1).mpr hfr)
  by_contra hgr_pos
  have hdeg_cases : g.natDegree = 1 ∨ g.natDegree = 2 := by
    rcases natDegree_cases_of_affine_family hf0 hg0 hfnn hgnn haff with hgdeg | hgdeg <;> lia
  let a : ℝ := f.coeff 1
  have ha_pos : 0 < a := by
    unfold HasPosLeadingCoeff at hf_pos
    rw [leadingCoeff, hf_deg1] at hf_pos
    lia
  have hf_deg_le_one : f.degree ≤ 1 := by
    rw [degree_eq_natDegree hf0, hf_deg1]
    norm_num
  have hf_eq : f = C a * X + C (f.coeff 0) := by
    simpa [a] using (eq_X_add_C_of_degree_le_one (p := f) hf_deg_le_one)
  have hroot_rel : a * r + f.coeff 0 = 0 := by
    have hf_eval : f.eval r = 0 := by simpa [Polynomial.IsRoot.def] using hfr
    rw [hf_eq, eval_add, eval_mul, eval_C, eval_X] at hf_eval
    simpa [a] using hf_eval
  let g' : ℝ[X] := g.comp (X + C r)
  let A : ℝ := g'.coeff 2
  let B : ℝ := g'.coeff 1
  let c : ℝ := g'.coeff 0
  have hc_eq : c = g.eval r := by
    dsimp [c, g']
    rw [coeff_zero_eq_eval_zero, eval_comp]
    simp
  have hc_pos : 0 < c := by
    rw [hc_eq]
    exact lt_of_not_ge hgr_pos
  have hg'_nonzero : g' ≠ 0 :=
    (Polynomial.comp_X_add_C_ne_zero_iff).2 hg0
  have hg'_natDegree : g'.natDegree = g.natDegree := by
    dsimp [g']
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  have hg'_deg_le_two : g'.degree ≤ 2 := by
    rcases hdeg_cases with hgdeg | hgdeg
    · rw [degree_eq_natDegree hg'_nonzero, hg'_natDegree, hgdeg]
      norm_num
    · rw [degree_eq_natDegree hg'_nonzero, hg'_natDegree, hgdeg]
      norm_num
  have hg'_eq : g' = C A * X ^ 2 + C B * X + C c := by
    simpa [A, B, c] using eq_quadratic_of_degree_le_two (p := g') hg'_deg_le_two
  have hA_nonneg : 0 ≤ A := by
    rcases hdeg_cases with hgdeg | hgdeg
    · have hg'_deg1 : g'.natDegree = 1 := by lia
      have hA_zero : A = 0 := by
        dsimp [A]
        apply coeff_eq_zero_of_natDegree_lt
        lia
      linarith
    · have hg'_deg2 : g'.natDegree = 2 := by lia
      have hg'_pos : HasPosLeadingCoeff g' := by simpa [g'] using hg_pos.comp_X_add_C r
      have hA_eq_lc : A = g'.leadingCoeff := by
        dsimp [A]
        symm
        rw [leadingCoeff, hg'_deg2]
      have hA_pos : 0 < A := by
        rw [hA_eq_lc]
        exact hg'_pos
      linarith
  let s : ℝ := ((a + B) ^ 2 + 4 * c) / (4 * a * c)
  have hs_pos : 0 < s := by
    dsimp [s]
    have hnum_pos : 0 < (a + B) ^ 2 + 4 * c := by
      have hsq_nonneg : 0 ≤ (a + B) ^ 2 := sq_nonneg (a + B)
      nlinarith
    have hden_pos : 0 < 4 * a * c := by positivity
    exact div_pos hnum_pos hden_pos
  let t : ℝ := 1 - s * r
  have ht_pos : 0 < t := by
    dsimp [t]
    nlinarith
  let p : ℝ[X] := (((C s * X + C t) * f) + g)
  have hp_rr : (p ≠ 0 ∧ p.Splits) := haff hs_pos ht_pos
  let q : ℝ[X] := p.comp (X + C r)
  have hq_rr : (q ≠ 0 ∧ q.Splits) := by
    dsimp [q, p]
    exact isRealRooted_comp_X_add_C hp_rr.1 hp_rr.2 r
  have hf_comp : f.comp (X + C r) = C a * X := by
    calc
      f.comp (X + C r) = (C a * X + C (f.coeff 0)).comp (X + C r) := by lia
      _ = C a * (X + C r) + C (f.coeff 0) := by simp
      _ = C a * X + C (a * r + f.coeff 0) := by
            simp only [map_add, map_mul]
            ring
      _ = C a * X := by rw [hroot_rel, Polynomial.C_0, add_zero]
  have hlin_comp :
      (C s * X + C t).comp (X + C r) = C s * X + C (s * r + t) := by
    calc
      (C s * X + C t).comp (X + C r) = C s * (X + C r) + C t := by simp
      _ = C s * X + C (s * r + t) := by
            simp only [map_add, map_mul]
            ring
  have hsrt : s * r + t = 1 := by
    dsimp [t]
    ring
  have hq_eq :
      q = C (s * a + A) * X ^ 2 + C (a + B) * X + C c := by
    calc
      q = ((C s * X + C t).comp (X + C r)) * (f.comp (X + C r)) + g' := by
            dsimp [q, p, g']
            simp
      _ = (C s * X + C (s * r + t)) * (C a * X) + g' := by rw [hlin_comp, hf_comp]
      _ = (C s * X + C 1) * (C a * X) + (C A * X ^ 2 + C B * X + C c) := by rw [hsrt, hg'_eq]
      _ = C (s * a + A) * X ^ 2 + C (a + B) * X + C c := by
            simp only [map_add, map_mul, Polynomial.C_1]
            ring
  have hsa_pos : 0 < s * a := mul_pos hs_pos ha_pos
  have hquad_pos : 0 < s * a + A := by linarith
  have hs_formula : 4 * (s * a) * c = (a + B) ^ 2 + 4 * c := by
    dsimp [s]
    have h4ac : 4 * a * c ≠ 0 := by positivity
    field_simp
  have hdiscrim_neg : discrim (s * a + A) (a + B) c < 0 := by
    have hmain : (a + B) ^ 2 < 4 * (s * a + A) * c := by nlinarith [hs_formula, hA_nonneg, hc_pos]
    rw [discrim]
    nlinarith
  have hq_noRoot : ∀ x : ℝ, ¬ q.IsRoot x := by
    intro x hx
    have hq_eval_zero : q.eval x = 0 := by simpa [Polynomial.IsRoot.def] using hx
    have hquad_eval :
        (s * a + A) * (x * x) + (a + B) * x + c = 0 := by
      have hq_eval_zero' :
          (C (s * a + A) * X ^ 2 + C (a + B) * X + C c).eval x = 0 := by
        lia
      simpa [eval_add, eval_mul, eval_C, eval_X, eval_pow, pow_two] using hq_eval_zero'
    have hdisc_sq :
        discrim (s * a + A) (a + B) c = (2 * (s * a + A) * x + (a + B)) ^ 2 :=
      discrim_eq_sq_of_quadratic_eq_zero hquad_eval
    have hdisc_nonneg : 0 ≤ discrim (s * a + A) (a + B) c := by
      rw [hdisc_sq]
      positivity
    linarith
  have hq_deg2 : q.natDegree = 2 := by
    rw [hq_eq]
    exact natDegree_quadratic hquad_pos.ne'
  have hroots_pos : 0 < q.roots.card := by
    rw [card_roots_of_splits hq_rr.2, hq_deg2]
    lia
  obtain ⟨x, hx_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hroots_pos
  exact hq_noRoot x ((mem_roots hq_rr.1).mp hx_mem)

/-- Linear left-hand branch of the affine converse. This extracts the
`f.natDegree = 1` case from `prec_of_affine_family_nonneg` so it can later be
reused as the degree-one base case for right-pair recursion. -/
private lemma prec_of_affine_family_nonneg_degree_one
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hdegf1 : f.natDegree = 1) :
    Prec f g := by
  have hdeg_cases : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 :=
    natDegree_cases_of_affine_family hf0 hg0 hfnn hgnn haff
  have hInter : Interlaces (1 : ℝ[X]) f := interlaces_one_linear hdegf1
  have h1_pos : HasPosLeadingCoeff (1 : ℝ[X]) := hasPosLeadingCoeff_one
  have hg_pos_local : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  have hdeg_right_local : g.natDegree ≤ f.natDegree + 1 :=
    natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
  have hF_pos :
      HasPosLeadingCoeff ((g / f) * f + (g % f) * (1 : ℝ[X])) := by
    simpa [EuclideanDomain.div_add_mod'] using hg_pos_local
  have hdeg_lo : f.natDegree ≤ ((g / f) * f + (g % f) * (1 : ℝ[X])).natDegree := by
    rcases hdeg_cases with hgdeg | hgdeg <;>
      simpa [EuclideanDomain.div_add_mod'] using (show f.natDegree ≤ g.natDegree by lia)
  have hdeg_hi :
      ((g / f) * f + (g % f) * (1 : ℝ[X])).natDegree ≤ f.natDegree + 1 := by
    simpa [EuclideanDomain.div_add_mod'] using hdeg_right_local
  have hb_nonpos : ∀ r, f.IsRoot r → (g % f).eval r ≤ 0 := by
    intro r hfr
    have hgr_nonpos :
        g.eval r ≤ 0 :=
      eval_nonpos_at_root_of_degree_one_of_affine_family
        hf0 hg0 hfnn hgnn haff hdegf1 r hfr
    have hf_eval : f.eval r = 0 := by simp_all
    have hdivmod_eval :
        (((g / f) * f + g % f).eval r) = g.eval r :=
      congrArg (fun p : ℝ[X] => p.eval r) (EuclideanDomain.div_add_mod' g f)
    simp_all
  have hprec_lin :
      Prec f (((g / f) * f) + (g % f) * (1 : ℝ[X])) :=
    prec_of_interlaces_evalCoeff_nonpos
      (f := f) (g := (1 : ℝ[X])) (a := g / f) (b := g % f)
      hInter h1_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
  simpa [EuclideanDomain.div_add_mod'] using hprec_lin

/-- Degree-one base case for the affine right pair. This is the right-pair
transport of `prec_of_affine_family_nonneg_degree_one`. -/
private lemma prec_right_pair_of_affine_family_degree_one
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hdegf1 : f.natDegree = 1) :
    Prec g (X * f) :=
  prec_to_prec_mul_X_of_nonneg
    (prec_of_affine_family_nonneg_degree_one hf0 hg0 hfnn hgnn haff hdegf1)
    hfnn hgnn

/-- Public degree-one right-pair form of the affine-family converse.  If
`f.natDegree = 1`, the affine-family hypothesis gives the stronger conclusion
`g ≪ X * f`, not only `f ≪ g`. -/
theorem prec_right_pair_of_affine_family_nonneg_degree_one
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hdegf1 : f.natDegree = 1) :
    Prec g (X * f) :=
  prec_right_pair_of_affine_family_degree_one
    hf0 hg0 hfnn hgnn haff hdegf1

/-- If `g` has an explicit factor `X`, any orientation of `(qg, f)` lifts
immediately to the affine right pair `(g, X * f)` by restoring the common
factor `X`. -/
private lemma prec_right_pair_of_root_zero_factor
    {f g qg : ℝ[X]}
    (hg : g = X * qg)
    (hprec_q : Prec qg f) :
    Prec g (X * f) := by
  have hprec_mul : Prec (X * qg) (X * f) :=
    prec_mul_common_factor isRealRooted_X.1 isRealRooted_X.2 hprec_q
  lia

/-- A second boundary closure hidden in the affine family: after rescaling the
slice `((C s * X + 1) * f) + g`, one gets `X * f + μ * (f + g)` for every
`μ > 0`, so the same right-family continuity argument also shows `X * f`
itself is real-rooted. -/
private lemma isRealRooted_X_mul_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    ((X * f) ≠ 0 ∧ (X * f).Splits) := by
  have hdeg_right : g.natDegree ≤ f.natDegree + 1 :=
    natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
  have hfg_nonneg : HasNonnegCoeffs (f + g) := hfnn.add hgnn
  have hfg_ne : f + g ≠ 0 :=
    add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hfnn hgnn hg0
  have hfg_pos : HasPosLeadingCoeff (f + g) := hfg_nonneg.pos_leadingCoeff hfg_ne
  have hXf_pos : HasPosLeadingCoeff (X * f) :=
    (hfnn.pos_leadingCoeff hf0).X_mul
  have hdeg_fg : (f + g).natDegree ≤ (X * f).natDegree := by
    have hmax : max f.natDegree g.natDegree ≤ f.natDegree + 1 := by simp_all
    have hadd : (f + g).natDegree ≤ max f.natDegree g.natDegree := natDegree_add_le f g
    rw [natDegree_mul X_ne_zero hf0, natDegree_X]
    lia
  apply AffineFamily.isRealRooted_of_add_C_mul_right_family_of_natDegree_le
  · intro μ hμ
    have hbase :
        ((((C μ⁻¹ * X + C (1 : ℝ)) * f) + g) ≠ 0 ∧ (((C μ⁻¹ * X + C (1 : ℝ)) * f) + g).Splits) :=
      haff (by positivity) zero_lt_one
    have hscaled :
        ((C μ * ((((C μ⁻¹ * X + C (1 : ℝ)) * f) + g))) ≠ 0 ∧
          (C μ * ((((C μ⁻¹ * X + C (1 : ℝ)) * f) + g))).Splits) :=
      isRealRooted_C_mul hbase.1 hbase.2 hμ.ne'
    have hmain : C μ * ((C μ⁻¹ * X) * f) = X * f := by grind
    have hEq :
        C μ * ((((C μ⁻¹ * X + C (1 : ℝ)) * f) + g))
          = X * f + C μ * (f + g) := by
      grind
    rw [hEq] at hscaled
    simpa using hscaled
  all_goals lia

/-- Direct endpoint form of the affine-family converse: the two-parameter
positive affine family already forces `X * f` to be real-rooted. -/
theorem isRealRooted_X_mul_of_affine_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    ((X * f) ≠ 0 ∧ (X * f).Splits) :=
  isRealRooted_X_mul_of_affine_family hf0 hg0 hfnn hgnn haff

/-- Left-endpoint form of the affine-family converse: the two-parameter
positive affine family already forces the lower member `f` to be real-rooted. -/
theorem isRealRooted_left_of_affine_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    (f ≠ 0 ∧ f.Splits) := by
  have hXf := isRealRooted_X_mul_of_affine_family_nonneg hf0 hg0 hfnn hgnn haff
  exact isRealRooted_of_X_mul hXf.1 hXf.2

/-- Repackage the affine family as a one-parameter positive-combination family
for the shifted pair `(g + X * f, f)`. This is the natural shifted target for
the affine converse: proving `Prec f (g + X * f)` would reduce the original
statement to the folklore subtraction step. -/
private lemma posComboRealRooted_shifted_pair_of_affine_family
    {f g : ℝ[X]}
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    PosComboRealRooted (g + X * f) f := by
  intro lam μ hlam hμ
  have hbase :
      ((((C (1 : ℝ) * X + C (μ / lam)) * f) + g) ≠ 0 ∧
        (((C (1 : ℝ) * X + C (μ / lam)) * f) + g).Splits) :=
    haff zero_lt_one (by positivity)
  have hscaled :
      ((C lam * ((((C (1 : ℝ) * X + C (μ / lam)) * f) + g))) ≠ 0 ∧
        (C lam * ((((C (1 : ℝ) * X + C (μ / lam)) * f) + g))).Splits) :=
    isRealRooted_C_mul hbase.1 hbase.2 hlam.ne'
  grind

/-- Degree bookkeeping for the shifted affine pair `(g + X * f, f)`: the left
member always has exact succ-degree over `f`. -/
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
    natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
  have hXf_pos : HasPosLeadingCoeff (X * f) :=
    (hfnn.pos_leadingCoeff hf0).X_mul
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  rcases lt_or_eq_of_le hdeg_right with hlt | heq
  · have hg_lt : g.natDegree < (X * f).natDegree := by simp_all
    have hsum_deg : (g + X * f).natDegree = (X * f).natDegree :=
      natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
        hg_lt hXf_pos
    simp_all
  · have hg_eq : g.natDegree = (X * f).natDegree := by simp_all
    have hsum_deg : (g + X * f).natDegree = (X * f).natDegree :=
      natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
        hg_eq hg_pos hXf_pos |>.trans hg_eq
    lia

/-- Data package for the shifted affine pair `(g + X * f, f)`. This isolates
the clean succ-degree positive-family reformulation of the affine converse. -/
private lemma affine_family_shifted_pair_data
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    PosComboRealRooted (g + X * f) f ∧
    HasNonnegCoeffs (g + X * f) ∧
    HasNonnegCoeffs f ∧
    (g + X * f) ≠ 0 ∧
    f ≠ 0 ∧
    HasPosLeadingCoeff (g + X * f) ∧
    HasPosLeadingCoeff f ∧
    (g + X * f).natDegree = f.natDegree + 1 := by
  have hshift_nonneg : HasNonnegCoeffs (g + X * f) :=
    hgnn.add hfnn.X_mul
  have hshift_ne : g + X * f ≠ 0 :=
    add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
      hgnn hfnn.X_mul (mul_ne_zero X_ne_zero hf0)
  refine
    ⟨posComboRealRooted_shifted_pair_of_affine_family haff,
      hshift_nonneg, hfnn, hshift_ne, hf0,
      hshift_nonneg.pos_leadingCoeff hshift_ne,
      hfnn.pos_leadingCoeff hf0,
      natDegree_shifted_pair_eq_succ_of_affine_family hf0 hg0 hfnn hgnn haff⟩

private lemma common_shifted_pair_iff_common_fg
    {f g : ℝ[X]} :
    (∃ r, (g + X * f).IsRoot r ∧ f.IsRoot r) ↔
      ∃ r, g.IsRoot r ∧ f.IsRoot r := by
  constructor
  · intro h
    rcases h with ⟨r, hshift, hfr⟩
    have hf_eval : f.eval r = 0 := by simp_all
    have hshift_eval : (g + X * f).eval r = 0 := by simp_all
    have hg_eval : g.eval r = 0 := by simp_all
    exact ⟨r, by simp_all, hfr⟩
  · intro h
    rcases h with ⟨r, hgr, hfr⟩
    have hf_eval : f.eval r = 0 := by simp_all
    have hg_eval : g.eval r = 0 := by simp_all
    refine ⟨r, ?_, hfr⟩
    simp [Polynomial.IsRoot.def, eval_add, eval_mul, eval_X, hf_eval, hg_eval]

private lemma no_common_shifted_pair_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, f.IsRoot r → ¬ (g + X * f).IsRoot r := by
  simp_all

private lemma not_revPrec_of_shifted_pair_succDegree
    {f s : ℝ[X]}
    (hdeg : s.natDegree = f.natDegree + 1) :
    ¬ Prec s f := by
  intro h
  rcases h with ⟨hs, hf, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩
  have hss_len : ss.length = s.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hs.2]
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf.2]
  lia

private lemma prec_shifted_pair_of_prec_or_revPrec
    {f g : ℝ[X]}
    (h : Prec f (g + X * f) ∨ Prec (g + X * f) f)
    (hdeg : (g + X * f).natDegree = f.natDegree + 1) :
    Prec f (g + X * f) := by
  rcases h with hfg | hgf
  · lia
  · exact False.elim (not_revPrec_of_shifted_pair_succDegree hdeg hgf)

private lemma prec_of_prec_shifted_pair_sameDegree
    {f g : ℝ[X]}
    (h : Prec f (g + X * f))
    (hf0 : f ≠ 0)
    (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : g.natDegree = f.natDegree) :
    Prec f g := by
  have hf : (f ≠ 0 ∧ f.Splits) := h.1
  have hshift : ((g + X * f) ≠ 0 ∧ (g + X * f).Splits) := h.2.1
  have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hf0
  have hshift_nonneg : HasNonnegCoeffs (g + X * f) :=
    hgnn.add hfnn.X_mul
  have hshift_ne : g + X * f ≠ 0 := hshift.1
  have hshift_pos : HasPosLeadingCoeff (g + X * f) :=
    hshift_nonneg.pos_leadingCoeff hshift_ne
  have hshift_deg : (g + X * f).natDegree = f.natDegree + 1 := by
    have hXf_deg : (X * f).natDegree = f.natDegree + 1 := by simp_all
    have hXf_pos : HasPosLeadingCoeff (X * f) :=
      (hfnn.pos_leadingCoeff hf0).X_mul
    have hg_lt : g.natDegree < (X * f).natDegree := by lia
    have hsum_deg : (g + X * f).natDegree = (X * f).natDegree :=
      natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
        hg_lt hXf_pos
    lia
  let a : ℝ := f.leadingCoeff⁻¹
  have ha_ne : a ≠ 0 := inv_ne_zero (ne_of_gt hf_pos)
  have hf_monic : (C a * f).Monic := by
    unfold a
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hshift_lc : (g + X * f).leadingCoeff = f.leadingCoeff := by
    have hg_top_zero : g.coeff (f.natDegree + 1) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      lia
    rw [leadingCoeff, hshift_deg, coeff_add, coeff_X_mul]
    simp [hg_top_zero]
  have hshift_monic : (C a * (g + X * f)).Monic := by
    unfold a
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    simp_all
  have hscaled : Prec (C a * f) (C a * (g + X * f)) :=
    prec_C_mul_right (prec_C_mul_left h ha_ne) ha_ne
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf.2 hfnn
  have hshift_nonpos : ∀ r ∈ (g + X * f).roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hshift.2 hshift_nonneg
  have hprec0 :
      Prec0 (C a * f) (C a * (g + X * f) - X * (C a * f)) := by
    have hdeg_scaled : (C a * f).natDegree + 1 = (C a * (g + X * f)).natDegree := by
      rw [natDegree_C_mul ha_ne, natDegree_C_mul ha_ne, hshift_deg]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using
      prec_sub_X_mul_right
        (f := C a * (g + X * f)) (g := C a * f)
        hscaled hshift_monic hf_monic hdeg_scaled
        (by
          simp_all)
        (by
          simp_all)
  have hEq_sub : C a * (g + X * f) - X * (C a * f) = C a * g := by grind
  have hprec_scaled : Prec (C a * f) (C a * g) := by
    rw [hEq_sub] at hprec0
    have hCa_f_ne : C a * f ≠ 0 := mul_ne_zero (C_ne_zero.mpr ha_ne) hf0
    have hCa_g_ne : C a * g ≠ 0 := mul_ne_zero (C_ne_zero.mpr ha_ne) hg0
    rcases hprec0 with hleft0 | hright0 | hprec <;> lia
  have hprec_back :
      Prec (C a⁻¹ * (C a * f)) (C a⁻¹ * (C a * g)) :=
    prec_C_mul_right
      (prec_C_mul_left hprec_scaled (inv_ne_zero ha_ne))
      (inv_ne_zero ha_ne)
  have hcancel_f : C a⁻¹ * (C a * f) = f := by
    calc
      C a⁻¹ * (C a * f) = C (a⁻¹ * a) * f := by grind
      _ = f := by simp_all
  have hcancel_g : C a⁻¹ * (C a * g) = g := by
    calc
      C a⁻¹ * (C a * g) = C (a⁻¹ * a) * g := by grind
      _ = g := by simp_all
  lia

private lemma prec_right_pair_of_prec_shifted_pair_sameDegree
    {f g : ℝ[X]}
    (h : Prec f (g + X * f))
    (hf0 : f ≠ 0)
    (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : g.natDegree = f.natDegree) :
    Prec g (X * f) :=
  prec_to_prec_mul_X_of_nonneg
    (prec_of_prec_shifted_pair_sameDegree h hf0 hg0 hfnn hgnn hdeg)
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

/-- Isolated high-degree frontier for the affine converse after removing the
already-settled shared-root succ-degree branch. What remains is exactly the
genuine no-shortcut core:

* either `(f, g)` have no common root, in which case the fixed right pair
  `(g, X * f)` must be oriented directly;
* or `g` has the same degree as `f`, in which case the shifted pair
  `(g + X * f, f)` should absorb the common-root bookkeeping.

The low-degree branches are handled separately in
`prec_of_affine_family_nonneg`. -/
private lemma prec_right_pair_of_affine_family_high_degree_core
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hno_common_fg : ¬ ∃ r, g.IsRoot r ∧ f.IsRoot r) :
    Prec g (X * f) := by
  -- Both degree branches (same and succ) reduce to the AllCombo upgrade
  -- `allComboRealRooted_of_affine_family_succDegree`, applied either to
  -- the original pair (succ case) or to the shifted pair (same case).
  have hXf_rr : ((X * f) ≠ 0 ∧ (X * f).Splits) :=
    isRealRooted_X_mul_of_affine_family hf0 hg0 hfnn hgnn haff
  have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_X_mul hXf_rr.1 hXf_rr.2
  have hdeg_cases : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 :=
    natDegree_cases_of_affine_family hf0 hg0 hfnn hgnn haff
  rcases hdeg_cases with hsame | hsucc
  · -- Same-degree case: apply AllCombo to the shifted pair (g + X*f, f).
    have hshift_nonneg : HasNonnegCoeffs (g + X * f) :=
      hgnn.add hfnn.X_mul
    have hshift_ne : g + X * f ≠ 0 :=
      add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
        hgnn hfnn.X_mul (mul_ne_zero X_ne_zero hf0)
    have hshift_deg : (g + X * f).natDegree = f.natDegree + 1 := by
      simpa [hsame] using
        natDegree_shifted_pair_eq_succ_of_affine_family hf0 hg0 hfnn hgnn haff
    have hshift_rr : ((g + X * f) ≠ 0 ∧ (g + X * f).Splits) :=
      AffineFamily.isRealRooted_right_of_affine_family_succDegree
        hf0 hshift_ne hfnn hshift_nonneg
        (shifted_affine_family_of_affine_family haff) hshift_deg.symm
    have hno_shift : ∀ r, (g + X * f).IsRoot r → ¬ f.IsRoot r :=
      fun r hshift_r hfr => by simp_all
    have hall_shift : AllComboRealRooted (g + X * f) f :=
      AffineFamily.allComboRealRooted_of_affine_family_succDegree
        hf0 hshift_ne hfnn hshift_nonneg
        (shifted_affine_family_of_affine_family haff)
        hXf_rr hshift_deg hno_shift
    have hprec_or : Prec f (g + X * f) ∨ Prec (g + X * f) f :=
      prec_of_allComboRealRooted hf_rr.1 hf_rr.2 hshift_rr.1 hshift_rr.2
        (allComboRealRooted_comm hall_shift) (Or.inl hshift_deg.symm)
    have hprec_f_shift : Prec f (g + X * f) :=
      prec_forward_of_orientation_of_succDegree hshift_deg hprec_or
    exact
      prec_right_pair_of_prec_shifted_pair_sameDegree
        hprec_f_shift hf0 hg0 hfnn hgnn hsame
  · -- Succ-degree case: apply AllCombo directly to (g, f).
    have hg_rr : (g ≠ 0 ∧ g.Splits) :=
      AffineFamily.isRealRooted_right_of_affine_family_succDegree
        hf0 hg0 hfnn hgnn haff hsucc.symm
    have hno_fg_fun : ∀ r, g.IsRoot r → ¬ f.IsRoot r := by simp_all
    have hall : AllComboRealRooted g f :=
      AffineFamily.allComboRealRooted_of_affine_family_succDegree
        hf0 hg0 hfnn hgnn haff hXf_rr hsucc hno_fg_fun
    have hprec_or : Prec f g ∨ Prec g f :=
      prec_of_allComboRealRooted hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2
        (allComboRealRooted_comm hall) (Or.inl hsucc.symm)
    have hprec_fg : Prec f g :=
      prec_forward_of_orientation_of_succDegree hsucc hprec_or
    exact prec_to_prec_mul_X_of_nonneg hprec_fg hfnn hgnn

/-- Wrapper matching the original high-degree target. The only genuinely hard
branches are delegated to `prec_right_pair_of_affine_family_high_degree_core`,
while the recursive shared-root succ-degree branch is handled in
`prec_right_pair_of_affine_family_high_degree`. -/
private lemma prec_right_pair_of_affine_family_high_degree_remaining
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hno_common_fg : ¬ ∃ r, g.IsRoot r ∧ f.IsRoot r) :
    Prec g (X * f) :=
  prec_right_pair_of_affine_family_high_degree_core
    hf0 hg0 hfnn hgnn haff hno_common_fg

private lemma prec_right_pair_of_affine_family_high_degree
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hdegf2 : 2 ≤ f.natDegree) :
    Prec g (X * f) := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          f ≠ 0 →
          g ≠ 0 →
          HasNonnegCoeffs f →
          HasNonnegCoeffs g →
          (∀ {s t : ℝ}, 0 < s → 0 < t →
            ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) →
          2 ≤ f.natDegree →
          Prec g (X * f))
      f.natDegree ?_ rfl hf0 hg0 hfnn hgnn haff hdegf2
  intro n ih f g hfdeg hf0 hg0 hfnn hgnn haff hdegf2
  have hXf_rr : ((X * f) ≠ 0 ∧ (X * f).Splits) :=
    isRealRooted_X_mul_of_affine_family hf0 hg0 hfnn hgnn haff
  have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_X_mul hXf_rr.1 hXf_rr.2
  have hdeg_cases : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 :=
    natDegree_cases_of_affine_family hf0 hg0 hfnn hgnn haff
  by_cases hcommon_fg : ∃ r, g.IsRoot r ∧ f.IsRoot r
  · rcases hcommon_fg with ⟨r, hgr, hfr⟩
    rcases hdeg_cases with hsame | hsucc
    · -- Same-degree + common root: use the shifted pair (f, g + X * f).
      -- The shifted pair IS real-rooted and shares the same common root r,
      -- so we can factor (X - C r) from both f and (g + X * f), recurse on
      -- the quotient pair, and lift back.
      have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hf0
      have hshift_nonneg : HasNonnegCoeffs (g + X * f) :=
        hgnn.add hfnn.X_mul
      have hshift_ne : g + X * f ≠ 0 :=
        add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
          hgnn hfnn.X_mul (mul_ne_zero X_ne_zero hf0)
      have hshift_pos : HasPosLeadingCoeff (g + X * f) :=
        hshift_nonneg.pos_leadingCoeff hshift_ne
      have hshift_deg : (g + X * f).natDegree = f.natDegree + 1 := by
        simpa [hsame] using
          natDegree_shifted_pair_eq_succ_of_affine_family hf0 hg0 hfnn hgnn haff
      have hshift_rr : ((g + X * f) ≠ 0 ∧ (g + X * f).Splits) :=
        AffineFamily.isRealRooted_right_of_affine_family_succDegree
          hf0 hshift_ne hfnn hshift_nonneg
          (shifted_affine_family_of_affine_family haff) hshift_deg.symm
      -- The common root of (f, g) is also a root of the shifted pair.
      have hshift_root : (g + X * f).IsRoot r := by simp_all
      -- Factor out the common root from the shifted pair using the
      -- standard reduction machinery.
      obtain ⟨qf, q_shift, hqf, hq_shift, hqf_nonneg, hq_shift_nonneg,
        hqf_ne, hq_shift_ne, _, _, hq_aff⟩ :=
        affine_family_common_root_reduction_data
          hf_rr.1 hf_rr.2 hshift_rr.1 hshift_rr.2 hfnn hshift_nonneg hf_pos hshift_pos
          (shifted_affine_family_of_affine_family haff) hfr hshift_root
      have hqf_deg_lt : qf.natDegree < n := by
        rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne,
          natDegree_X_sub_C]
        lia
      have hqf_deg_pos : 1 ≤ qf.natDegree := by
        rw [hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne,
          natDegree_X_sub_C] at hdegf2
        lia
      -- By induction, the quotient pair satisfies Prec q_shift (X * qf).
      have hprec_q : Prec q_shift (X * qf) := by
        by_cases hqf_deg1 : qf.natDegree = 1
        · exact
            prec_right_pair_of_affine_family_degree_one
              hqf_ne hq_shift_ne hqf_nonneg hq_shift_nonneg hq_aff hqf_deg1
        · grind
      -- Lift: Prec (g + X * f) (X * f) from Prec q_shift (X * qf).
      have hprec_shift : Prec (g + X * f) (X * f) := by
        have hXf_eq : X * f = (X - C r) * (X * qf) := by grind
        have hshift_eq : g + X * f = (X - C r) * q_shift := hq_shift
        rw [hshift_eq, hXf_eq]
        exact prec_mul_common_factor (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hprec_q
      -- Step back: Prec f (g + X * f) from Prec (g + X * f) (X * f).
      have hprec_f_shift : Prec f (g + X * f) :=
        prec_of_prec_mul_X_of_nonneg hprec_shift hfnn hshift_nonneg
      -- Conclude: Prec g (X * f) from the shifted-pair Prec.
      exact
        prec_right_pair_of_prec_shifted_pair_sameDegree
          hprec_f_shift hf0 hg0 hfnn hgnn hsame
    · have hg_rr : (g ≠ 0 ∧ g.Splits) :=
        AffineFamily.isRealRooted_right_of_affine_family_succDegree
          hf0 hg0 hfnn hgnn haff hsucc.symm
      have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hf0
      have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
      obtain ⟨qf, qg, hqf, hqg, hqf_nonneg, hqg_nonneg, hqf_ne, hqg_ne,
        _, _, hqaff⟩ :=
        affine_family_common_root_reduction_data
          hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hfnn hgnn hf_pos hg_pos haff hfr hgr
      have hqf_deg_lt : qf.natDegree < n := by
        rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C]
        lia
      have hqf_deg_pos : 1 ≤ qf.natDegree := by
        rw [hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C] at hdegf2
        lia
      have hprec_q : Prec qg (X * qf) := by
        by_cases hqf_deg1 : qf.natDegree = 1
        · exact
            prec_right_pair_of_affine_family_degree_one
              hqf_ne hqg_ne hqf_nonneg hqg_nonneg hqaff hqf_deg1
        · grind
      exact prec_right_pair_of_common_root_factor hqf hqg hprec_q
  · exact
      prec_right_pair_of_affine_family_high_degree_remaining
        hf0 hg0 hfnn hgnn haff hcommon_fg

/-- Converse affine-family step used in Brändén 7.8.5:
if all positive affine combinations `((C s * X + C t) * f) + g` are real-rooted
and both `f, g` are nonzero with nonnegative coefficients, then `f ≪ g`.

This is exactly the remaining local blocker in the forward matrix argument. -/
theorem prec_of_affine_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    :
    Prec f g := by
  have hdeg_cases : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 :=
    natDegree_cases_of_affine_family hf0 hg0 hfnn hgnn haff
  have hXf_rr : ((X * f) ≠ 0 ∧ (X * f).Splits) :=
    isRealRooted_X_mul_of_affine_family hf0 hg0 hfnn hgnn haff
  have hf_rr : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_X_mul hXf_rr.1 hXf_rr.2
  by_cases hdegf0 : f.natDegree = 0
  · rcases hdeg_cases with hgdeg | hgdeg
    · have hg_deg0 : g.natDegree = 0 := by lia
      have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_deg_zero hg0 hg_deg0
      exact prec_degree_zero_degree_zero hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hdegf0 hg_deg0
    · have hg_deg1 : g.natDegree = 1 := by lia
      have hg_rr : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_degree_one hg_deg1
      exact prec_degree_zero_right_of_degree_one hf_rr.1 hf_rr.2 hg_rr.1 hg_rr.2 hdegf0 hg_deg1
  by_cases hdegf1 : f.natDegree = 1
  · exact prec_of_affine_family_nonneg_degree_one hf0 hg0 hfnn hgnn haff hdegf1
  have hdegf2 : 2 ≤ f.natDegree := by lia
  have hprec_pair : Prec g (X * f) :=
    prec_right_pair_of_affine_family_high_degree hf0 hg0 hfnn hgnn haff hdegf2
  exact prec_of_prec_mul_X_of_nonneg hprec_pair hfnn hgnn

/-- Right-pair form of the affine-family converse. This is the degree-free
public API: the affine-family hypothesis gives `f ≪ g`, and nonnegative
coefficients transport this to `g ≪ X * f`. -/
theorem prec_right_pair_of_affine_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    Prec g (X * f) :=
  prec_to_prec_mul_X_of_nonneg
    (prec_of_affine_family_nonneg hf0 hg0 hfnn hgnn haff)
    hfnn hgnn

/-- Closed affine-segment wrapper for `prec_of_affine_family_nonneg`.

For each positive affine factor `sX+t`, assume the two endpoint polynomials
`(sX+t)P0+H0` and `(sX+t)P1+H1` are positively compatible, and assume the
endpoints themselves are real-rooted.  Then every convex interpolation
`Pβ=(1-β)P0+βP1`, `Hβ=(1-β)H0+βH1` satisfies `Pβ ≪ Hβ`, provided the
usual nonzero and nonnegative-coefficient hypotheses for Branden's affine
criterion hold. -/
theorem prec_of_affine_segment_endpoints_nonneg
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
    Prec (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) := by
  refine prec_of_affine_family_nonneg hPβ0 hHβ0 hPβnn hHβnn ?_
  intro s t hs ht
  have hseg :
      ((C (1 - β) * (((C s * X + C t) * P0) + H0) +
          C β * (((C s * X + C t) * P1) + H1)) ≠ 0 ∧
        (C (1 - β) * (((C s * X + C t) * P0) + H0) +
            C β * (((C s * X + C t) * P1) + H1)).Splits) :=
    PosComboRealRooted.isRealRooted_closed_segment
      (hendpoint hs ht) (hleft hs ht).1 (hleft hs ht).2 (hright hs ht).1 (hright hs ht).2 hβ0 hβ1
  grind

/-- Variant of `prec_of_affine_segment_endpoints_nonneg` where endpoint
real-rootedness is recovered from positive-combination real-rootedness plus
equal degree and positive leading coefficients at every affine specialization. -/
theorem prec_of_affine_segment_endpoints_sameDegree_nonneg
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
    Prec (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) := by
  refine prec_of_affine_family_nonneg hPβ0 hHβ0 hPβnn hHβnn ?_
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
ASW/PF version of `prec_of_affine_segment_endpoints_nonneg`.

For every positive affine factor `sX+t`, it is enough to prove Polya-frequency
for the coefficient sequence of each nonzero endpoint pencil `F0 + z F1`,
`z>=0`. ASW turns this Toeplitz-total-nonnegativity input into endpoint
`PosComboRealRooted`; the preceding affine-segment wrapper then gives the
directed segment relation.
-/
theorem prec_of_affine_segment_endpoint_pf_nonneg
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
    Prec (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) := by
  refine prec_of_affine_segment_endpoints_nonneg hβ0 hβ1 hPβ0 hHβ0 hPβnn hHβnn ?_
    hleft hright
  intro s t hs ht
  exact PosComboRealRooted.of_aissenSchoenbergWhitney_right_pencil
    (f := (((C s * X + C t) * P0) + H0))
    (g := (((C s * X + C t) * P1) + H1))
    (fun {z} hz => hpencil_ne hs ht hz)
    (fun {z} hz => hpencil_pf hs ht hz)

/--
TNN-named version of `prec_of_affine_segment_endpoint_pf_nonneg`.

The LGV certificate layer naturally produces Toeplitz total nonnegativity of
the coefficient sequence.  Since `IsPolyaFreqSeq` is the same
predicate here, this wrapper avoids a small definitional conversion at the
final handoff.
-/
theorem prec_of_affine_segment_endpoint_tnn_nonneg
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
    (hpencil_tnn :
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
    Prec (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) :=
  prec_of_affine_segment_endpoint_pf_nonneg hβ0 hβ1 hPβ0 hHβ0 hPβnn hHβnn
    hpencil_ne
    (fun {_s _t _z} hs ht hz => hpencil_tnn hs ht hz)
    hleft hright

/--
Same-degree ASW/PF endpoint wrapper.  This is the version to use when endpoint
real-rootedness should be recovered from positive compatibility plus equal
degree and positive leading coefficients.
-/
theorem prec_of_affine_segment_endpoint_pf_sameDegree_nonneg
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
    Prec (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) := by
  refine prec_of_affine_segment_endpoints_sameDegree_nonneg hβ0 hβ1 hPβ0 hHβ0 hPβnn
    hHβnn ?_ hleft_pos hright_pos hdeg
  intro s t hs ht
  exact PosComboRealRooted.of_aissenSchoenbergWhitney_right_pencil
    (f := (((C s * X + C t) * P0) + H0))
    (g := (((C s * X + C t) * P1) + H1))
    (fun {z} hz => hpencil_ne hs ht hz)
    (fun {z} hz => hpencil_pf hs ht hz)

/--
Same-degree TNN-named endpoint wrapper.
-/
theorem prec_of_affine_segment_endpoint_tnn_sameDegree_nonneg
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
    (hpencil_tnn :
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
    Prec (C (1 - β) * P0 + C β * P1) (C (1 - β) * H0 + C β * H1) :=
  prec_of_affine_segment_endpoint_pf_sameDegree_nonneg hβ0 hβ1 hPβ0 hHβ0 hPβnn
    hHβnn hpencil_ne
    (fun {_s _t _z} hs ht hz => hpencil_tnn hs ht hz)
    hleft_pos hright_pos hdeg

/-- Branden's affine-family converse immediately upgrades to the full
Obreschkoff all-combinations conclusion in the nonnegative-coefficient regime:
once `prec_of_affine_family_nonneg` gives `f ≪ g`, every real linear
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
  allComboRealRooted_of_prec
    (prec_of_affine_family_nonneg hf0 hg0 hfnn hgnn haff)

/-- Public shifted-pair package extracted from a nonnegative affine family.
This is the corrected same-degree seam after the failed boundary-right-pair
target: the affine family automatically promotes the shifted pair
`(g + X * f, f)` into the clean succ-degree positive-combination regime. -/
theorem shifted_pair_data_of_affine_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    PosComboRealRooted (g + X * f) f ∧
    HasNonnegCoeffs (g + X * f) ∧
    HasNonnegCoeffs f ∧
    (g + X * f) ≠ 0 ∧
    f ≠ 0 ∧
    HasPosLeadingCoeff (g + X * f) ∧
    HasPosLeadingCoeff f ∧
    (g + X * f).natDegree = f.natDegree + 1 :=
  affine_family_shifted_pair_data hf0 hg0 hfnn hgnn haff

/-- A nonnegative affine family already orients the shifted pair:
`f ≺ g + X * f`. This is the public corrected replacement for the earlier
false attempt to orient every boundary pair `(C t * f + g, X * f)`. -/
theorem prec_shifted_pair_of_affine_family_nonneg
    {f g : ℝ[X]}
    (hf0 : f ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    Prec f (g + X * f) := by
  have hshift_nonneg : HasNonnegCoeffs (g + X * f) :=
    hgnn.add hfnn.X_mul
  have hshift_ne : g + X * f ≠ 0 :=
    add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
      hgnn hfnn.X_mul (mul_ne_zero X_ne_zero hf0)
  exact
    prec_of_affine_family_nonneg
      hf0 hshift_ne hfnn hshift_nonneg
      (shifted_affine_family_of_affine_family haff)

/-- Same-degree affine families recover the fixed right pair `(g, X * f)` via
the shifted-pair seam. This is the honest same-degree boundary theorem that
survives the linear counterexample to the stronger false bridge. -/
theorem prec_right_pair_of_affine_family_nonneg_sameDegree
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits))
    (hdeg : g.natDegree = f.natDegree) :
    Prec g (X * f) :=
  prec_right_pair_of_prec_shifted_pair_sameDegree
    (prec_shifted_pair_of_affine_family_nonneg hf0 hfnn hgnn haff)
    hf0 hg0 hfnn hgnn hdeg

/-- Public shifted-pair reduction in the same-degree nonnegative regime:
once the corrected shifted pair satisfies `f ≺ g + X * f`, the original pair
already satisfies `f ≺ g`. This packages the internal subtraction step used in
the affine-family same-degree branch. -/
theorem prec_of_prec_shifted_pair_sameDegree_nonneg
    {f g : ℝ[X]}
    (h : Prec f (g + X * f))
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : g.natDegree = f.natDegree) :
    Prec f g :=
  prec_of_prec_shifted_pair_sameDegree
    h hf0 hg0 hfnn hgnn hdeg

/-- Public wrapper of the internal positive-family degree-gap obstruction:
for a positive-combination real-rooted pair with nonnegative coefficients,
the right degree is at most one more than the left degree. -/
theorem natDegree_right_le_succ_of_posComboRealRooted_of_nonnegCoeffs
    {f g : ℝ[X]}
    (hfg : PosComboRealRooted f g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    g.natDegree ≤ f.natDegree + 1 :=
  natDegree_right_le_succ_of_posComboRealRooted_nonneg
    hfg hf0 hg0 hfnn hgnn

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
      natDegree_right_le_succ_of_posComboRealRooted_of_nonnegCoeffs
        (f := g) (g := f) (PosComboRealRooted.comm hfg) hg0 hf0 hgnn hfnn
  · exact
      natDegree_right_le_succ_of_posComboRealRooted_of_nonnegCoeffs
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
      ((((C s * X + C t) * (0 : ℝ[X])) + g) ≠ 0 ∧ (((C s * X + C t) * (0 : ℝ[X])) + g).Splits) := by
  simp [*]

lemma affine_family_of_zero_right {f : ℝ[X]} (hf_ne : f ≠ 0) (hf_splits : f.Splits) :
    ∀ {s t : ℝ}, 0 < s → 0 < t →
      ((((C s * X + C t) * f) + (0 : ℝ[X])) ≠ 0 ∧ (((C s * X + C t) * f) + (0 : ℝ[X])).Splits) := by
  intro s t hs ht
  simpa using isRealRooted_mul (isRealRooted_affine_factor (t := t) hs).1
    (isRealRooted_affine_factor (t := t) hs).2 hf_ne hf_splits

lemma hasNonnegCoeffs_affine_linear {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasNonnegCoeffs (C a * X + C b) := by
  have hCb : HasNonnegCoeffs (C b) := by rintro (_ | n) <;> simp [hb]
  exact (nonnegCoeffs_C_mul ha hasNonnegCoeffs_X).add hCb

lemma prec0_one_affine_linear {a b : ℝ} (ha : 0 < a) :
    Prec0 (1 : ℝ[X]) (C a * X + C b) := by
  have hInter : Interlaces (1 : ℝ[X]) (C a * X + C b) := by
    refine interlaces_one_linear ?_
    grind
  exact hInter.toPrec.toPrec0

end RealRooted
