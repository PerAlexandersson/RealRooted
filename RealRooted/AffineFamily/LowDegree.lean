/-
# Affine-family degree and low-degree reduction

Degree control, root-zero reductions, and the explicit low-degree branch of
the affine-family converse.
-/
import RealRooted.ProductFamily
import RealRooted.AffineDerivative
import RealRooted.AffineFamily.Basic
import RealRooted.AffineFamily.PositiveFamily
import RealRooted.AffineFamily.Boundary
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
protected theorem AffineFamily.natDegree_right_le_succ_of_affine_family
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
protected theorem AffineFamily.natDegree_right_le_succ_of_posComboRealRooted_nonneg
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

protected lemma AffineFamily.natDegree_cases_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 := by
  have hdeg_right : g.natDegree ≤ f.natDegree + 1 :=
    AffineFamily.natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
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
    AffineFamily.natDegree_right_le_succ_of_posComboRealRooted_nonneg
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
    AffineFamily.natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
  have hdeg_pair_lo : g.natDegree ≤ (X * f).natDegree := by simp_all
  have hdeg_pair_hi : (X * f).natDegree ≤ g.natDegree + 1 :=
    AffineFamily.natDegree_right_le_succ_of_posComboRealRooted_nonneg
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
    AffineFamily.natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
  have hdeg_q_lo : qg.natDegree ≤ f.natDegree := by simp_all
  have hdeg_q_hi : f.natDegree ≤ qg.natDegree + 1 := by
    have hdeg_pair_hi : (X * f).natDegree ≤ g.natDegree + 1 :=
      AffineFamily.natDegree_right_le_succ_of_posComboRealRooted_nonneg
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
    rcases AffineFamily.natDegree_cases_of_affine_family hf0 hg0 hfnn hgnn haff with
      hgdeg | hgdeg <;> lia
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
protected lemma AffineFamily.prec_of_affine_family_nonneg_degree_one
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
    AffineFamily.natDegree_cases_of_affine_family hf0 hg0 hfnn hgnn haff
  have hInter : Interlaces (1 : ℝ[X]) f := interlaces_one_linear hdegf1
  have h1_pos : HasPosLeadingCoeff (1 : ℝ[X]) := hasPosLeadingCoeff_one
  have hg_pos_local : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hg0
  have hdeg_right_local : g.natDegree ≤ f.natDegree + 1 :=
    AffineFamily.natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
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
transport of `AffineFamily.prec_of_affine_family_nonneg_degree_one`. -/
protected lemma AffineFamily.prec_right_pair_of_affine_family_degree_one
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
    (AffineFamily.prec_of_affine_family_nonneg_degree_one hf0 hg0 hfnn hgnn haff hdegf1)
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
  AffineFamily.prec_right_pair_of_affine_family_degree_one
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
protected lemma AffineFamily.isRealRooted_X_mul_of_affine_family
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (haff :
      ∀ {s t : ℝ}, 0 < s → 0 < t →
        ((((C s * X + C t) * f) + g) ≠ 0 ∧ (((C s * X + C t) * f) + g).Splits)) :
    ((X * f) ≠ 0 ∧ (X * f).Splits) := by
  have hdeg_right : g.natDegree ≤ f.natDegree + 1 :=
    AffineFamily.natDegree_right_le_succ_of_affine_family hf0 hg0 hfnn hgnn haff
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
        ((((C μ⁻¹ * X + C (1 : ℝ)) * f) + g) ≠ 0 ∧
          (((C μ⁻¹ * X + C (1 : ℝ)) * f) + g).Splits) :=
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
  AffineFamily.isRealRooted_X_mul_of_affine_family hf0 hg0 hfnn hgnn haff

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

end RealRooted
