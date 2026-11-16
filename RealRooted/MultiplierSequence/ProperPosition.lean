module

import RealRooted.MultiplierSequence.Laguerre
import RealRooted.Interlacing.Reversal
import RealRooted.Interlacing.ReversalCommonFactor
import RealRooted.MultiplierSequence.InvPochhammer
public import RealRooted.CommonInterleaver.RootDesc
public import RealRooted.OperatorPreservesInterlacing
import RealRooted.MultiplierSequence.PolyaSchur
public import RealRooted.MultiplierSequence.Infinite
import RealRooted.ObreschkoffConverse.Forward
import RealRooted.ObreschkoffConverse.Converse
import RealRooted.Mathlib.Algebra.Polynomial.Splits

/-!
# Directed proper position for diagonal multiplier operators

A multiplier sequence preserves real-rootedness of every real pencil `a f + b g`, so it preserves
interlacing up to orientation (finite Pólya--Schur).  Comparing the sums of the roots (Vieta)
fixes the orientation: positive multiplier sequences preserve directed proper position.

Reversal conjugation also transports interlacing under weights `gamma k * delta (d-k)`
at input degree `d`, including shifted binomial diagonals across consecutive degrees.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

private theorem natDegree_diagonalOperator_eq_of_natDegree_eq
    {gamma : ℕ → ℝ} {p : ℝ[X]} {d : ℕ}
    (hpdeg : p.natDegree = d) (hp0 : p ≠ 0) (hgamma : gamma d ≠ 0) :
    (diagonalOperator gamma p).natDegree = d := by
  have hdeg : (diagonalOperator gamma p).natDegree = p.natDegree := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_diagonalOperator_le gamma p)
    rw [coeff_diagonalOperator]
    exact mul_ne_zero (by simpa [hpdeg] using hgamma)
      (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  exact hdeg.trans hpdeg

private theorem diagonalOperator_roots_sum_scale
    {gamma : ℕ → ℝ} {p : ℝ[X]} {d : ℕ}
    (hd : 0 < d) (hpdeg : p.natDegree = d) (hp0 : p ≠ 0)
    (hps : p.Splits) (hgamma_top : gamma d ≠ 0)
    (hout : (diagonalOperator gamma p).Splits) :
    (diagonalOperator gamma p).roots.sum =
      (gamma (d - 1) / gamma d) * p.roots.sum := by
  have houtdeg : (diagonalOperator gamma p).natDegree = d :=
    natDegree_diagonalOperator_eq_of_natDegree_eq hpdeg hp0 hgamma_top
  have hnext : (diagonalOperator gamma p).nextCoeff =
      gamma (d - 1) * p.nextCoeff := by
    rw [Polynomial.nextCoeff, houtdeg, coeff_diagonalOperator,
      Polynomial.nextCoeff, hpdeg]
    simp [hd.ne']
  have hleading : (diagonalOperator gamma p).leadingCoeff =
      gamma d * p.leadingCoeff := by
    rw [Polynomial.leadingCoeff, houtdeg, coeff_diagonalOperator,
      ← hpdeg, Polynomial.leadingCoeff]
  have hout_vieta := hout.sum_roots_eq_neg_nextCoeff_div_leadingCoeff
    (by rw [hleading]
        exact mul_ne_zero hgamma_top (Polynomial.leadingCoeff_ne_zero.mpr hp0))
  have hp_vieta := hps.sum_roots_eq_neg_nextCoeff_div_leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  rw [hout_vieta, hnext, hleading, hp_vieta]
  field_simp [hgamma_top, Polynomial.leadingCoeff_ne_zero.mpr hp0]

/-- A finite multiplier sequence preserves the directed `StrictInterl` relation.

The top multipliers preserve the two exact degrees.  In the equal-degree case,
the displayed adjacent-sign hypothesis preserves the root-sum order; in the
successor-degree case exact degree preservation determines the orientation.
-/
theorem IsFiniteMultiplierSequence.strictInterl_diagonalOperator
    {N : ℕ} {gamma : ℕ → ℝ}
    (hgamma : IsFiniteMultiplierSequence N gamma)
    {f g : ℝ[X]} (hfg : StrictInterl f g)
    (hfdeg : f.natDegree ≤ N) (hgdeg : g.natDegree ≤ N)
    (hgamma_f : gamma f.natDegree ≠ 0)
    (hgamma_g : gamma g.natDegree ≠ 0)
    (hsign : f.natDegree = g.natDegree → 0 < f.natDegree →
      0 ≤ gamma (f.natDegree - 1) * gamma f.natDegree) :
    StrictInterl (diagonalOperator gamma f) (diagonalOperator gamma g) := by
  have hf0 : f ≠ 0 := hfg.1.1
  have hg0 : g ≠ 0 := hfg.2.1.1
  have hfs : f.Splits := hfg.1.2
  have hgs : g.Splits := hfg.2.1.2
  have hfd : (diagonalOperator gamma f).natDegree = f.natDegree :=
    natDegree_diagonalOperator_eq_of_natDegree_eq rfl hf0 hgamma_f
  have hgd : (diagonalOperator gamma g).natDegree = g.natDegree :=
    natDegree_diagonalOperator_eq_of_natDegree_eq rfl hg0 hgamma_g
  have hTf0 : diagonalOperator gamma f ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mp
    rw [Polynomial.leadingCoeff, hfd, coeff_diagonalOperator, coeff_natDegree]
    exact mul_ne_zero hgamma_f (Polynomial.leadingCoeff_ne_zero.mpr hf0)
  have hTg0 : diagonalOperator gamma g ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mp
    rw [Polynomial.leadingCoeff, hgd, coeff_diagonalOperator, coeff_natDegree]
    exact mul_ne_zero hgamma_g (Polynomial.leadingCoeff_ne_zero.mpr hg0)
  have hTf_splits : (diagonalOperator gamma f).Splits :=
    (hgamma hfdeg hfs).resolve_left hTf0
  have hTg_splits : (diagonalOperator gamma g).Splits :=
    (hgamma hgdeg hgs).resolve_left hTg0
  have hall : AllComboRealRooted (diagonalOperator gamma f)
      (diagonalOperator gamma g) := by
    intro a b
    have hdegree : (C a * f + C b * g).natDegree ≤ N :=
      (Polynomial.natDegree_add_le _ _).trans <|
        max_le ((Polynomial.natDegree_C_mul_le a f).trans hfdeg)
        ((Polynomial.natDegree_C_mul_le b g).trans hgdeg)
    have hcomb := allComboRealRooted_of_strictInterl hfg a b
    have hmap : diagonalOperator gamma (C a * f + C b * g) =
        C a * diagonalOperator gamma f + C b * diagonalOperator gamma g := by
      rw [diagonalOperator_add, diagonalOperator_C_mul,
        diagonalOperator_C_mul]
    rcases hgamma hdegree hcomb with hzero | hsplit_out
    · simp [← hmap, hzero]
    · simpa only [← hmap] using hsplit_out
  rcases hfg.natDegree_eq_or_eq_succ with hsame | hsucc
  · have hdeg_out : (diagonalOperator gamma f).natDegree =
        (diagonalOperator gamma g).natDegree := by rw [hfd, hgd, hsame]
    have hor := strictInterl_of_allComboRealRooted hTf0 hTf_splits hTg0
      hTg_splits hall (Or.inr hdeg_out)
    rcases hor with hforward | hreverse
    · exact hforward
    · by_cases hd : f.natDegree = 0
      · have hroots_f : (diagonalOperator gamma f).roots = 0 := by
          apply Multiset.card_eq_zero.mp
          rw [Polynomial.splits_iff_card_roots.mp hTf_splits, hfd, hd]
        have hroots_g : (diagonalOperator gamma g).roots = 0 := by
          apply Multiset.card_eq_zero.mp
          rw [Polynomial.splits_iff_card_roots.mp hTg_splits, hgd, hsame, hd]
        apply hreverse.of_reverse_of_roots_sum_le hdeg_out
        rw [hroots_f, hroots_g]
      · have hpos : 0 < f.natDegree := Nat.pos_of_ne_zero hd
        have hsign' := hsign hsame.symm hpos
        have hratio : 0 ≤ gamma (f.natDegree - 1) / gamma f.natDegree := by
          rcases lt_or_gt_of_ne hgamma_f with hneg | hpos_gamma
          · rw [div_nonneg_iff]
            exact Or.inr ⟨by nlinarith [hsign'], le_of_lt hneg⟩
          · exact div_nonneg (by nlinarith [hsign']) (le_of_lt hpos_gamma)
        have hsum_input : f.roots.sum ≤ g.roots.sum :=
          hfg.roots_sum_le_of_sameDegree hsame.symm
        have hsum_f := diagonalOperator_roots_sum_scale hpos rfl hf0 hfs
          hgamma_f hTf_splits
        have hsum_g := diagonalOperator_roots_sum_scale (d := g.natDegree)
          (by simpa [hsame] using hpos) rfl hg0 hgs
          hgamma_g hTg_splits
        have hsum_g' : (diagonalOperator gamma g).roots.sum =
            (gamma (f.natDegree - 1) / gamma f.natDegree) * g.roots.sum := by
          simpa [hsame] using hsum_g
        apply hreverse.of_reverse_of_roots_sum_le hdeg_out
        rw [hsum_f, hsum_g']
        exact mul_le_mul_of_nonneg_left hsum_input hratio
  · have hdeg_out : (diagonalOperator gamma f).natDegree + 1 =
        (diagonalOperator gamma g).natDegree := by rw [hfd, hgd, hsucc]
    have hor := strictInterl_of_allComboRealRooted hTf0 hTf_splits hTg0
      hTg_splits hall (Or.inl hdeg_out)
    exact StrictInterl.forward_of_orientation_of_succDegree hdeg_out.symm hor

/-- A strictly positive infinite multiplier sequence preserves directed proper
position without a degree bound in the statement. -/
theorem IsMultiplierSequence.strictInterl_diagonalOperator_of_pos
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma)
    (hpos : ∀ k, 0 < gamma k) {f g : ℝ[X]} (hfg : StrictInterl f g) :
    StrictInterl (diagonalOperator gamma f) (diagonalOperator gamma g) := by
  let N := max f.natDegree g.natDegree
  apply IsFiniteMultiplierSequence.strictInterl_diagonalOperator
    (hgamma.finite N) hfg (by exact le_max_left _ _) (by exact le_max_right _ _)
    (hpos _).ne' (hpos _).ne'
  intro hsame hd
  exact mul_nonneg (le_of_lt (hpos (f.natDegree - 1)))
    (le_of_lt (hpos f.natDegree))

/-- A common right interleaver is transported by a strictly positive multiplier
sequence. -/
theorem HasCommonInterleaver.diagonalOperator_of_pos
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma)
    (hpos : ∀ k, 0 < gamma k) {fs : List ℝ[X]}
    (hcommon : HasCommonInterleaver fs) :
    HasCommonInterleaver (fs.map (diagonalOperator gamma)) := by
  rcases hcommon with ⟨h, hh⟩
  refine ⟨diagonalOperator gamma h, ?_⟩
  intro f hf
  rcases List.mem_map.mp hf with ⟨p, hp, rfl⟩
  exact hgamma.strictInterl_diagonalOperator_of_pos hpos (hh p hp)

/-- A common left interleaver is transported by a strictly positive multiplier
sequence. -/
theorem HasCommonLeftInterleaver.diagonalOperator_of_pos
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma)
    (hpos : ∀ k, 0 < gamma k) {fs : List ℝ[X]}
    (hcommon : HasCommonLeftInterleaver fs) :
    HasCommonLeftInterleaver (fs.map (diagonalOperator gamma)) := by
  rcases hcommon with ⟨h, hh⟩
  refine ⟨diagonalOperator gamma h, ?_⟩
  intro f hf
  rcases List.mem_map.mp hf with ⟨p, hp, rfl⟩
  exact hgamma.strictInterl_diagonalOperator_of_pos hpos (hh p hp)

/-- The shifted Euler operator preserves directed proper position when its
shift is strictly positive. -/
theorem eulerShift_strictInterl_of_pos
    {r : ℝ} (hr : 0 < r) {f g : ℝ[X]} (hfg : StrictInterl f g) :
    StrictInterl (eulerShift r f) (eulerShift r g) := by
  have hpf := isPFMultiplierSequence_natCast_add hr.le
  have hmult : IsMultiplierSequence (fun k => (k : ℝ) + r) :=
    (isPFMultiplierSequence_iff_multiplierSequence_and_nonneg.mp hpf).1
  have h := hmult.strictInterl_diagonalOperator_of_pos
    (fun k => by positivity) hfg
  simpa only [diagonalOperator_natCast_add_eq_eulerShift] using h

/-- The unshifted Euler operator preserves directed proper position when both
outputs are nonzero. -/
theorem eulerShift_zero_strictInterl_of_nonzero
    {f g : ℝ[X]} (hf : eulerShift 0 f ≠ 0) (hg : eulerShift 0 g ≠ 0)
    (hfg : StrictInterl f g) : StrictInterl (eulerShift 0 f) (eulerShift 0 g) := by
  have hmap_f : diagonalOperator (fun k => (k : ℝ)) f = eulerShift 0 f := by
    simpa only [add_zero] using diagonalOperator_natCast_add_eq_eulerShift 0 f
  have hmap_g : diagonalOperator (fun k => (k : ℝ)) g = eulerShift 0 g := by
    simpa only [add_zero] using diagonalOperator_natCast_add_eq_eulerShift 0 g
  have hfdeg : 0 < f.natDegree := by
    apply Nat.pos_of_ne_zero
    intro hdeg
    apply hf
    rw [← hmap_f]
    rw [← eulerOperator_eq_diagonalOperator_natCast,
      Polynomial.derivative_eq_zero.mpr hdeg]
    simp
  have hgdeg : 0 < g.natDegree := by
    apply Nat.pos_of_ne_zero
    intro hdeg
    apply hg
    rw [← hmap_g]
    rw [← eulerOperator_eq_diagonalOperator_natCast,
      Polynomial.derivative_eq_zero.mpr hdeg]
    simp
  let N := max f.natDegree g.natDegree
  have h := IsFiniteMultiplierSequence.strictInterl_diagonalOperator
    (isMultiplierSequence_natCast.finite N) hfg (le_max_left _ _) (le_max_right _ _)
    (by exact_mod_cast hfdeg.ne') (by exact_mod_cast hgdeg.ne')
    (fun hsame _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [hmap_f, hmap_g] at h
  exact h

/-- The shifted Euler operator preserves the zero-aware directed interlacing
relation for every nonnegative shift. -/
theorem eulerShift_interl_of_nonneg
    {r : ℝ} (hr : 0 ≤ r) {f g : ℝ[X]} (hfg : StrictInterl f g) :
    Interl (eulerShift r f) (eulerShift r g) := by
  by_cases hrpos : 0 < r
  · exact (eulerShift_strictInterl_of_pos hrpos hfg).toInterl
  · have hrzero : r = 0 := le_antisymm (le_of_not_gt hrpos) hr
    subst r
    by_cases hf : eulerShift 0 f = 0
    · rw [hf]
      exact interl_zero_left _
    by_cases hg : eulerShift 0 g = 0
    · rw [hg]
      exact interl_zero_right _
    · exact (eulerShift_zero_strictInterl_of_nonzero hf hg hfg).toInterl

/-- The alternating multiplier sequence reverses the directed order on the
linear pair `X + 2`, `X + 1`. -/
theorem alternating_sign_linear_not_strictInterl :
    ¬ StrictInterl
      (diagonalOperator (fun k => (-1 : ℝ) ^ k) (X + C 2))
      (diagonalOperator (fun k => (-1 : ℝ) ^ k) (X + C 1)) := by
  have hdiag (c : ℝ) : diagonalOperator (fun k => (-1 : ℝ) ^ k) (X + C c) =
      -X + C c := by
    calc
      _ = ((X + C c : ℝ[X]).comp (-X)) := by
        simpa only [mul_one, diagonalOperator_one_sequence] using
          diagonalOperator_alternating (fun _ => (1 : ℝ)) (X + C c)
      _ = -X + C c := by
        rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
  rw [hdiag, hdiag]
  intro h
  have hsum := h.roots_sum_le_of_sameDegree (by simp)
  have hleft := h.1.2.sum_roots_eq_neg_nextCoeff_div_leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr h.1.1)
  have hright := h.2.1.2.sum_roots_eq_neg_nextCoeff_div_leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr h.2.1.1)
  have hleft_sum : (-X + C 2 : ℝ[X]).roots.sum = 2 := by
    calc
      _ = -(-X + C 2 : ℝ[X]).nextCoeff /
          (-X + C 2 : ℝ[X]).leadingCoeff := hleft
      _ = 2 := by norm_num [Polynomial.nextCoeff, Polynomial.leadingCoeff]
  have hright_sum : (-X + C 1 : ℝ[X]).roots.sum = 1 := by
    calc
      _ = -(-X + C 1 : ℝ[X]).nextCoeff /
          (-X + C 1 : ℝ[X]).leadingCoeff := hright
      _ = 1 := by
        norm_num [Polynomial.nextCoeff, Polynomial.leadingCoeff, coeff_add,
          coeff_neg, coeff_X, coeff_C, coeff_one]
  rw [hleft_sum, hright_sum] at hsum
  norm_num at hsum

/-- A positive multiplier preserves successor-degree interlacing. This is the
Pólya--Schur/HKO consequence in `IsMultiplierSequence.strictInterl_diagonalOperator_of_pos`;
see Borcea--Brändén, arXiv:0809.0401, Theorem 1.9. -/
theorem Interlaces.diagonalOperator_of_pos
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma)
    (hpos : ∀ k, 0 < gamma k) {f g : ℝ[X]} (hfg : Interlaces f g) :
    Interlaces (diagonalOperator gamma f) (diagonalOperator gamma g) := by
  apply (hgamma.strictInterl_diagonalOperator_of_pos hpos hfg.toStrictInterl).toInterlaces
  rw [natDegree_diagonalOperator_eq_of_natDegree_eq rfl hfg.2.1.1 (hpos _).ne',
    natDegree_diagonalOperator_eq_of_natDegree_eq rfl hfg.1.1 (hpos _).ne']
  exact hfg.2.2.1

/-- Conjugating a positive multiplier by natural-degree reversal preserves
successor-degree interlacing of PF polynomials with nonzero constant terms.
This follows from Pólya--Schur preservation and the order-reversing inversion of
negative roots; see Borcea--Brändén, arXiv:0809.0401, Theorem 1.9 for the HKO step.
The effective weight is `delta (p.natDegree - k)`, so it varies with the row degree. -/
theorem Interlaces.reverse_diagonalOperator_reverse_of_pos
    {delta : ℕ → ℝ} (hdelta : IsMultiplierSequence delta)
    (hpos : ∀ k, 0 < delta k) {f g : ℝ[X]} (hfg : Interlaces f g)
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hf0 : f.coeff 0 ≠ 0) (hg0 : g.coeff 0 ≠ 0) :
    Interlaces (diagonalOperator delta f.reverse).reverse
      (diagonalOperator delta g.reverse).reverse := by
  have hrev := interlaces_reverse_of_roots_neg hfg
    (roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hg.hasNonnegCoeffs hg0)
    (roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hf.hasNonnegCoeffs hf0)
  have hdiag := hrev.diagonalOperator_of_pos hdelta hpos
  have hnn (p : ℝ[X]) (hp : IsPFPolynomial p) :
      HasNonnegCoeffs (diagonalOperator delta p.reverse) :=
    hp.reverse.hasNonnegCoeffs.diagonalOperator (fun k => (hpos k).le)
  have hconst (p : ℝ[X]) (hp : p ≠ 0) :
      (diagonalOperator delta p.reverse).coeff 0 ≠ 0 := by
    rw [coeff_diagonalOperator, Polynomial.coeff_zero_reverse]
    exact mul_ne_zero (hpos 0).ne' (Polynomial.leadingCoeff_ne_zero.mpr hp)
  exact interlaces_reverse_of_roots_neg hdiag
    (roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne (hnn g hg) (hconst g hfg.1.1))
    (roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne (hnn f hf) (hconst f hfg.2.1.1))

/-- The elementary coefficient identity for reversal-conjugated diagonal operators.
A nonzero constant term fixes the reversal degree, and the top multiplier prevents
its loss after the first diagonal. The resulting weight depends on the input degree. -/
theorem diagonalOperator_reverse_diagonalOperator_reverse
    (gamma delta : ℕ → ℝ) {p : ℝ[X]} (hp0 : p.coeff 0 ≠ 0)
    (hdelta : delta p.natDegree ≠ 0) :
    diagonalOperator gamma (diagonalOperator delta p.reverse).reverse =
      diagonalOperator (fun k => gamma k * delta (p.natDegree - k)) p := by
  have hp : p ≠ 0 := fun h => hp0 (by simp [h])
  have hrev : p.reverse.natDegree = p.natDegree := by
    rw [Polynomial.reverse_natDegree,
      Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hp0), Nat.sub_zero]
  have hdegree : (diagonalOperator delta p.reverse).natDegree = p.natDegree :=
    natDegree_diagonalOperator_eq_of_natDegree_eq hrev
      (Polynomial.reverse_eq_zero.not.mpr hp) hdelta
  ext k
  rw [coeff_diagonalOperator, coeff_diagonalOperator, Polynomial.coeff_reverse, hdegree]
  by_cases hk : k ≤ p.natDegree
  · rw [Polynomial.revAt_le hk, coeff_diagonalOperator, Polynomial.coeff_reverse,
      Polynomial.revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hk]
    ring
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hk), coeff_diagonalOperator,
      Polynomial.coeff_reverse,
      Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hk),
      coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hk)]
    ring

/-- Two positive multiplier sequences give a cross-rank diagonal interlacing
preserver with weights `gamma k * delta (p.natDegree - k)`.
This is reversal conjugation followed by fixed multiplier preservation, a direct
corollary of Pólya--Schur (1914), DOI: 10.1515/crll.1914.144.89, and root inversion. -/
theorem Interlaces.diagonalOperator_twoSided_of_pos
    {gamma delta : ℕ → ℝ}
    (hgamma : IsMultiplierSequence gamma) (hdelta : IsMultiplierSequence delta)
    (hgammaPos : ∀ k, 0 < gamma k) (hdeltaPos : ∀ k, 0 < delta k)
    {f g : ℝ[X]} (hfg : Interlaces f g)
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hf0 : f.coeff 0 ≠ 0) (hg0 : g.coeff 0 ≠ 0) :
    Interlaces
      (diagonalOperator (fun k => gamma k * delta (f.natDegree - k)) f)
      (diagonalOperator (fun k => gamma k * delta (g.natDegree - k)) g) := by
  rw [← diagonalOperator_reverse_diagonalOperator_reverse gamma delta hf0 (hdeltaPos _).ne',
    ← diagonalOperator_reverse_diagonalOperator_reverse gamma delta hg0 (hdeltaPos _).ne']
  exact Interlaces.diagonalOperator_of_pos hgamma hgammaPos
    (hfg.reverse_diagonalOperator_reverse_of_pos hdelta hdeltaPos hf hg hf0 hg0)

/-- Shifted binomial diagonals preserve interlacing across consecutive degrees.
Their weights factor as `(d+a+b)! / ((k+a)! (d-k+b)!)`. The two reciprocal
factorials are shifted Pólya--Schur multiplier sequences, so reversal conjugation
applies. This is a direct corollary of the Laguerre multiplier theorem and root inversion;
see Pólya--Schur (1914), DOI: 10.1515/crll.1914.144.89. -/
theorem Interlaces.diagonalOperator_choose_shift
    (a b : ℕ) {f g : ℝ[X]} (hfg : Interlaces f g)
    (hf : IsPFPolynomial f) (hg : IsPFPolynomial g)
    (hf0 : f.coeff 0 ≠ 0) (hg0 : g.coeff 0 ≠ 0) :
    Interlaces
      (diagonalOperator (fun k => (Nat.choose (f.natDegree + a + b) (k + a) : ℝ)) f)
      (diagonalOperator (fun k => (Nat.choose (g.natDegree + a + b) (k + a) : ℝ)) g) := by
  have hfac (j : ℕ) : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hpos (j : ℕ) : 0 < (j.factorial : ℝ)⁻¹ := by positivity
  have hid (p : ℝ[X]) :
      diagonalOperator (fun k => (Nat.choose (p.natDegree + a + b) (k + a) : ℝ)) p =
        C ((p.natDegree + a + b).factorial : ℝ) *
          diagonalOperator (fun k => ((k + a).factorial : ℝ)⁻¹ *
            ((p.natDegree - k + b).factorial : ℝ)⁻¹) p := by
    ext k
    rw [coeff_diagonalOperator, coeff_C_mul, coeff_diagonalOperator]
    by_cases hk : k ≤ p.natDegree
    · have hchoose := Nat.choose_mul_factorial_mul_factorial
        (n := p.natDegree + a + b) (k := k + a) (by lia)
      have hsub : p.natDegree + a + b - (k + a) = p.natDegree - k + b := by lia
      rw [hsub] at hchoose
      have hc : (Nat.choose (p.natDegree + a + b) (k + a) : ℝ) *
          ((k + a).factorial : ℝ) * ((p.natDegree - k + b).factorial : ℝ) =
          ((p.natDegree + a + b).factorial : ℝ) := by exact_mod_cast hchoose
      field_simp [hfac]
      linear_combination p.coeff k * hc
    · rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hk)]
      ring
  rw [hid f, hid g]
  exact (hfg.diagonalOperator_twoSided_of_pos
    (isMultiplierSequence_inv_factorial.shift a) (isMultiplierSequence_inv_factorial.shift b)
    (fun k => hpos (k + a)) (fun k => hpos (k + b)) hf hg hf0 hg0).C_mul_both
      (hfac _) (hfac _)

end RealRooted
