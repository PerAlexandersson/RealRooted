module

import RealRooted.ChudnovskySeymour.Core
public import RealRooted.PFPolynomial
public import RealRooted.Compatibility.Basic

/-!
# Chudnovsky--Seymour for PF families with zero members

The Chudnovsky--Seymour theorem `chudnovskySeymour_pairwiseCompatible_iff_familyCompatible`
assumes every member is nonzero.  For polynomials with nonnegative coefficients and only real
roots (PF polynomials), zero members are harmless: they contribute nothing to a weighted sum.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

private lemma weightedSum_filter_ne_zero (ws : List (ℝ × ℝ[X])) :
    weightedSum (ws.filter fun ap => decide (ap.2 ≠ 0)) = weightedSum ws := by
  induction ws with
  | nil => simp
  | cons ap ws ih =>
    rcases ap with ⟨a, p⟩
    by_cases hp : p = 0 <;> simp_all [weightedSum]

/-- Pairwise compatibility of PF polynomials implies joint compatibility, allowing zero
members. -/
theorem PairwiseCompatible.familyCompatible {fs : List ℝ[X]}
    (hpair : PairwiseCompatible fs) (hpf : ∀ p ∈ fs, IsPFPolynomial p) :
    FamilyCompatible fs := by
  set gs := fs.filter fun p => decide (p ≠ 0)
  have hmem {p : ℝ[X]} (hp : p ∈ gs) : p ∈ fs ∧ p ≠ 0 := by simpa [gs] using hp
  have hrr : ∀ p ∈ gs, p ≠ 0 ∧ p.Splits := fun p hp =>
    (hpf p (hmem hp).1).ne_zero_and_splits (hmem hp).2
  have hpos : ∀ p ∈ gs, HasPosLeadingCoeff p := fun p hp =>
    (hpf p (hmem hp).1).hasNonnegCoeffs.pos_leadingCoeff (hmem hp).2
  have hlist : fs.Pairwise Compatible := List.pairwise_iff_get.mpr hpair
  have hfamily : FamilyCompatible gs :=
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible hrr hpos).mp
      (List.pairwise_iff_get.mp (hlist.filter _))
  intro ws hws hweights
  have hvs {ap : ℝ × ℝ[X]} (hap : ap ∈ ws.filter fun ap => decide (ap.2 ≠ 0)) :
      ap ∈ ws ∧ ap.2 ≠ 0 := by simpa using hap
  rw [← weightedSum_filter_ne_zero ws]
  exact hfamily _ (fun ap hap => by simpa [gs] using ⟨hws ap (hvs hap).1, (hvs hap).2⟩)
    fun ap hap => hweights ap (hvs hap).1

/-- Nonnegative weighted sums of a pairwise-compatible PF family are PF. -/
theorem PairwiseCompatible.isPFPolynomial_weightedSum {fs : List ℝ[X]}
    (hpair : PairwiseCompatible fs) (hpf : ∀ p ∈ fs, IsPFPolynomial p)
    {ws : List (ℝ × ℝ[X])} (hmem : ∀ ap ∈ ws, ap.2 ∈ fs) (hweights : ∀ ap ∈ ws, 0 ≤ ap.1) :
    IsPFPolynomial (weightedSum ws) :=
  IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    (hasNonnegCoeffs_weightedSum ws hweights fun ap hap =>
      (hpf ap.2 (hmem ap hap)).hasNonnegCoeffs)
    (((hpair.familyCompatible hpf) ws hmem hweights).imp_right And.right)

end RealRooted
