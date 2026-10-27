module

import RealRooted.RootVieta
import RealRooted.CoefficientDominance.Symmetric.Polynomial
public import RealRooted.SortedRoots
public import RealRooted.CoefficientDominance.Symmetric.Finite

/-!
# Vieta formulas in terms of sorted root sequences

Coefficients and values of a polynomial with nonzero roots and constant coefficient one,
expressed through the reciprocal sorted-root sequence `SortedRoots.rootSeq`.
-/

public section

namespace RealRooted.RootVieta

open Polynomial

noncomputable section

/-- The coefficient of a polynomial with constant coefficient one is the
elementary symmetric function of its reciprocal sorted-root sequence. -/
theorem coeff_eq_esym_recip_rootSeq {p : ℝ[X]}
    (hcard : p.roots.card = p.natDegree)
    (hnz : ∀ ξ ∈ p.roots, ξ ≠ 0) (hzero : p.coeff 0 = 1) (j : ℕ) :
    p.coeff j = CoefficientDominance.Symmetric.esym
      (fun i => 1 / SortedRoots.rootSeq p i) (SortedRoots.rootMags p).length j := by
  have hprod := eq_prod_one_add hcard hnz hzero
  have hroots := SortedRoots.prod_roots_eq_range p
    (fun m : ℝ => 1 + C (1 / m) * X)
  have hmap : (p.roots.map (fun ξ => 1 + C (-(1 / ξ)) * X)).prod =
      ∏ i ∈ Finset.range (SortedRoots.rootMags p).length,
        (1 + C (1 / SortedRoots.rootSeq p i) * X) := by
    rw [← hroots]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun ξ hξ => ?_)
    rw [one_div_neg_eq_neg_one_div]
  have hfac := hprod.trans hmap
  conv_lhs => rw [hfac]
  rw [CoefficientDominance.Symmetric.coeff_prod_one_add]

/-- Evaluating a polynomial with constant coefficient one at `-s` factors over
its reciprocal sorted-root sequence. -/
theorem eval_neg_eq_prod_recip_rootSeq {p : ℝ[X]}
    (hcard : p.roots.card = p.natDegree)
    (hnz : ∀ ξ ∈ p.roots, ξ ≠ 0) (hzero : p.coeff 0 = 1) (s : ℝ) :
    p.eval (-s) = ∏ i ∈ Finset.range (SortedRoots.rootMags p).length,
      (1 - s * (1 / SortedRoots.rootSeq p i)) := by
  have hprod := eq_prod_one_add hcard hnz hzero
  have hroots := SortedRoots.prod_roots_eq_range p
    (fun m : ℝ => 1 + C (1 / m) * X)
  have hmap : (p.roots.map (fun ξ => 1 + C (-(1 / ξ)) * X)).prod =
      ∏ i ∈ Finset.range (SortedRoots.rootMags p).length,
        (1 + C (1 / SortedRoots.rootSeq p i) * X) := by
    rw [← hroots]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun ξ hξ => ?_)
    rw [one_div_neg_eq_neg_one_div]
  have hfac := hprod.trans hmap
  conv_lhs => rw [hfac]
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp
  ring

end

end RealRooted.RootVieta
