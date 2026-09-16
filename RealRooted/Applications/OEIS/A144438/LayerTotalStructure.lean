import RealRooted.Applications.OEIS.A144438.TotalBridge
import RealRooted.Multiaffine
import RealRooted.MultivariateStability.AffineEulerCore

/-!
# Multiaffine structure of the Deco layer total

The ordinary-coordinate total is multiaffine.  The polynomial itself remains
defined by the normal-plus-exceptional recurrence; the proof uses the checked
comparison-bottom enumerator identity, whose summands are squarefree
finite-set monomials.

This structural result is a prerequisite for multiaffine stability criteria.
It does not assert stability of the outer sum.
-/

namespace RealRooted.Applications.OEIS

open scoped BigOperators

noncomputable section

/-- The admissible-code enumerator is multiaffine in its ordinary bottom
coordinates. -/
theorem admissibleCodePolynomial_isMultiaffine {R : Type*} [CommSemiring R]
    [Nontrivial R] (h : Nat) :
    MvPolynomial.IsMultiaffine (admissibleCodePolynomial (R := R) h) := by
  rw [admissibleCodePolynomial]
  apply MvPolynomial.IsMultiaffine.sum
  intro c hc
  unfold MinimumInsertionWord.comparisonBottomMonomial
  unfold MvPolynomial.finsetMonomial
  exact MvPolynomial.IsMultiaffine.prod_X _

/-- The normalized-fiber sum is multiaffine in its ordinary bottom
coordinates. -/
theorem normalizedFiberPolynomial_isMultiaffine {R : Type*} [CommSemiring R]
    [Nontrivial R] (h : Nat) :
    MvPolynomial.IsMultiaffine (normalizedFiberPolynomial (R := R) h) := by
  rw [← admissibleCodePolynomial_eq_normalizedFiberPolynomial]
  exact admissibleCodePolynomial_isMultiaffine h

/-- The recurrence-defined ordinary-coordinate total is multiaffine. -/
theorem decoBottomTotal_isMultiaffine (n : Nat) :
    MvPolynomial.IsMultiaffine (decoBottomTotal n) := by
  rw [← admissibleCodePolynomial_eq_decoBottomTotal]
  exact admissibleCodePolynomial_isMultiaffine (n + 2)

/-- The recurrence-defined rank-`n` total uses only the ordinary labels
`1, ..., n`. -/
theorem vars_decoBottomTotal_subset_Icc (n : Nat) :
    (decoBottomTotal n).vars ⊆ Finset.Icc 1 n := by
  rw [← admissibleCodePolynomial_eq_decoBottomTotal,
    admissibleCodePolynomial_eq_sum_historyFiberPolynomial]
  intro x hx
  have houter := (_root_.MvPolynomial.vars_sum_subset Finset.univ
    (fun H : DecoExceptionalHistory (n + 2) =>
      historyFiberPolynomial (R := Real) H)) hx
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at houter
  obtain ⟨H, hxH⟩ := houter
  unfold historyFiberPolynomial at hxH
  have hinner := (_root_.MvPolynomial.vars_sum_subset Finset.univ
    (fun c : DecoHistoryFiber H =>
      MinimumInsertionWord.comparisonBottomMonomial
        (R := Real) c.1.1.inverseWord)) hxH
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hinner
  obtain ⟨c, hxc⟩ := hinner
  unfold MinimumInsertionWord.comparisonBottomMonomial at hxc
  unfold MvPolynomial.finsetMonomial at hxc
  have hprod := (_root_.MvPolynomial.vars_prod
    (s := MinimumInsertionWord.comparisonBottomSupport c.1.1.inverseWord)
    (fun y : Nat => (MvPolynomial.X y : MvPolynomial Nat Real))) hxc
  simp only [Finset.mem_biUnion] at hprod
  obtain ⟨y, hy, hxy⟩ := hprod
  rw [_root_.MvPolynomial.vars_X] at hxy
  simp only [Finset.mem_singleton] at hxy
  subst x
  exact Finset.mem_Icc.mpr
    (mem_comparisonBottomSupport_inverseWord_bounds H c hy)

/-- The recurrence-defined ordinary-coordinate total has nonnegative
coefficients. -/
theorem decoBottomTotal_hasNonnegCoeffs (n : Nat) :
    MvPolynomial.HasNonnegCoeffs (decoBottomTotal n) := by
  rw [← rename_dehomogenize_decoLayerTotal_eq_decoBottomTotal]
  exact ((decoLayerTotal_hasNonnegCoeffs n).dehomogenize).rename_of_injective
    (decoLayerBottomEmbedding n).injective

/-- Stability of a homogeneous layer total orients its ordinary affine Euler
core against the bottom total.  This is the general-degree replacement for a
multiaffine argument at the homogeneous level. -/
theorem eval_coordinateWronskian_decoNormalBottomCore_total_nonneg
    (n : Nat) (hstable : MvRealStable (decoLayerTotal n)) :
    ∀ i x, 0 ≤ MvPolynomial.eval x
      (MvPolynomial.coordinateWronskian
        (decoNormalBottomCore n (decoBottomTotal n))
        (decoBottomTotal n) i) := by
  have hsource :=
    hstable.eval_coordinateWronskian_affineEulerCore_nonneg_of_nonnegative
      (decoLayerTotal_hasNonnegCoeffs n)
      (decoLayerTotal_isHomogeneous n) (by lia)
  have hrename := MvPolynomial.eval_coordinateWronskian_rename_nonneg
    (decoLayerBottomEmbedding n) (decoLayerBottomEmbedding n).injective
    (MvPolynomial.affineEulerCore id ((n + 1 : Nat) : Real)
      (MvPolynomial.dehomogenize (decoLayerTotal n)))
    (MvPolynomial.dehomogenize (decoLayerTotal n)) hsource
  rw [MvPolynomial.rename_affineEulerCore
      (decoLayerBottomEmbedding n) (decoLayerBottomEmbedding n).injective,
    rename_dehomogenize_decoLayerTotal_eq_decoBottomTotal] at hrename
  simpa [decoNormalBottomCore_eq_affineEulerCore, Function.comp_def] using
    hrename

/-- Stability of the homogeneous finite-coordinate layer total is exactly
common-rotation stability of its multiaffine ordinary-coordinate
dehomogenization. -/
theorem decoLayerTotal_mvRealStable_iff_commonRotation_bottomTotal (n : Nat) :
    MvRealStable (decoLayerTotal n) ↔
      MvCommonRotationStable (complexifyMv (decoBottomTotal n)) := by
  have hrename :
      MvPolynomial.rename (decoLayerBottomEmbedding n)
          (complexifyMv (MvPolynomial.dehomogenize (decoLayerTotal n))) =
        complexifyMv (decoBottomTotal n) := by
    have h := congrArg complexifyMv
      (rename_dehomogenize_decoLayerTotal_eq_decoBottomTotal n)
    simpa [complexifyMv, MvPolynomial.map_rename] using h
  rw [← hrename,
    mvCommonRotationStable_rename_iff
      (decoLayerBottomEmbedding n).injective]
  exact mvRealStable_iff_commonRotation_dehomogenize
    (decoLayerTotal_isHomogeneous n)

end

end RealRooted.Applications.OEIS
