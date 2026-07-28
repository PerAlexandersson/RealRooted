import RealRooted.LiuOppositeSigns.XSub.CubicQuadratic

/-!
# Liu left-successor x-subtraction degree-two endpoint

This module packages the normalized cubic/quadratic arithmetic leaf as the
positive-split left-successor right-degree-two endpoint and predicate wrappers.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- The normalized monic cubic/quadratic x-subtraction leaf implies the
degree-three/degree-two positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_two_of_monic
    (hmono : xSubCubicQuadraticSplitsStatement)
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 3) (hqdeg : q.natDegree = 2)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  obtain ⟨a, b, c, u, v, hab, hbc, huv, hproots, hqroots,
      hpfac, hqfac, hau, hbv, huc⟩ :=
    exists_roots_order_of_positiveSplitRootCountPair_three_two
      hpair hpdeg hqdeg
  have hc0 : c ≤ 0 := by
    have hc_mem : c ∈ p.roots := by
      rw [hproots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hpnn c hc_mem
  have hv0 : v ≤ 0 := by
    have hv_mem : v ∈ q.roots := by
      rw [hqroots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hqnn v hv_mem
  let A : ℝ := p.leadingCoeff
  let B : ℝ := q.leadingCoeff
  have hA_pos : 0 < A := by
    dsimp [A]
    exact hpair.left_pos
  have hB_pos : 0 < B := by
    dsimp [B]
    exact hpair.right_pos
  let ν : ℝ := μ * B / A
  have hν_pos : 0 < ν := by
    dsimp [ν]
    exact div_pos (mul_pos hμ hB_pos) hA_pos
  let inner : ℝ[X] :=
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C ν * ((X - C u) * (X - C v))
  have hinner_splits : inner.Splits := by
    dsimp [inner]
    exact hmono hab hbc huv hau hbv huc hc0 hv0 hν_pos
  have hpoly : X * p - C μ * q = C A * inner := by
    rw [hpfac, hqfac]
    dsimp [inner, ν, A, B]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    field_simp [hpair.left_pos.ne']
  rw [hpoly]
  exact hinner_splits.C_mul A

/-- Degree-three/degree-two positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_two
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 3) (hqdeg : q.natDegree = 2)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits :=
  splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_two_of_monic
    xSubCubicQuadraticSplits hpair hpnn hqnn hpdeg hqdeg hμ

/-- Degree-two right endpoint reduction for the sign-normalized x-subtraction
leaf, modulo the normalized monic cubic/quadratic arithmetic leaf. -/
theorem
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_two_of_monic
    (hmono : xSubCubicQuadraticSplitsStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree + 1)
    (hgdeg : g.natDegree = 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg_shift : (f.comp (X + C r)).natDegree = 3 := by
    have hfdeg : f.natDegree = 3 := by
      lia
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hgdeg_shift : (g.comp (X + C r)).natDegree = 2 := by
    simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_two_of_monic
    hmono (hpair.comp_X_add_C r) hfnn hgnn hfdeg_shift hgdeg_shift hμ

/-- Degree-two right endpoint case for the sign-normalized x-subtraction
leaf. -/
theorem
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_two
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree + 1)
    (hgdeg : g.natDegree = 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_two_of_monic
    xSubCubicQuadraticSplits hpair hfnn hgnn hdeg hgdeg

/-- Low-degree right endpoint cases for the sign-normalized x-subtraction
leaf. -/
theorem positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_one
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree + 1)
    (hgdeg : g.natDegree ≤ 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hzero : g.natDegree = 0
  · exact positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
      hpair hfnn hgnn hdeg hzero
  · have hone : g.natDegree = 1 := by
      lia
    exact positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one
      hpair hfnn hgnn hdeg hone

/-- Endpoint cases through right degree two for the sign-normalized
x-subtraction leaf. -/
theorem positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree + 1)
    (hgdeg : g.natDegree ≤ 2) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hle_one : g.natDegree ≤ 1
  · exact positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_one
      hpair hfnn hgnn hdeg hle_one
  · have htwo : g.natDegree = 2 := by
      lia
    exact positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_two
      hpair hfnn hgnn hdeg htwo

/-- Pack the low-degree-right endpoint terminal as a predicate-restricted
positive-split x-sub family. -/
theorem
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_one :
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 1) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_one
    hpair hfnn hgnn hdeg hgdeg

/-- Pack the constant-right endpoint terminal as a predicate-restricted
positive-split x-sub family. -/
theorem
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_zero :
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 0) := by
  refine positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement_of_imp
    (Q := fun n => n ≤ 1) ?_
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_one
  intro n hn
  simp [hn]

/-- Pack the degree-one-right endpoint terminal as a predicate-restricted
positive-split x-sub family. -/
theorem
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_one :
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 1) := by
  refine positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement_of_imp
    (Q := fun n => n ≤ 1) ?_
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_one
  intro n hn
  simp [hn]

/-- Pack the degree-two-right endpoint terminal as a predicate-restricted
positive-split x-sub family, modulo the normalized monic arithmetic leaf. -/
theorem
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two_of_monic
    (hmono : xSubCubicQuadraticSplitsStatement) :
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 2) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_two_of_monic
      hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-two-right endpoint terminal as a predicate-restricted
positive-split x-sub family. -/
theorem
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two :
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 2) :=
  positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_two_of_monic
    xSubCubicQuadraticSplits

/-- Pack the endpoint cases through degree two as a predicate-restricted
positive-split x-sub family. -/
theorem
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_two :
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 2) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
    hpair hfnn hgnn hdeg hgdeg

end LiuOppositeSigns
end RealRooted
