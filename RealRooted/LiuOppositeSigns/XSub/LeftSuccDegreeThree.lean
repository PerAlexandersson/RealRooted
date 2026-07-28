import RealRooted.LiuOppositeSigns.XSub.LeftSuccDegreeTwo
import RealRooted.LiuOppositeSigns.XSub.QuarticCubicBoundary

/-!
# Liu left-successor x-subtraction degree-three endpoint

This module packages the normalized quartic/cubic arithmetic leaf as the
positive-split left-successor right-degree-three endpoint and predicate wrappers.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- The normalized monic degree-four/degree-three terminal implies the
corresponding positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_four_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement)
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 4) (hqdeg : q.natDegree = 3)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  obtain ⟨a, b, c, d, u, v, w, hab, hbc, hcd, huv, hvw, hproots,
      hqroots, hpfac, hqfac, hau, hbv, hcw, huc, hvd⟩ :=
    exists_roots_order_of_positiveSplitRootCountPair_four_three
      hpair hpdeg hqdeg
  have hd0 : d ≤ 0 := by
    have hd_mem : d ∈ p.roots := by
      rw [hproots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hpnn d hd_mem
  have hw0 : w ≤ 0 := by
    have hw_mem : w ∈ q.roots := by
      rw [hqroots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hqnn w hw_mem
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
    X * ((X - C a) * (X - C b) * (X - C c) * (X - C d)) -
      C ν * ((X - C u) * (X - C v) * (X - C w))
  have hinner_splits : inner.Splits := by
    dsimp [inner]
    exact hmono hab hbc hcd huv hvw hau hbv hcw huc hvd hd0 hw0 hν_pos
  have hpfacA :
      p = C A * ((X - C a) * (X - C b) * (X - C c) * (X - C d)) := by
    simpa [A, mul_assoc] using hpfac
  have hqfacB : q = C B * ((X - C u) * (X - C v) * (X - C w)) := by
    simpa [B] using hqfac
  have hpoly : X * p - C μ * q = C A * inner := by
    rw [hpfacA, hqfacB]
    dsimp [inner, ν]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    field_simp [hA_pos.ne']
  rw [hpoly]
  exact hinner_splits.C_mul A

/-- Degree-four/degree-three positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_four_three
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 4) (hqdeg : q.natDegree = 3)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits :=
  splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_four_three_of_monic
    xSubQuarticCubicSplits hpair hpnn hqnn hpdeg hqdeg hμ

/-- Degree-three right endpoint reduction for the sign-normalized
x-subtraction leaf, modulo the normalized monic quartic/cubic arithmetic leaf.
-/
theorem
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree + 1)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg_shift : (f.comp (X + C r)).natDegree = 4 := by
    have hfdeg : f.natDegree = 4 := by
      lia
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hgdeg_shift : (g.comp (X + C r)).natDegree = 3 := by
    simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_four_three_of_monic
    hmono (hpair.comp_X_add_C r) hfnn hgnn hfdeg_shift hgdeg_shift hμ

/-- Degree-three right endpoint reduction for the sign-normalized
x-subtraction leaf. -/
theorem positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree + 1)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
    xSubQuarticCubicSplits hpair hfnn hgnn hdeg hgdeg

/-- Endpoint cases through right degree three for the sign-normalized
x-subtraction leaf, modulo the normalized monic quartic/cubic arithmetic leaf.
-/
theorem
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree + 1)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hle_two : g.natDegree ≤ 2
  · exact positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
      hpair hfnn hgnn hdeg hle_two
  · have hthree : g.natDegree = 3 := by
      lia
    exact
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
        hmono hpair hfnn hgnn hdeg hthree

/-- Endpoint cases through right degree three for the sign-normalized
x-subtraction leaf. -/
theorem positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree + 1)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
    xSubQuarticCubicSplits hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-three-right endpoint terminal as a predicate-restricted
positive-split x-sub family, modulo the normalized monic quartic/cubic
arithmetic leaf. -/
theorem
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
      hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-three-right endpoint terminal as a predicate-restricted
positive-split x-sub family. -/
theorem
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three :
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) :=
  positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
    xSubQuarticCubicSplits

/-- Pack endpoint cases through degree three as a predicate-restricted
positive-split x-sub family, modulo the normalized monic quartic/cubic
arithmetic leaf. -/
theorem
    positiveSplitLeftSuccXSubFamilyPredicate_of_right_natDegree_le_three_of_monic
    (hmono : xSubQuarticCubicSplitsStatement) :
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
      hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack endpoint cases through degree three as a predicate-restricted
positive-split x-sub family. -/
theorem positiveSplitLeftSuccXSubFamilyPredicate_of_right_natDegree_le_three :
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) :=
  positiveSplitLeftSuccXSubFamilyPredicate_of_right_natDegree_le_three_of_monic
    xSubQuarticCubicSplits

end LiuOppositeSigns
end RealRooted
