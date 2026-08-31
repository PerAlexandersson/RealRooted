import RealRooted.LiuOppositeSigns.XSub.CubicCubic.LeftRepeated

/-!
# Cubic/cubic x-subtraction theorem and degree-three endpoint wrappers.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- The normalized monic cubic/cubic x-subtraction leaf. -/
theorem xSubCubicCubicSplits :
    xSubCubicCubicSplitsStatement := by
  intro a b c u v w μ hab hbc huv hvw hub hvc hav hbw hc0 hw0 hμ
  by_cases hw_eq : w = 0
  · subst w
    by_cases hc_eq : c = 0
    · subst c
      simpa using xSubCubicCubicSplits_of_upper_roots_zero
        hab huv hav hub hbw hvc hμ
    · simpa using xSubCubicCubicSplits_of_right_upper_root_zero
        hab hbc huv hub hvc hav hμ
  · have hw_lt : w < 0 := lt_of_le_of_ne hw0 hw_eq
    exact xSubCubicCubicSplits_of_negative_endpoints
      hab hbc huv hvw hub hvc hav hbw hc0 hw_lt hμ

/-- The normalized monic cubic/cubic x-subtraction leaf implies the
degree-three/degree-three positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement)
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 3) (hqdeg : q.natDegree = 3)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  obtain ⟨a, b, c, u, v, w, hab, hbc, huv, hvw, hproots, hqroots,
      hpfac, hqfac, hub, hvc, hav, hbw⟩ :=
    exists_roots_order_of_positiveSplitRootCountPair_three_three
      hpair hpdeg hqdeg
  have hc0 : c ≤ 0 := by
    have hc_mem : c ∈ p.roots := by
      rw [hproots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hpnn c hc_mem
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
    X * ((X - C a) * (X - C b) * (X - C c)) -
      C ν * ((X - C u) * (X - C v) * (X - C w))
  have hinner_splits : inner.Splits := by
    dsimp [inner]
    exact hmono hab hbc huv hvw hub hvc hav hbw hc0 hw0 hν_pos
  have hpoly : X * p - C μ * q = C A * inner := by
    rw [hpfac, hqfac]
    dsimp [inner, ν, A, B]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    field_simp [hpair.left_pos.ne']
  rw [hpoly]
  exact hinner_splits.C_mul A

/-- The normalized monic cubic/cubic x-subtraction leaf implies the
degree-three/degree-three positive-split x-subtraction endpoint. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_three
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 3) (hqdeg : q.natDegree = 3)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits :=
  splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_three_of_monic
    xSubCubicCubicSplits hpair hpnn hqnn hpdeg hqdeg hμ

/-- Degree-three right endpoint reduction for the same-degree sign-normalized
x-subtraction leaf, modulo the normalized monic cubic/cubic arithmetic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg : f.natDegree = 3 := by lia
  have hFdeg : (f.comp (X + C r)).natDegree = 3 := by simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 3 := by simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_three_three_of_monic
    hmono (hpair.comp_X_add_C r) hfnn hgnn hFdeg hGdeg hμ

/-- Degree-three right endpoint reduction for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_three
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
    xSubCubicCubicSplits hpair hfnn hgnn hdeg hgdeg

/-- Endpoint cases through right degree three for the same-degree sign-normalized
x-subtraction leaf, modulo the normalized monic cubic/cubic arithmetic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hle_two : g.natDegree ≤ 2
  · exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_two
      hpair hfnn hgnn hdeg hle_two
  · have hthree : g.natDegree = 3 := by lia
    exact
      positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
        hmono hpair hfnn hgnn hdeg hthree

/-- Endpoint cases through right degree three for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree ≤ 3) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
    xSubCubicCubicSplits hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-three right endpoint reduction as a predicate-restricted
same-degree sign-normalized x-subtraction target, modulo the normalized monic
cubic/cubic arithmetic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement) :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact
    positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_three_of_monic
      hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-three right endpoint reduction as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 3) :=
  positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_three_of_monic
    xSubCubicCubicSplits

/-- Pack the endpoint cases through degree three as a predicate-restricted
same-degree sign-normalized x-subtraction target, modulo the normalized monic
cubic/cubic arithmetic leaf. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three_of_monic
    (hmono : xSubCubicCubicSplitsStatement) :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact
    positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_three_of_monic
      hmono hpair hfnn hgnn hdeg hgdeg

/-- Pack the endpoint cases through degree three as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 3) :=
  positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_three_of_monic
    xSubCubicCubicSplits

end LiuOppositeSigns
end RealRooted
