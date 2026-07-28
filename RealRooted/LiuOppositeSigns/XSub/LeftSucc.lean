import RealRooted.LiuOppositeSigns.PositiveSplitPair
import RealRooted.QuadraticRoot

/-!
# Liu left-successor x-subtraction base cases

This module contains the left-successor positive-split x-subtraction target
interface and the degree-zero right-endpoint terminal used by the two-degree
factor-return branch.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Positive-split left-successor subtraction-family target.  After a shift
that makes the two endpoints coefficientwise nonnegative, the one-sided pencil
`X * f - μ g`, `μ > 0`, should be real-rooted.  This is the honest
two-degree Liu factor-return leaf left after the false all-combinations route
is removed. -/
def positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄ (r : ℝ),
    PositiveSplitRootCountPair f g →
    HasNonnegCoeffs (f.comp (X + C r)) →
    HasNonnegCoeffs (g.comp (X + C r)) →
    f.natDegree = g.natDegree + 1 →
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits

/-- Predicate-restricted form of the positive-split left-successor
subtraction-family target.  The predicate records endpoint restrictions on
`g.natDegree`. -/
def positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
    (P : ℕ → Prop) : Prop :=
  ∀ ⦃f g : ℝ[X]⦄ (r : ℝ),
    PositiveSplitRootCountPair f g →
    HasNonnegCoeffs (f.comp (X + C r)) →
    HasNonnegCoeffs (g.comp (X + C r)) →
    f.natDegree = g.natDegree + 1 →
    P g.natDegree →
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits

/-- Predicate-restricted positive-split x-subtraction targets transport along
endpoint predicate implications. -/
theorem positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement_of_imp
    {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        Q) :
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      P := by
  intro f g r hpair hfnn hgnn hdeg hgdeg μ hμ
  exact hQ r hpair hfnn hgnn hdeg (hPQ _ hgdeg) μ hμ

/-- The unrestricted positive-split x-sub family is the `P := True` case of
the predicate-restricted target. -/
theorem positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicate_true_of_xSub
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun _ => True) := by
  intro f g r hpair hfnn hgnn hdeg _ μ hμ
  exact hsub r hpair hfnn hgnn hdeg μ hμ

/-- A `P := True` positive-split x-sub family gives the unrestricted target. -/
theorem positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_predicate_true
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyPredicateStatement
        (fun _ => True)) :
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement := by
  intro f g r hpair hfnn hgnn hdeg μ hμ
  exact hsub r hpair hfnn hgnn hdeg trivial μ hμ

/-- Quadratic terminal case for the x-subtraction pencil: a degree-one
positive-leading left endpoint and degree-zero positive-leading right endpoint
give a splitting polynomial `X * p - μ q` for every `μ > 0`. -/
lemma splits_X_mul_sub_C_mul_of_natDegree_one_zero
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p)
    (hq_pos : HasPosLeadingCoeff q) (hpdeg : p.natDegree = 1)
    (hqdeg : q.natDegree = 0) {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  let a := p.coeff 1
  let b := p.coeff 0
  let c := q.coeff 0
  have hp_eq : p = C a * X + C b := by
    simpa [a, b] using Polynomial.eq_X_add_C_of_natDegree_le_one hpdeg.le
  have hq_eq : q = C c := by
    simpa [c] using Polynomial.eq_C_of_natDegree_eq_zero hqdeg
  have ha_pos : 0 < a := by
    simpa [HasPosLeadingCoeff, hpdeg, leadingCoeff, a] using hp_pos
  have hc_pos : 0 < c := by
    simpa [HasPosLeadingCoeff, hqdeg, leadingCoeff, c] using hq_pos
  have hpoly : X * p - C μ * q = C a * X ^ 2 + C b * X + C (-μ * c) := by
    rw [hp_eq, hq_eq]
    simp [C_mul, C_neg]
    ring
  have hprod : 0 < 4 * a * μ * c := by positivity
  have hdisc : 0 ≤ discrim a b (-μ * c) := by
    rw [discrim]
    nlinarith [sq_nonneg b, hprod]
  simpa [hpoly] using quadraticPoly_splits_of_discrim_nonneg ha_pos.ne' hdisc

/-- Degree-zero right endpoint base case for the sign-normalized x-subtraction
leaf. -/
theorem positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (_hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (_hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree + 1)
    (hgdeg : g.natDegree = 0) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg : f.natDegree = 1 := by
    lia
  have hFdeg : (f.comp (X + C r)).natDegree = 1 := by
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 0 := by
    simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_natDegree_one_zero
    (hpair.left_pos.comp_X_add_C r) (hpair.right_pos.comp_X_add_C r)
    hFdeg hGdeg hμ
end LiuOppositeSigns
end RealRooted
