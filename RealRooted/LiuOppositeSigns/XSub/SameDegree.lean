import RealRooted.LiuOppositeSigns.PositiveSplitPair
import RealRooted.QuadraticRoot

/-!
# Liu same-degree and right-successor x-subtraction base cases

This module contains the generic positive-split translated x-subtraction
interface for the same-degree and right-successor branches, together with the
constant and linear endpoint cases.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Positive-split x-subtraction target for an arbitrary endpoint degree
relation.  This is the common statement shape behind the same-, right-successor,
and left-successor translated half-pencil leaves. -/
def positiveSplitTranslatedXSubRightFamilyRelationStatement
    (R : ℕ → ℕ → Prop) : Prop :=
  ∀ ⦃f g : ℝ[X]⦄ (r : ℝ),
    PositiveSplitRootCountPair f g →
    HasNonnegCoeffs (f.comp (X + C r)) →
    HasNonnegCoeffs (g.comp (X + C r)) →
    R f.natDegree g.natDegree →
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits

/-- Predicate-restricted positive-split x-subtraction target for an arbitrary
endpoint degree relation.  The predicate records endpoint restrictions on
`g.natDegree`. -/
def positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement
    (R : ℕ → ℕ → Prop) (P : ℕ → Prop) : Prop :=
  ∀ ⦃f g : ℝ[X]⦄ (r : ℝ),
    PositiveSplitRootCountPair f g →
    HasNonnegCoeffs (f.comp (X + C r)) →
    HasNonnegCoeffs (g.comp (X + C r)) →
    R f.natDegree g.natDegree →
    P g.natDegree →
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits

/-- Predicate-restricted relation x-subtraction targets transport along
endpoint predicate implications. -/
theorem positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement_of_imp
    {R : ℕ → ℕ → Prop} {P Q : ℕ → Prop} (hPQ : ∀ n, P n → Q n)
    (hQ :
      positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement R Q) :
    positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement R P := by
  intro f g r hpair hfnn hgnn hdeg hgdeg μ hμ
  exact hQ r hpair hfnn hgnn hdeg (hPQ _ hgdeg) μ hμ

/-- The unrestricted relation x-subtraction target is the `P := True` case of
the predicate-restricted target. -/
theorem positiveSplitTranslatedXSubRightFamilyPredicateRelation_true_of_relation
    {R : ℕ → ℕ → Prop}
    (hsub : positiveSplitTranslatedXSubRightFamilyRelationStatement R) :
    positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement R
      (fun _ => True) := by
  intro f g r hpair hfnn hgnn hdeg _ μ hμ
  exact hsub r hpair hfnn hgnn hdeg μ hμ

/-- A `P := True` relation x-subtraction target gives the unrestricted
relation target. -/
theorem positiveSplitTranslatedXSubRightFamilyRelation_of_predicate_true
    {R : ℕ → ℕ → Prop}
    (hsub :
      positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement R
        (fun _ => True)) :
    positiveSplitTranslatedXSubRightFamilyRelationStatement R := by
  intro f g r hpair hfnn hgnn hdeg μ hμ
  exact hsub r hpair hfnn hgnn hdeg trivial μ hμ

/-- Same-degree positive-split subtraction-family target. -/
def positiveSplitSameDegreeTranslatedXSubRightFamilyStatement : Prop :=
  positiveSplitTranslatedXSubRightFamilyRelationStatement
    (fun m n => m = n)

/-- Predicate-restricted same-degree positive-split subtraction-family target. -/
def positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
    (P : ℕ → Prop) : Prop :=
  positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement
    (fun m n => m = n) P

/-- Right-successor positive-split subtraction-family target. -/
def positiveSplitRightSuccDegreeTranslatedXSubRightFamilyStatement : Prop :=
  positiveSplitTranslatedXSubRightFamilyRelationStatement
    (fun m n => n = m + 1)

/-- Predicate-restricted right-successor positive-split subtraction-family
target. -/
def positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
    (P : ℕ → Prop) : Prop :=
  positiveSplitTranslatedXSubRightFamilyPredicateRelationStatement
    (fun m n => n = m + 1) P

/-- Degree guardrail for the translated x-subtraction endpoint: in the
left-successor case, `g.comp (X + C r)` and `X * f.comp (X + C r)` differ by
two degrees, so this endpoint cannot be proved by a direct `Prec` witness. -/
theorem not_positiveSplitLeftSuccDegreeTranslatedXPrec
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hdeg : f.natDegree = g.natDegree + 1) :
    ¬ Prec (g.comp (X + C r)) (X * f.comp (X + C r)) := by
  intro hprec
  have hF_ne : f.comp (X + C r) ≠ 0 :=
    (hpair.left_pos.comp_X_add_C r).ne_zero
  have hXF_deg :
      (X * f.comp (X + C r)).natDegree =
        (f.comp (X + C r)).natDegree + 1 :=
    natDegree_X_mul hF_ne
  have hF_deg : (f.comp (X + C r)).natDegree = f.natDegree := by
    simp [Polynomial.natDegree_comp]
  have hG_deg : (g.comp (X + C r)).natDegree = g.natDegree := by
    simp [Polynomial.natDegree_comp]
  have hgap :
      (g.comp (X + C r)).natDegree + 1 <
        (X * f.comp (X + C r)).natDegree := by
    rw [hXF_deg, hF_deg, hG_deg]
    lia
  exact not_prec_of_left_natDegree_succ_lt_right hgap hprec

/-- Quadratic terminal case for the x-subtraction pencil with two degree-one
endpoints and a nonnegative constant term on the right endpoint. -/
lemma splits_X_mul_sub_C_mul_of_natDegree_one_one_right_nonneg
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p)
    (hpdeg : p.natDegree = 1) (hqdeg : q.natDegree = 1)
    (hqnn : HasNonnegCoeffs q) {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  let a := p.coeff 1
  let b := p.coeff 0
  let c := q.coeff 1
  let d := q.coeff 0
  have hp_eq : p = C a * X + C b := by
    simpa [a, b] using Polynomial.eq_X_add_C_of_natDegree_le_one hpdeg.le
  have hq_eq : q = C c * X + C d := by
    simpa [c, d] using Polynomial.eq_X_add_C_of_natDegree_le_one hqdeg.le
  have ha_pos : 0 < a := by
    simpa [HasPosLeadingCoeff, hpdeg, leadingCoeff, a] using hp_pos
  have hd_nonneg : 0 ≤ d := by
    simpa [d] using hqnn 0
  have hpoly :
      X * p - C μ * q =
        C a * X ^ 2 + C (b - μ * c) * X + C (-μ * d) := by
    rw [hp_eq, hq_eq]
    simp [C_mul, C_sub, C_neg]
    ring
  have hprod_nonneg : 0 ≤ 4 * a * μ * d := by positivity
  have hdisc : 0 ≤ discrim a (b - μ * c) (-μ * d) := by
    rw [discrim]
    nlinarith [sq_nonneg (b - μ * c), hprod_nonneg]
  simpa [hpoly] using quadraticPoly_splits_of_discrim_nonneg ha_pos.ne' hdisc

/-- Linear-or-constant terminal case for the x-subtraction pencil. -/
lemma splits_X_mul_sub_C_mul_of_left_natDegree_zero_right_natDegree_le_one
    {p q : ℝ[X]} (hpdeg : p.natDegree = 0) (hqdeg : q.natDegree ≤ 1)
    (μ : ℝ) :
    (X * p - C μ * q).Splits := by
  apply Polynomial.Splits.of_natDegree_le_one
  have hleft : (X * p).natDegree ≤ 1 := by
    calc
      (X * p).natDegree ≤ X.natDegree + p.natDegree :=
        Polynomial.natDegree_mul_le
      _ = 1 := by simp [hpdeg]
  have hright : (C μ * q).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le μ q).trans hqdeg
  simpa using Polynomial.natDegree_sub_le_of_le hleft hright

/-- Degree-zero right endpoint base case for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
    {f g : ℝ[X]} {r : ℝ}
    (_hpair : PositiveSplitRootCountPair f g)
    (_hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (_hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 0) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ _hμ
  have hfdeg : f.natDegree = 0 := by
    lia
  have hFdeg : (f.comp (X + C r)).natDegree = 0 := by
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree ≤ 1 := by
    have hGdeg_eq : (g.comp (X + C r)).natDegree = 0 := by
      simpa [Polynomial.natDegree_comp] using hgdeg
    exact hGdeg_eq.le.trans (by norm_num)
  exact splits_X_mul_sub_C_mul_of_left_natDegree_zero_right_natDegree_le_one
    hFdeg hGdeg μ

/-- Degree-one right endpoint case for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_one
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (_hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg : f.natDegree = 1 := by
    lia
  have hFdeg : (f.comp (X + C r)).natDegree = 1 := by
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 1 := by
    simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_natDegree_one_one_right_nonneg
    (hpair.left_pos.comp_X_add_C r) hFdeg hGdeg hgnn hμ

/-- Low-degree right endpoint cases for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_one
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree ≤ 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hzero : g.natDegree = 0
  · exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
      hpair hfnn hgnn hdeg hzero
  · have hone : g.natDegree = 1 := by
      lia
    exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_one
      hpair hfnn hgnn hdeg hone

/-- Degree-one right endpoint base case for the right-successor
sign-normalized x-subtraction leaf. -/
theorem positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one
    {f g : ℝ[X]} {r : ℝ}
    (_hpair : PositiveSplitRootCountPair f g)
    (_hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (_hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hgdeg : g.natDegree = 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ _hμ
  have hfdeg : f.natDegree = 0 := by
    lia
  have hFdeg : (f.comp (X + C r)).natDegree = 0 := by
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree ≤ 1 := by
    simpa [Polynomial.natDegree_comp] using hgdeg.le
  exact splits_X_mul_sub_C_mul_of_left_natDegree_zero_right_natDegree_le_one
    hFdeg hGdeg μ

/-- Pack the degree-zero right endpoint terminal as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_zero :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 0) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
    hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-one right endpoint terminal as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_one :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 1) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_one
    hpair hfnn hgnn hdeg hgdeg

/-- Pack the low-degree right endpoint terminals as a predicate-restricted
same-degree sign-normalized x-subtraction target. -/
theorem
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_le_one :
    positiveSplitSameDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n ≤ 1) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_one
    hpair hfnn hgnn hdeg hgdeg

/-- Pack the degree-one right endpoint terminal as a predicate-restricted
right-successor sign-normalized x-subtraction target. -/
theorem
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicate_of_right_natDegree_one :
    positiveSplitRightSuccDegreeTranslatedXSubRightFamilyPredicateStatement
      (fun n => n = 1) := by
  intro f g r hpair hfnn hgnn hdeg hgdeg
  exact positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one
    hpair hfnn hgnn hdeg hgdeg


end LiuOppositeSigns
end RealRooted
