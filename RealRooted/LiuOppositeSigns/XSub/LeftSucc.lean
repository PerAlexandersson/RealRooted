import RealRooted.CubicDiscriminant
import RealRooted.LiuOppositeSigns.PositiveSplitPair
import RealRooted.QuadraticRoot
import RealRooted.SameDegreeQuadraticRootCount

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
  have hq_eq : q = C c := by simpa [c] using Polynomial.eq_C_of_natDegree_eq_zero hqdeg
  have ha_pos : 0 < a := by simpa [HasPosLeadingCoeff, hpdeg, leadingCoeff, a] using hp_pos
  have hc_pos : 0 < c := by simpa [HasPosLeadingCoeff, hqdeg, leadingCoeff, c] using hq_pos
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
  have hfdeg : f.natDegree = 1 := by lia
  have hFdeg : (f.comp (X + C r)).natDegree = 1 := by simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 0 := by simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_natDegree_one_zero
    (hpair.left_pos.comp_X_add_C r) (hpair.right_pos.comp_X_add_C r)
    hFdeg hGdeg hμ

/-- Cubic-discriminant certificate for the degree-two/degree-one x-subtraction
leaf.  The normalized hypotheses say that the quadratic roots `a ≤ b` and
linear root `c` are nonpositive after translation, and that the linear root is
not below the lower quadratic root. -/
def xSubQuadraticLinearCubicDiscrimNonnegStatement : Prop :=
  ∀ {a b c μ : ℝ},
    a ≤ b → a ≤ c → b ≤ 0 → c ≤ 0 → 0 < μ →
      0 ≤ cubicDiscr (X * ((X - C a) * (X - C b)) - C μ * (X - C c))

/-- Explicit discriminant certificate for the normalized case
`a ≤ c ≤ b ≤ 0`. -/
lemma xSubQuadraticLinearCubicDiscrimNonneg_between
    {u v w μ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hμ : 0 < μ) :
    0 ≤ cubicDiscr
      (X * ((X - C (-(u + v + w))) * (X - C (-w))) -
        C μ * (X - C (-(v + w)))) := by
  have hpoly :
      X * ((X - C (-(u + v + w))) * (X - C (-w))) -
          C μ * (X - C (-(v + w))) =
        C 1 * X ^ 3 + C (u + v + 2 * w) * X ^ 2 +
          C ((u + v + w) * w - μ) * X + C (-μ * (v + w)) := by
    simp only [C_add, C_mul, C_neg, C_sub, C_1, C_ofNat]
    ring_nf
  have hdisc :
      cubicDiscr
          (X * ((X - C (-(u + v + w))) * (X - C (-w))) -
            C μ * (X - C (-(v + w)))) =
        (μ - v ^ 2 - v * w) ^ 2 * (4 * μ + w ^ 2) +
          u *
            (μ ^ 2 * u + 20 * μ ^ 2 * v + 4 * μ * u ^ 2 * v +
              12 * μ * u * v ^ 2 + 12 * μ * v ^ 3 + 10 * μ ^ 2 * w +
              2 * μ * u ^ 2 * w + 12 * μ * u * v * w +
              18 * μ * v ^ 2 * w + 8 * μ * u * w ^ 2 + u ^ 3 * w ^ 2 +
              10 * μ * v * w ^ 2 + 4 * u ^ 2 * v * w ^ 2 +
              6 * u * v ^ 2 * w ^ 2 + 4 * v ^ 3 * w ^ 2 +
              2 * μ * w ^ 3 + 2 * u ^ 2 * w ^ 3 + 6 * u * v * w ^ 3 +
              6 * v ^ 2 * w ^ 3 + u * w ^ 4 + 2 * v * w ^ 4) := by
    rw [hpoly, cubicDiscr_of_coeffs]
    ring
  rw [hdisc]
  positivity

/-- Explicit discriminant certificate for the normalized case
`a ≤ b ≤ c ≤ 0`. -/
lemma xSubQuadraticLinearCubicDiscrimNonneg_right
    {u v w μ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hμ : 0 < μ) :
    0 ≤ cubicDiscr
      (X * ((X - C (-(u + v + w))) * (X - C (-(v + w)))) -
        C μ * (X - C (-w))) := by
  have hpoly :
      X * ((X - C (-(u + v + w))) * (X - C (-(v + w)))) -
          C μ * (X - C (-w)) =
        C 1 * X ^ 3 + C (u + 2 * v + 2 * w) * X ^ 2 +
          C ((u + v + w) * (v + w) - μ) * X + C (-μ * w) := by
    simp only [C_add, C_mul, C_neg, C_sub, C_1, C_ofNat]
    ring_nf
  have hdisc :
      cubicDiscr
          (X * ((X - C (-(u + v + w))) * (X - C (-(v + w)))) -
            C μ * (X - C (-w))) =
        (4 * μ + u ^ 2) * (μ - u * v - v ^ 2) ^ 2 +
          w *
            (10 * μ ^ 2 * u + 2 * μ * u ^ 3 + 20 * μ ^ 2 * v +
              10 * μ * u ^ 2 * v + 2 * u ^ 4 * v +
              18 * μ * u * v ^ 2 + 6 * u ^ 3 * v ^ 2 +
              12 * μ * v ^ 3 + 4 * u ^ 2 * v ^ 3 + μ ^ 2 * w +
              8 * μ * u ^ 2 * w + u ^ 4 * w + 12 * μ * u * v * w +
              6 * u ^ 3 * v * w + 12 * μ * v ^ 2 * w +
              6 * u ^ 2 * v ^ 2 * w + 2 * μ * u * w ^ 2 +
              2 * u ^ 3 * w ^ 2 + 4 * μ * v * w ^ 2 +
              4 * u ^ 2 * v * w ^ 2 + u ^ 2 * w ^ 3) := by
    rw [hpoly, cubicDiscr_of_coeffs]
    ring
  rw [hdisc]
  positivity

/-- The cubic-discriminant certificate needed in the degree-two/degree-one
x-subtraction leaf. -/
theorem xSubQuadraticLinearCubicDiscrimNonneg :
    xSubQuadraticLinearCubicDiscrimNonnegStatement := by
  intro a b c μ hab hac hb0 hc0 hμ
  by_cases hcb : c ≤ b
  · let u : ℝ := c - a
    let v : ℝ := b - c
    let w : ℝ := -b
    have hu : 0 ≤ u := by
      dsimp [u]
      linarith
    have hv : 0 ≤ v := by
      dsimp [v]
      linarith
    have hw : 0 ≤ w := by
      dsimp [w]
      linarith
    have hnorm :
        X * ((X - C a) * (X - C b)) - C μ * (X - C c) =
          X * ((X - C (-(u + v + w))) * (X - C (-w))) -
            C μ * (X - C (-(v + w))) := by
      dsimp [u, v, w]
      ring_nf
    rw [hnorm]
    exact xSubQuadraticLinearCubicDiscrimNonneg_between hu hv hw hμ
  · have hbc : b ≤ c := le_of_not_ge hcb
    let u : ℝ := b - a
    let v : ℝ := c - b
    let w : ℝ := -c
    have hu : 0 ≤ u := by
      dsimp [u]
      linarith
    have hv : 0 ≤ v := by
      dsimp [v]
      linarith
    have hw : 0 ≤ w := by
      dsimp [w]
      linarith
    have hnorm :
        X * ((X - C a) * (X - C b)) - C μ * (X - C c) =
          X * ((X - C (-(u + v + w))) * (X - C (-(v + w)))) -
            C μ * (X - C (-w)) := by
      dsimp [u, v, w]
      ring_nf
    rw [hnorm]
    exact xSubQuadraticLinearCubicDiscrimNonneg_right hu hv hw hμ

/-- If the normalized cubic-discriminant certificate is available, then the
degree-two/degree-one x-subtraction pencil splits. -/
lemma splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_one_of_cubicDiscrim
    (harith : xSubQuadraticLinearCubicDiscrimNonnegStatement)
    {p q : ℝ[X]} (hpair : PositiveSplitRootCountPair p q)
    (hpnn : HasNonnegCoeffs p) (hqnn : HasNonnegCoeffs q)
    (hpdeg : p.natDegree = 2) (hqdeg : q.natDegree = 1)
    {μ : ℝ} (hμ : 0 < μ) :
    (X * p - C μ * q).Splits := by
  obtain ⟨a, b, hab, hproots, hpfac⟩ :=
    exists_roots_pair_of_splits_natDegree_two hpair.left_splits hpdeg
  obtain ⟨c, hqroots, hqfac⟩ :=
    exists_linear_factor_of_splits_natDegree_one hpair.right_splits hqdeg
  have hac : a ≤ c :=
    left_root_le_singleton_root_of_positiveSplitRootCountPair_two_one
      hpair hab hproots hqroots
  have hb0 : b ≤ 0 := by
    have hb_mem : b ∈ p.roots := by
      rw [hproots]
      simp only [Multiset.insert_eq_cons]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hpnn b hb_mem
  have hc0 : c ≤ 0 := by
    have hc_mem : c ∈ q.roots := by
      rw [hqroots]
      simp
    exact roots_nonpos_of_hasNonnegCoeffs hqnn c hc_mem
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
  let inner : ℝ[X] := X * ((X - C a) * (X - C b)) - C ν * (X - C c)
  have hinner_deg : inner.natDegree ≤ 3 := by
    dsimp [inner]
    compute_degree
  have hinner_disc : 0 ≤ cubicDiscr inner := by
    dsimp [inner]
    exact harith hab hac hb0 hc0 hν_pos
  have hinner_splits : inner.Splits :=
    splits_of_natDegree_le_three_cubicDiscr_nonneg hinner_deg hinner_disc
  have hpfacA : p = C A * ((X - C a) * (X - C b)) := by simpa [A] using hpfac
  have hqfacB : q = C B * (X - C c) := by simpa [B] using hqfac
  have hpoly : X * p - C μ * q = C A * inner := by
    rw [hpfacA, hqfacB]
    dsimp [inner, ν]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    field_simp [hA_pos.ne']
  rw [hpoly]
  exact hinner_splits.C_mul A

/-- Degree-one right endpoint reduction for the sign-normalized
x-subtraction leaf, modulo the explicit cubic-discriminant certificate. -/
theorem
    positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one_of_cubicDiscrim
    (harith : xSubQuadraticLinearCubicDiscrimNonnegStatement)
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree + 1)
    (hgdeg : g.natDegree = 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg_shift : (f.comp (X + C r)).natDegree = 2 := by
    have hfdeg : f.natDegree = 2 := by lia
    simpa [Polynomial.natDegree_comp] using hfdeg
  have hgdeg_shift : (g.comp (X + C r)).natDegree = 1 := by
    simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_positiveSplit_natDegree_two_one_of_cubicDiscrim
    harith (hpair.comp_X_add_C r) hfnn hgnn hfdeg_shift hgdeg_shift hμ

/-- Degree-one right endpoint case for the sign-normalized x-subtraction
leaf. -/
theorem positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hfnn : HasNonnegCoeffs (f.comp (X + C r)))
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree + 1)
    (hgdeg : g.natDegree = 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits :=
  positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one_of_cubicDiscrim
    xSubQuadraticLinearCubicDiscrimNonneg hpair hfnn hgnn hdeg hgdeg
end LiuOppositeSigns
end RealRooted
