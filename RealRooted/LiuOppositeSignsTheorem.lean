import RealRooted.CommonInterleaverTwo
import RealRooted.LiuOppositeSigns
import RealRooted.SameDegreeCountFromAnalytic

/-!
# Liu opposite-sign compatibility theorem targets

This module connects the lightweight root-count scaffolding in
`RealRooted.LiuOppositeSigns` to the existing `Compatible` API.  The hard
mathematical content of Lily L. Liu's Theorem 2.1 is kept as a named statement
so later proof work can target a stable interface.
-/

open Polynomial

namespace RealRooted
namespace LiuOppositeSigns

/-- Liu Theorem 2.1, stated against the project's `Compatible` predicate:
for two real-rooted polynomials with opposite leading signs, compatibility is
equivalent to the appropriate largest-root deletion branch satisfying Liu's
closed-at-or-above root-count condition. -/
def theorem21CompatibleRootCountStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    (Compatible f g ↔ theorem21RootCountBranches f g)

/-- Nonconstant form of Liu Theorem 2.1.  This is the induction-friendly
version of the statement because the root-count branches delete a largest root
from each polynomial. -/
def theorem21CompatibleRootCountNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      (Compatible f g ↔ theorem21RootCountBranches f g)

/-- The paper-shaped statement implies its nonconstant restriction. -/
theorem theorem21CompatibleRootCountNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  fun f g hf hg hsgn _ _ => h f g hf hg hsgn

/-- Projection form of `theorem21CompatibleRootCountStatement`. -/
theorem compatible_iff_theorem21RootCountBranches
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  h f g hf hg hsgn

/-- Projection form of the nonconstant Liu Theorem 2.1 statement. -/
theorem compatible_iff_theorem21RootCountBranches_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0) :
    Compatible f g ↔ theorem21RootCountBranches f g :=
  h f g hf hg hsgn hf_deg hg_deg

/-- Forward direction of Liu Theorem 2.1 as a reusable projection. -/
theorem theorem21RootCountBranches_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  (h f g hf hg hsgn).1 hcompat

/-- Forward direction of the nonconstant Liu Theorem 2.1 statement. -/
theorem theorem21RootCountBranches_of_compatible_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches f g :=
  (h f g hf hg hsgn hf_deg hg_deg).1 hcompat

/-- Reverse direction of Liu Theorem 2.1 as a reusable projection. -/
theorem compatible_of_theorem21RootCountBranches
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  (h f g hf hg hsgn).2 hbranches

/-- Reverse direction of the nonconstant Liu Theorem 2.1 statement. -/
theorem compatible_of_theorem21RootCountBranches_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hbranches : theorem21RootCountBranches f g) :
    Compatible f g :=
  (h f g hf hg hsgn hf_deg hg_deg).2 hbranches

/-- Forward direction of Liu Theorem 2.1 with the branch predicate swapped. -/
theorem theorem21RootCountBranches_symm_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches g f :=
  theorem21RootCountBranches_of_compatible h hg hf hsgn.symm hcompat.comm

/-- Forward direction of the nonconstant statement with the branch predicate
swapped. -/
theorem theorem21RootCountBranches_symm_of_compatible_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21RootCountBranches g f :=
  theorem21RootCountBranches_of_compatible_nonconstant h hg hf hsgn.symm
    hg_deg hf_deg hcompat.comm

/-- Reverse direction of Liu Theorem 2.1 with the branch predicate swapped. -/
theorem compatible_of_theorem21RootCountBranches_symm
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hbranches : theorem21RootCountBranches g f) :
    Compatible f g :=
  (compatible_of_theorem21RootCountBranches h hg hf hsgn.symm hbranches).comm

/-- Reverse direction of the nonconstant statement with the branch predicate
swapped. -/
theorem compatible_of_theorem21RootCountBranches_symm_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hbranches : theorem21RootCountBranches g f) :
    Compatible f g :=
  (compatible_of_theorem21RootCountBranches_nonconstant h hg hf hsgn.symm
    hg_deg hf_deg hbranches).comm

/-- Projection form of Liu Theorem 2.1 after swapping the two polynomials. -/
theorem compatible_iff_theorem21RootCountBranches_symm
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g) :
    Compatible f g ↔ theorem21RootCountBranches g f :=
  ⟨theorem21RootCountBranches_symm_of_compatible h hf hg hsgn,
    compatible_of_theorem21RootCountBranches_symm h hf hg hsgn⟩

/-- Projection form of the nonconstant Liu Theorem 2.1 statement after
swapping the two polynomials. -/
theorem compatible_iff_theorem21RootCountBranches_symm_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0) :
    Compatible f g ↔ theorem21RootCountBranches g f :=
  ⟨theorem21RootCountBranches_symm_of_compatible_nonconstant h hf hg hsgn
      hf_deg hg_deg,
    compatible_of_theorem21RootCountBranches_symm_nonconstant h hf hg hsgn
      hf_deg hg_deg⟩

theorem
    rootCountAtOrAbove_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    ∀ x : ℝ,
      |((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ))| ≤ 2 :=
  rootCountAtOrAbove_abs_sub_le_two_of_theorem21RootCountBranches hsgn
    (theorem21RootCountBranches_of_compatible h hf hg hsgn hcompat)

theorem
    rootCountAtOrAbove_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    ∀ x : ℝ,
      |((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ))| ≤ 2 :=
  rootCountAtOrAbove_abs_sub_le_two_of_theorem21RootCountBranches hsgn
    (theorem21RootCountBranches_of_compatible_nonconstant h hf hg hsgn
      hf_deg hg_deg hcompat)

theorem
    rootCountAtOrAbove_branch_bounds_of_compatible_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    (∀ x : ℝ,
      ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 2 ∧
        ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 1) ∨
      (∀ x : ℝ,
        ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 1 ∧
          ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 2) :=
  rootCountAtOrAbove_branch_bounds_of_theorem21RootCountBranches hsgn
    (theorem21RootCountBranches_of_compatible h hf hg hsgn hcompat)

theorem
    rootCountAtOrAbove_branch_bounds_of_compatible_of_theorem21CompatibleRootCount_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    (∀ x : ℝ,
      ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 2 ∧
        ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 1) ∨
      (∀ x : ℝ,
        ((rootCountAtOrAbove f x : ℤ) - (rootCountAtOrAbove g x : ℤ)) ≤ 1 ∧
          ((rootCountAtOrAbove g x : ℤ) - (rootCountAtOrAbove f x : ℤ)) ≤ 2) :=
  rootCountAtOrAbove_branch_bounds_of_theorem21RootCountBranches hsgn
    (theorem21RootCountBranches_of_compatible_nonconstant h hf hg hsgn
      hf_deg hg_deg hcompat)

theorem theorem21PositiveDeletionCountBranches_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21PositiveDeletionCountBranches f g :=
  theorem21PositiveDeletionCountBranches_of_theorem21RootCountBranches hf hg hsgn
    (theorem21RootCountBranches_of_compatible h hf hg hsgn hcompat)

theorem theorem21PositiveDeletionCountBranches_of_compatible_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21PositiveDeletionCountBranches f g :=
  theorem21PositiveDeletionCountBranches_of_theorem21RootCountBranches hf hg hsgn
    (theorem21RootCountBranches_of_compatible_nonconstant h hf hg hsgn
      hf_deg hg_deg hcompat)

/-- Same-degree positive-leading root-count leaf, phrased as a
`PositiveSplitRootCountPair` production target. -/
def positiveSplitSameDegreeRootCountAboveNonRootStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    PositiveSplitRootCountPair f g

/-- Succ-degree positive-leading root-count leaf, phrased as a
`PositiveSplitRootCountPair` production target. -/
def positiveSplitSuccDegreeRootCountAboveNonRootStatement : Prop :=
  ∀ ⦃f g : ℝ[X]⦄,
    HasPosLeadingCoeff f →
    HasPosLeadingCoeff g →
    HasNonnegCoeffs f →
    HasNonnegCoeffs g →
    PosComboRealRooted f g →
    g.natDegree = f.natDegree + 1 →
    (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
    f.Splits →
    PositiveSplitRootCountPair f g

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

/-- A positive-leading, splitting, degree-one polynomial has one real root and
factors as its leading coefficient times the corresponding monic factor. -/
lemma exists_linear_factor_of_splits_natDegree_one
    {p : ℝ[X]} (hp_split : p.Splits) (hpdeg : p.natDegree = 1) :
    ∃ a : ℝ, p.roots = {a} ∧ p = C p.leadingCoeff * (X - C a) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, p.roots = {a} :=
    Multiset.card_eq_one.mp (by rw [card_roots_of_splits hp_split, hpdeg])
  refine ⟨a, ha, ?_⟩
  have hprod := hp_split.eq_prod_roots
  rw [ha] at hprod
  simpa using hprod

/-- In the `(2, 1)` positive split root-count case, the linear root cannot lie
strictly below both quadratic roots. -/
lemma left_root_le_singleton_root_of_positiveSplitRootCountPair_two_one
    {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g)
    {a b c : ℝ} (hab : a ≤ b) (hfroots : f.roots = {a, b})
    (hgroots : g.roots = {c}) :
    a ≤ c := by
  by_contra hac
  have hca : c < a := lt_of_not_ge hac
  let x : ℝ := (a + c) / 2
  have hxa : x ≤ a := by
    dsimp [x]
    linarith
  have hxb : x ≤ b := hxa.trans hab
  have hcount := h.count.left_sub_le_one x
  have hf_count : rootCountAtOrAbove f x = 2 := by
    rw [rootCountAtOrAbove, hfroots]
    simp only [Multiset.insert_eq_cons]
    rw [Multiset.filter_cons_of_pos ({b} : Multiset ℝ) hxa]
    rw [Multiset.filter_singleton (fun r : ℝ => x ≤ r), if_pos hxb]
    simp
  have hg_count : rootCountAtOrAbove g x = 0 := by
    rw [rootCountAtOrAbove, hgroots]
    rw [Multiset.filter_singleton (fun r : ℝ => x ≤ r),
      if_neg (by dsimp [x]; linarith)]
    simp
  rw [hf_count, hg_count] at hcount
  norm_num at hcount

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
  have hpfacA : p = C A * ((X - C a) * (X - C b)) := by
    simpa [A] using hpfac
  have hqfacB : q = C B * (X - C c) := by
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
    have hfdeg : f.natDegree = 2 := by
      lia
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

theorem posComboNoCommonSameDegreeRootCountAboveNonRoot_of_positiveSplit
    (hpack : positiveSplitSameDegreeRootCountAboveNonRootStatement) :
    PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno x hfx hgx
  exact (hpack hf_pos hg_pos hfnn hgnn hfg hdeg hno).sameDegreeRootCountAboveNonRoot
    hdeg x hfx hgx

theorem posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_positiveSplit
    (hpack : positiveSplitSuccDegreeRootCountAboveNonRootStatement) :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split x hfx hgx
  exact (hpack hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split)
    |>.succDegreeRootCountAboveNonRoot hdeg x hfx hgx

/-- A strict-upper non-root count proof supplies the positive-split
same-degree Liu root-count package. -/
theorem positiveSplitSameDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot
    (hcount : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement) :
    positiveSplitSameDegreeRootCountAboveNonRootStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_split : f.Splits :=
    (hfg.isRealRooted_left_of_sameDegree hf_pos hg_pos hdeg).2
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_sameDegree hf_pos hg_pos hdeg).2
  exact PositiveSplitRootCountPair.of_rootCountAbove_bounds_of_nonRoot
    hf_pos hg_pos hf_split hg_split
    (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno)

/-- A strict-upper non-root count proof supplies the positive-split
successor-degree Liu root-count package. -/
theorem positiveSplitSuccDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot
    (hcount : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    positiveSplitSuccDegreeRootCountAboveNonRootStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split
  have hg_split : g.Splits :=
    (hfg.isRealRooted_right_of_succDegree hf_pos hg_pos hdeg).2
  exact PositiveSplitRootCountPair.of_rootCountAbove_bounds_of_nonRoot
    hf_pos hg_pos hf_split hg_split
    (hcount hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split)

/-- The existing same-degree analytic count spine supplies the positive-split
same-degree Liu root-count package. -/
theorem positiveSplitSameDegreeRootCountAboveNonRoot_from_analytic :
    positiveSplitSameDegreeRootCountAboveNonRootStatement :=
  positiveSplitSameDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot
    _root_.RealRooted.posComboNoCommonSameDegreeRootCountAboveNonRootNonneg_from_analytic

/-- The common-left-interleaver reduction supplies the positive-split
successor-degree Liu root-count package. -/
theorem positiveSplitSuccDegreeRootCountAboveNonRoot_of_commonLeftInterleaver
    (hleft : PosComboNoCommonSuccDegreeCommonLeftInterleaverNonnegStatement) :
    positiveSplitSuccDegreeRootCountAboveNonRootStatement :=
  positiveSplitSuccDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot
    (posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_commonLeftInterleaver
      hleft)

/-- A compatible succ-degree non-root count leaf supplies the positive-split
successor-degree Liu root-count package. -/
theorem positiveSplitSuccDegreeRootCountAboveNonRoot_of_compatibleRootCount
    (hcount : CompatibleSuccDegreeRootCountAboveNonRootStatement) :
    positiveSplitSuccDegreeRootCountAboveNonRootStatement :=
  positiveSplitSuccDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot
    (_root_.RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_compatible
      hcount)

/-- Closed-segment endpoint count equality supplies the positive-split
successor-degree Liu root-count package. -/
theorem positiveSplitSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq
    (hcount : CompatibleSuccDegreeClosedSegmentCountEqStatement) :
    positiveSplitSuccDegreeRootCountAboveNonRootStatement :=
  positiveSplitSuccDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot
    (_root_.RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_closedSegmentCountEq
      hcount)

/-- Closed-segment no-gap-two supplies the positive-split successor-degree
Liu root-count package. -/
theorem positiveSplitSuccDegreeRootCountAboveNonRoot_of_closedSegmentNoGapTwo
    (hclosed : CompatibleSuccDegreeClosedSegmentNoGapTwoStatement) :
    positiveSplitSuccDegreeRootCountAboveNonRootStatement :=
  positiveSplitSuccDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot
    (_root_.RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_closedSegmentNoGapTwo
      hclosed)

/-- Right-pencil no-gap-two supplies the positive-split successor-degree Liu
root-count package. -/
theorem positiveSplitSuccDegreeRootCountAboveNonRoot_of_rightFamilyNoGapTwo
    (hright : CompatibleSuccDegreeRightFamilyNoGapTwoStatement) :
    positiveSplitSuccDegreeRootCountAboveNonRootStatement :=
  positiveSplitSuccDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot
    (_root_.RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_rightFamilyNoGapTwo
      hright)

/-- Endpoint-sign no-gap-two supplies the positive-split successor-degree Liu
root-count package. -/
theorem positiveSplitSuccDegreeRootCountAboveNonRoot_of_endpointSignNoGapTwo
    (hsign : CompatibleSuccDegreeEndpointSignNoGapTwoStatement) :
    positiveSplitSuccDegreeRootCountAboveNonRootStatement :=
  positiveSplitSuccDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot
    (_root_.RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_endpointSignNoGapTwo
      hsign)

/-- Lower endpoint-sign no-gap supplies the positive-split successor-degree
Liu root-count package. -/
theorem positiveSplitSuccDegreeRootCountAboveNonRoot_of_endpointSignLower
    (hlower : CompatibleSuccDegreeEndpointSignLowerNoGapStatement) :
    positiveSplitSuccDegreeRootCountAboveNonRootStatement :=
  positiveSplitSuccDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot
    (_root_.RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_endpointSignLower
      hlower)

/-- Exact lower-count endpoint comparison supplies the positive-split
successor-degree Liu root-count package. -/
theorem positiveSplitSuccDegreeRootCountAboveNonRoot_of_lowerCountEq
    (hcount : CompatibleSuccDegreeEndpointSignLowerCountEqStatement) :
    positiveSplitSuccDegreeRootCountAboveNonRootStatement :=
  positiveSplitSuccDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot
    (_root_.RealRooted.posComboNoCommonSuccDegreeRootCountAboveNonRoot_of_lowerCountEq
      hcount)

namespace PositiveSplitRootCountPair

theorem pairHasCommonInterleaver_of_sameDegree {f g : ℝ[X]}
    (h : PositiveSplitRootCountPair f g) (hdeg : g.natDegree = f.natDegree) :
    ∃ h' : ℝ[X], Prec f h' ∧ Prec g h' := by
  have hcount : ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≤ 1 ∧
        ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≤ 1 :=
    sameDegreeRootCountAbove_of_nonRoot_bound
      h.left_pos.ne_zero h.right_pos.ne_zero
      (fun _ hfx hgx => h.rootCountAbove_bounds_of_nonRoot hfx hgx)
  have hcross :=
    rootCrossing_of_rootCountAbove_diff_le_one
      h.left_splits h.right_splits hdeg hcount
  have hlenf : (rootSeqDesc f).length = f.natDegree :=
    rootSeqDesc_length h.left_splits
  have hleng : (rootSeqDesc g).length = g.natDegree :=
    rootSeqDesc_length h.right_splits
  exact
    pairHasCommonInterleaver_of_sameDegree_slotIntersections
      h.left_pos.ne_zero h.right_pos.ne_zero h.left_splits h.right_splits hdeg <|
        fun j hj =>
          rootSlotInterval_inter_nonempty_of_sameDegree_crossing
            (rootSeqDesc f) (rootSeqDesc g)
            rootSeqDesc_pairwise rootSeqDesc_pairwise
            (by rw [hleng, hlenf, hdeg])
            (fun k hk1 hk2 => hcross.1 k hk1 (by rw [hlenf] at hk2; exact hk2))
            (fun k hk1 hk2 => hcross.2 k hk1 (by rw [hlenf] at hk2; exact hk2))
            j (by rw [hlenf]; exact hj) (by rw [hleng, hdeg]; exact hj)

theorem pairHasCommonInterleaver_of_succDegree {f g : ℝ[X]}
    (h : PositiveSplitRootCountPair f g)
    (hdeg : g.natDegree = f.natDegree + 1) :
    ∃ h' : ℝ[X], Prec f h' ∧ Prec g h' := by
  have hcount : ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card ≤ 1 ∧
        ((g.roots.filter (x < ·)).card : ℤ) -
          (f.roots.filter (x < ·)).card ≤ 1 :=
    sameDegreeRootCountAbove_of_nonRoot_bound
      h.left_pos.ne_zero h.right_pos.ne_zero
      (fun _ hfx hgx => h.rootCountAbove_bounds_of_nonRoot hfx hgx)
  have hcross :=
    succDegreeRootCrossing_of_rootCountAbove
      h.left_splits h.right_splits hdeg hcount
  have hlenf : (rootSeqDesc f).length = f.natDegree :=
    rootSeqDesc_length h.left_splits
  have hleng : (rootSeqDesc g).length = g.natDegree :=
    rootSeqDesc_length h.right_splits
  exact
    pairHasCommonInterleaver_of_succDegree_slotIntersections
      h.left_pos.ne_zero h.right_pos.ne_zero h.left_splits h.right_splits hdeg <|
        fun j hj =>
          rootSlotInterval_inter_nonempty_of_crossing
            (rootSeqDesc f) (rootSeqDesc g)
            rootSeqDesc_pairwise rootSeqDesc_pairwise
            (by rw [hleng, hlenf, hdeg])
            (fun k hk1 hk2 => hcross.1 k hk1 (by rw [hlenf] at hk2; exact hk2))
            (fun k hk1 hk2 => hcross.2 k hk1 (by rw [hlenf] at hk2; exact hk2))
            j (by rw [hlenf]; exact hj)
            (by
              rw [hleng, hdeg]
              exact Nat.lt_succ_of_lt hj)

/-- Common-interleaver constructor for the reverse successor-degree
orientation. -/
theorem pairHasCommonInterleaver_of_leftSuccDegree {f g : ℝ[X]}
    (h : PositiveSplitRootCountPair f g)
    (hdeg : f.natDegree = g.natDegree + 1) :
    ∃ h' : ℝ[X], Prec f h' ∧ Prec g h' := by
  obtain ⟨h', hgh, hfh⟩ := h.symm.pairHasCommonInterleaver_of_succDegree hdeg
  exact ⟨h', hfh, hgh⟩

/-- Any positive-leading split pair with Liu-compatible root counts has a
common interleaver. -/
theorem pairHasCommonInterleaver {f g : ℝ[X]}
    (h : PositiveSplitRootCountPair f g) :
    ∃ h' : ℝ[X], Prec f h' ∧ Prec g h' := by
  have hgap := h.natDegree_abs_sub_le_one
  have hleft : f.natDegree ≤ g.natDegree + 1 := by
    have hle := (abs_le.mp hgap).2
    have : (f.natDegree : ℤ) ≤ (g.natDegree : ℤ) + 1 := by linarith
    exact_mod_cast this
  have hright : g.natDegree ≤ f.natDegree + 1 := by
    have hle := (abs_le.mp hgap).1
    have : (g.natDegree : ℤ) ≤ (f.natDegree : ℤ) + 1 := by linarith
    exact_mod_cast this
  by_cases hfg_eq : f.natDegree = g.natDegree
  · exact h.pairHasCommonInterleaver_of_sameDegree hfg_eq.symm
  · rcases Nat.lt_or_gt_of_ne hfg_eq with hfg_lt | hgf_lt
    · have hdeg : g.natDegree = f.natDegree + 1 :=
        Nat.le_antisymm hright (Nat.succ_le_of_lt hfg_lt)
      exact h.pairHasCommonInterleaver_of_succDegree hdeg
    · have hdeg : f.natDegree = g.natDegree + 1 :=
        Nat.le_antisymm hleft (Nat.succ_le_of_lt hgf_lt)
      exact h.pairHasCommonInterleaver_of_leftSuccDegree hdeg

/-- Liu-compatible positive-leading split pairs are compatible. -/
theorem compatible {f g : ℝ[X]} (h : PositiveSplitRootCountPair f g) :
    Compatible f g := by
  obtain ⟨k, hfk, hgk⟩ := h.pairHasCommonInterleaver
  exact Compatible.of_commonInterleaver hfk hgk h.left_pos h.right_pos

/-- A common-right-interleaver witness is unchanged by removing a negation
from the left endpoint, since `Prec` only depends on the roots. -/
theorem pairHasCommonInterleaver_of_neg_left {f g : ℝ[X]}
    (h : PositiveSplitRootCountPair (-f) g) :
    ∃ k : ℝ[X], Prec f k ∧ Prec g k := by
  obtain ⟨k, hfk, hgk⟩ := h.pairHasCommonInterleaver
  refine ⟨k, ?_, hgk⟩
  have hscale : Prec (C (-1 : ℝ) * (-f)) k :=
    prec_C_mul_left hfk (by norm_num)
  simpa using hscale

/-- A common-right-interleaver witness is unchanged by removing a negation
from the right endpoint, since `Prec` only depends on the roots. -/
theorem pairHasCommonInterleaver_of_neg_right {f g : ℝ[X]}
    (h : PositiveSplitRootCountPair f (-g)) :
    ∃ k : ℝ[X], Prec f k ∧ Prec g k := by
  obtain ⟨k, hfk, hgk⟩ := h.pairHasCommonInterleaver
  refine ⟨k, hfk, ?_⟩
  have hscale : Prec (C (-1 : ℝ) * (-g)) k :=
    prec_C_mul_left hgk (by norm_num)
  simpa using hscale

end PositiveSplitRootCountPair

/-- All-combinations real-rootedness descends through translation by
`X + C r`. -/
theorem allComboRealRooted_of_comp_X_add_C {f g : ℝ[X]} (r : ℝ)
    (hall : AllComboRealRooted (f.comp (X + C r)) (g.comp (X + C r))) :
    AllComboRealRooted f g := by
  intro α β
  have htranslate :
      (C α * f + C β * g).comp (X + C r) =
        C α * f.comp (X + C r) + C β * g.comp (X + C r) := by
    simp
  exact splits_of_comp_X_add_C_splits r
    (by simpa [htranslate] using hall α β)

namespace Compatible

/-- Compatibility descends through translation by `X + C r`. -/
lemma of_comp_X_add_C {f g : ℝ[X]} (r : ℝ)
    (hcompat : Compatible (f.comp (X + C r)) (g.comp (X + C r))) :
    Compatible f g := by
  intro α β hα hβ
  have htranslate :
      C α * f.comp (X + C r) + C β * g.comp (X + C r) =
        (C α * f + C β * g).comp (X + C r) := by
    simp
  rcases hcompat α β hα hβ with hzero | hrr
  · left
    by_contra hne
    have hcomp_ne : (C α * f + C β * g).comp (X + C r) ≠ 0 :=
      (Polynomial.comp_X_add_C_ne_zero_iff).2 hne
    exact hcomp_ne (htranslate ▸ hzero)
  · right
    refine ⟨?_, ?_⟩
    · intro hzero
      have hcomp_zero : (C α * f + C β * g).comp (X + C r) = 0 := by
        simpa using congrArg (fun p : ℝ[X] => p.comp (X + C r)) hzero
      exact hrr.1 (htranslate.symm ▸ hcomp_zero)
    · exact splits_of_comp_X_add_C_splits r (htranslate ▸ hrr.2)

/-- A one-parameter positive right pencil, together with split endpoints,
gives full nonnegative compatibility by scaling the left coefficient to `1`. -/
lemma of_splits_of_pos_right_family {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits)
    (hfamily : ∀ μ : ℝ, 0 < μ → (f + C μ * g).Splits) :
    Compatible f g := by
  intro α β hα hβ
  by_cases hsum : C α * f + C β * g = 0
  · exact Or.inl hsum
  · right
    refine ⟨hsum, ?_⟩
    by_cases hα0 : α = 0
    · subst hα0
      simpa using (Polynomial.Splits.C (R := ℝ) β).mul hg
    · have hα_pos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
      by_cases hβ0 : β = 0
      · subst hβ0
        simpa using (Polynomial.Splits.C (R := ℝ) α).mul hf
      · have hβ_pos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
        have hμ_pos : 0 < β / α := div_pos hβ_pos hα_pos
        have hright : (f + C (β / α) * g).Splits :=
          hfamily (β / α) hμ_pos
        have hscale :
            C α * (f + C (β / α) * g) = C α * f + C β * g := by
          rw [mul_add]
          congr 1
          have hαβ : α * (β / α) = β := by
            field_simp [hα0]
          calc
            C α * (C (β / α) * g) = C (α * (β / α)) * g := by
              simp [mul_assoc]
            _ = C β * g := by rw [hαβ]
        rw [← hscale]
        exact (Polynomial.Splits.C (R := ℝ) α).mul hright

end Compatible

/-- Guardrail for the factor-return route: multiplying the higher-degree
member of a simple quadratic/linear interlacing pair by `X` need not preserve
all-combinations real-rootedness.  Thus the Liu factor-return proof cannot use
a generic all-combinations strengthening of the translated `X * q` target. -/
theorem not_allComboRealRooted_X_mul_quadratic_linear_example :
    ¬ AllComboRealRooted
      (X * ((X + C (1 : ℝ)) * (X + C (3 : ℝ)))) (-(X + C (2 : ℝ))) := by
  intro hall
  let p : ℝ[X] :=
    C (1 : ℝ) * (X * ((X + C (1 : ℝ)) * (X + C (3 : ℝ)))) +
      C (-1 : ℝ) * (-(X + C (2 : ℝ)))
  have hp_splits : p.Splits := by
    simpa [p] using hall 1 (-1)
  have hp_deg : p.natDegree ≤ 3 := by
    dsimp [p]
    compute_degree!
  have hdisc_nonneg : 0 ≤ cubicDiscr p :=
    cubicDiscr_nonneg_of_splits_natDegree_le_three hp_deg hp_splits
  have hdisc_neg : cubicDiscr p < 0 := by
    norm_num [p, cubicDiscr, coeff_add, coeff_C_mul, coeff_neg, coeff_mul,
      Finset.antidiagonal, coeff_X, coeff_C, coeff_one]
  linarith

namespace LeftRootCountBranch

/-- A left Liu branch gives a common-right-interleaver witness for the actual
deletion pair `(deleteRootFactor f r, g)`, after stripping the sign
normalization used to make leading coefficients positive. -/
theorem deletePairHasCommonInterleaver {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k := by
  rcases h.positiveSplitDeletionCount hsgn hf_splits hg_splits with hpos | hpos
  · exact hpos.pairHasCommonInterleaver_of_neg_right
  · exact hpos.pairHasCommonInterleaver_of_neg_left

/-- After translating by the restored largest root, the sign-normalized left
deletion pair has nonnegative coefficients. -/
theorem positiveDeletionPair_comp_X_add_C_hasNonnegCoeffs
    {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    (HasNonnegCoeffs ((deleteRootFactor f r).comp (X + C r)) ∧
        HasNonnegCoeffs ((-g).comp (X + C r))) ∨
      (HasNonnegCoeffs ((-(deleteRootFactor f r)).comp (X + C r)) ∧
        HasNonnegCoeffs (g.comp (X + C r))) := by
  have hroots :=
    h.deletionPair_roots_le_left_largest hsgn.left_ne_zero
  rcases (h.delete_oppositeLeadingSigns hsgn).pos_neg_or_neg_pos with hpos | hpos
  · left
    refine ⟨?_, ?_⟩
    · exact hasNonnegCoeffs_comp_X_add_C_of_roots_le
        hpos.1 (h.delete_splits hf_splits) hroots.1
    · refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.2 hg_splits.neg ?_
      intro t ht
      exact hroots.2 t (by simpa [Polynomial.roots_neg] using ht)
  · right
    refine ⟨?_, ?_⟩
    · refine hasNonnegCoeffs_comp_X_add_C_of_roots_le
        hpos.1 (h.delete_splits hf_splits).neg ?_
      intro t ht
      exact hroots.1 t (by simpa [Polynomial.roots_neg] using ht)
    · exact hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.2 hg_splits hroots.2

/-- A supplied common-right-interleaver witness for the actual left deletion
pair gives compatibility of the sign-normalized deletion pair. -/
theorem positiveDeletionPair_compatible_of_commonInterleaver
    {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) :
    Compatible (deleteRootFactor f r) (-g) ∨
      Compatible (-(deleteRootFactor f r)) g := by
  rcases hcommon with ⟨k, hqk, hgk⟩
  rcases (h.delete_oppositeLeadingSigns hsgn).pos_neg_or_neg_pos with hpos | hpos
  · left
    have hneg_gk : Prec (-g) k := by
      have hscale : Prec (C (-1 : ℝ) * g) k :=
        prec_C_mul_left hgk (by norm_num)
      simpa using hscale
    exact Compatible.of_commonInterleaver hqk hneg_gk hpos.1 hpos.2
  · right
    have hneg_qk : Prec (-(deleteRootFactor f r)) k := by
      have hscale : Prec (C (-1 : ℝ) * deleteRootFactor f r) k :=
        prec_C_mul_left hqk (by norm_num)
      simpa using hscale
    exact Compatible.of_commonInterleaver hneg_qk hgk hpos.1 hpos.2

/-- To prove all-combinations real-rootedness for a left branch, it is enough
to prove the translated target after restoring the deleted factor as `X`. -/
theorem allComboRealRooted_of_translated_restore
    {f g : ℝ[X]} {r s : ℝ} (h : LeftRootCountBranch f g r s)
    (hall : AllComboRealRooted
      (X * (deleteRootFactor f r).comp (X + C r)) (g.comp (X + C r))) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_comp_X_add_C r <| by
    simpa [h.left_comp_X_add_C_eq_X_mul_deleteRootFactor_comp] using hall

/-- Sign-normalized translated all-combinations data are enough to restore the
original left branch. -/
theorem allComboRealRooted_of_positiveTranslatedRestore
    {f g : ℝ[X]} {r s : ℝ} (h : LeftRootCountBranch f g r s)
    (hall : AllComboRealRooted
        (X * (deleteRootFactor f r).comp (X + C r)) ((-g).comp (X + C r)) ∨
      AllComboRealRooted
        (X * (-(deleteRootFactor f r)).comp (X + C r)) (g.comp (X + C r))) :
    AllComboRealRooted f g := by
  apply h.allComboRealRooted_of_translated_restore
  rcases hall with hall | hall
  · simpa using hall.neg_right
  · simpa [mul_neg] using hall.neg_left

/-- To prove compatibility for a left branch, it is enough to prove the
translated target after restoring the deleted factor as `X`. -/
theorem compatible_of_translated_restore
    {f g : ℝ[X]} {r s : ℝ} (h : LeftRootCountBranch f g r s)
    (hcompat : Compatible
      (X * (deleteRootFactor f r).comp (X + C r)) (g.comp (X + C r))) :
    Compatible f g :=
  Compatible.of_comp_X_add_C r <| by
    simpa [h.left_comp_X_add_C_eq_X_mul_deleteRootFactor_comp] using hcompat

end LeftRootCountBranch

namespace RightRootCountBranch

/-- A right Liu branch gives a common-right-interleaver witness for the actual
deletion pair `(f, deleteRootFactor g s)`, after stripping the sign
normalization used to make leading coefficients positive. -/
theorem deletePairHasCommonInterleaver {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k := by
  rcases h.positiveSplitDeletionCount hsgn hf_splits hg_splits with hpos | hpos
  · exact hpos.pairHasCommonInterleaver_of_neg_right
  · exact hpos.pairHasCommonInterleaver_of_neg_left

/-- After translating by the restored largest root, the sign-normalized right
deletion pair has nonnegative coefficients. -/
theorem positiveDeletionPair_comp_X_add_C_hasNonnegCoeffs
    {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hf_splits : f.Splits) (hg_splits : g.Splits) :
    (HasNonnegCoeffs (f.comp (X + C s)) ∧
        HasNonnegCoeffs ((-(deleteRootFactor g s)).comp (X + C s))) ∨
      (HasNonnegCoeffs ((-f).comp (X + C s)) ∧
        HasNonnegCoeffs ((deleteRootFactor g s).comp (X + C s))) := by
  have hroots :=
    h.deletionPair_roots_le_right_largest hsgn.right_ne_zero
  rcases (h.delete_oppositeLeadingSigns hsgn).pos_neg_or_neg_pos with hpos | hpos
  · left
    refine ⟨?_, ?_⟩
    · exact hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.1 hf_splits hroots.1
    · refine hasNonnegCoeffs_comp_X_add_C_of_roots_le
        hpos.2 (h.delete_splits hg_splits).neg ?_
      intro t ht
      exact hroots.2 t (by simpa [Polynomial.roots_neg] using ht)
  · right
    refine ⟨?_, ?_⟩
    · refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.1 hf_splits.neg ?_
      intro t ht
      exact hroots.1 t (by simpa [Polynomial.roots_neg] using ht)
    · exact hasNonnegCoeffs_comp_X_add_C_of_roots_le
        hpos.2 (h.delete_splits hg_splits) hroots.2

/-- A supplied common-right-interleaver witness for the actual right deletion
pair gives compatibility of the sign-normalized deletion pair. -/
theorem positiveDeletionPair_compatible_of_commonInterleaver
    {f g : ℝ[X]} {r s : ℝ}
    (h : RightRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) :
    Compatible f (-(deleteRootFactor g s)) ∨
      Compatible (-f) (deleteRootFactor g s) := by
  rcases hcommon with ⟨k, hfk, hqk⟩
  rcases (h.delete_oppositeLeadingSigns hsgn).pos_neg_or_neg_pos with hpos | hpos
  · left
    have hneg_qk : Prec (-(deleteRootFactor g s)) k := by
      have hscale : Prec (C (-1 : ℝ) * deleteRootFactor g s) k :=
        prec_C_mul_left hqk (by norm_num)
      simpa using hscale
    exact Compatible.of_commonInterleaver hfk hneg_qk hpos.1 hpos.2
  · right
    have hneg_fk : Prec (-f) k := by
      have hscale : Prec (C (-1 : ℝ) * f) k :=
        prec_C_mul_left hfk (by norm_num)
      simpa using hscale
    exact Compatible.of_commonInterleaver hneg_fk hqk hpos.1 hpos.2

/-- To prove all-combinations real-rootedness for a right branch, it is enough
to prove the translated target after restoring the deleted factor as `X`. -/
theorem allComboRealRooted_of_translated_restore
    {f g : ℝ[X]} {r s : ℝ} (h : RightRootCountBranch f g r s)
    (hall : AllComboRealRooted (f.comp (X + C s))
      (X * (deleteRootFactor g s).comp (X + C s))) :
    AllComboRealRooted f g :=
  allComboRealRooted_of_comp_X_add_C s <| by
    simpa [h.right_comp_X_add_C_eq_X_mul_deleteRootFactor_comp] using hall

/-- Sign-normalized translated all-combinations data are enough to restore the
original right branch. -/
theorem allComboRealRooted_of_positiveTranslatedRestore
    {f g : ℝ[X]} {r s : ℝ} (h : RightRootCountBranch f g r s)
    (hall : AllComboRealRooted (f.comp (X + C s))
        (X * (-(deleteRootFactor g s)).comp (X + C s)) ∨
      AllComboRealRooted ((-f).comp (X + C s))
        (X * (deleteRootFactor g s).comp (X + C s))) :
    AllComboRealRooted f g := by
  apply h.allComboRealRooted_of_translated_restore
  rcases hall with hall | hall
  · simpa [mul_neg] using hall.neg_right
  · simpa using hall.neg_left

/-- To prove compatibility for a right branch, it is enough to prove the
translated target after restoring the deleted factor as `X`. -/
theorem compatible_of_translated_restore
    {f g : ℝ[X]} {r s : ℝ} (h : RightRootCountBranch f g r s)
    (hcompat : Compatible (f.comp (X + C s))
      (X * (deleteRootFactor g s).comp (X + C s))) :
    Compatible f g :=
  Compatible.of_comp_X_add_C s <| by
    simpa [h.right_comp_X_add_C_eq_X_mul_deleteRootFactor_comp] using hcompat

end RightRootCountBranch

/-- Liu branch data together with a common-right interleaver for the actual
deletion pair selected by that branch.  This keeps the largest-root/order
certificate that is lost in the fully sign-normalized compatibility package. -/
def theorem21DeletionPairCommonInterleaverBranches (f g : ℝ[X]) : Prop :=
  ∃ r s,
    (LeftRootCountBranch f g r s ∧
        ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) ∨
      (RightRootCountBranch f g r s ∧
        ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)

/-- Liu root-count branches produce common-right-interleaver witnesses for the
actual deletion pair in the selected branch. -/
theorem theorem21DeletionPairCommonInterleaverBranches_of_theorem21RootCountBranches
    {f g : ℝ[X]} (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (h : theorem21RootCountBranches f g) :
    theorem21DeletionPairCommonInterleaverBranches f g := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact ⟨r, s, Or.inl
      ⟨hleft, hleft.deletePairHasCommonInterleaver
        hsgn hf_splits hg_splits⟩⟩
  · exact ⟨r, s, Or.inr
      ⟨hright, hright.deletePairHasCommonInterleaver
        hsgn hf_splits hg_splits⟩⟩

/-- The branch-retaining common-interleaver package forgets back to Liu's
root-count branches. -/
theorem theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
    {f g : ℝ[X]} (h : theorem21DeletionPairCommonInterleaverBranches f g) :
    theorem21RootCountBranches f g := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact ⟨r, s, Or.inl hleft.1⟩
  · exact ⟨r, s, Or.inr hright.1⟩

/-- With splitting and opposite-leading-sign hypotheses, Liu's root-count
branches are equivalent to the branch-retaining common-interleaver package. -/
theorem theorem21DeletionPairCommonInterleaverBranches_iff_rootCountBranches
    {f g : ℝ[X]} (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hsgn : OppositeLeadingSigns f g) :
    theorem21DeletionPairCommonInterleaverBranches f g ↔
      theorem21RootCountBranches f g :=
  ⟨theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches,
    theorem21DeletionPairCommonInterleaverBranches_of_theorem21RootCountBranches
      hf_splits hg_splits hsgn⟩

/-- The remaining factor-return principle for the reverse direction of Liu
Theorem 2.1.  It says that once the selected deletion pair has a common
right interleaver, the deleted largest linear factor can be put back to recover
compatibility of the original opposite-leading-sign pair. -/
def theorem21DeletionPairCommonInterleaverFactorReturnStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      (LeftRootCountBranch f g r s →
        (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
          Compatible f g) ∧
      (RightRootCountBranch f g r s →
        (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
          Compatible f g)

/-- Stronger all-real-combination version of the factor-return principle. -/
def theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement :
    Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      (LeftRootCountBranch f g r s →
        (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
          AllComboRealRooted f g) ∧
      (RightRootCountBranch f g r s →
        (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
          AllComboRealRooted f g)

/-- The all-real-combination factor-return target implies the existing
compatibility factor-return target. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_allCombo
    (hreturn :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement := by
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon
    exact Compatible.of_allComboRealRooted
      ((hreturn hf hg hsgn).1 hleft hcommon)
  · intro hright hcommon
    exact Compatible.of_allComboRealRooted
      ((hreturn hf hg hsgn).2 hright hcommon)

/-- Swap the common-right-interleaver witness in a right deletion pair. -/
theorem rightDeletionPairCommonInterleaver_symm {f g : ℝ[X]} {s : ℝ}
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) :
    ∃ k : ℝ[X], Prec (deleteRootFactor g s) k ∧ Prec f k := by
  rcases hcommon with ⟨k, hfk, hgk⟩
  exact ⟨k, hgk, hfk⟩

/-- Same-degree left-branch all-combinations factor-return target. -/
def theorem21LeftFactorReturnSameDegreeAllComboStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        f.natDegree = g.natDegree →
          (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
            AllComboRealRooted f g

/-- Succ-degree left-branch all-combinations factor-return target. -/
def theorem21LeftFactorReturnSuccDegreeAllComboStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        f.natDegree = g.natDegree + 1 →
          (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
            AllComboRealRooted f g

/-- Two-degree-gap left-branch all-combinations factor-return target. -/
def theorem21LeftFactorReturnTwoDegreeAllComboStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        f.natDegree = g.natDegree + 2 →
          (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
            AllComboRealRooted f g

/-- The three left-branch all-combinations factor-return cases.  The right
branch follows by symmetry. -/
def theorem21LeftFactorReturnAllComboDegreeCasesStatement : Prop :=
  theorem21LeftFactorReturnSameDegreeAllComboStatement ∧
    theorem21LeftFactorReturnSuccDegreeAllComboStatement ∧
      theorem21LeftFactorReturnTwoDegreeAllComboStatement

/-- Same-degree right-branch all-combinations factor-return target. -/
def theorem21RightFactorReturnSameDegreeAllComboStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      RightRootCountBranch f g r s →
        g.natDegree = f.natDegree →
          (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
            AllComboRealRooted f g

/-- Succ-degree right-branch all-combinations factor-return target. -/
def theorem21RightFactorReturnSuccDegreeAllComboStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      RightRootCountBranch f g r s →
        g.natDegree = f.natDegree + 1 →
          (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
            AllComboRealRooted f g

/-- Two-degree-gap right-branch all-combinations factor-return target. -/
def theorem21RightFactorReturnTwoDegreeAllComboStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      RightRootCountBranch f g r s →
        g.natDegree = f.natDegree + 2 →
          (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
            AllComboRealRooted f g

/-- The right same-degree all-combinations factor-return case follows from
the left same-degree case by swapping the two polynomials. -/
theorem theorem21RightFactorReturnSameDegreeAllCombo_of_leftSameDegree
    (hleft : theorem21LeftFactorReturnSameDegreeAllComboStatement) :
    theorem21RightFactorReturnSameDegreeAllComboStatement := by
  exact fun {f} {g} {r} {s} hf hg hsgn hright hdeg hcommon =>
    allComboRealRooted_comm <|
      hleft (f := g) (g := f) (r := s) (s := r)
        hg hf hsgn.symm hright.toLeftBranch_symm hdeg
        (rightDeletionPairCommonInterleaver_symm hcommon)

/-- The right successor-degree all-combinations factor-return case follows
from the left successor-degree case by swapping the two polynomials. -/
theorem theorem21RightFactorReturnSuccDegreeAllCombo_of_leftSuccDegree
    (hleft : theorem21LeftFactorReturnSuccDegreeAllComboStatement) :
    theorem21RightFactorReturnSuccDegreeAllComboStatement := by
  exact fun {f} {g} {r} {s} hf hg hsgn hright hdeg hcommon =>
    allComboRealRooted_comm <|
      hleft (f := g) (g := f) (r := s) (s := r)
        hg hf hsgn.symm hright.toLeftBranch_symm hdeg
        (rightDeletionPairCommonInterleaver_symm hcommon)

/-- The right two-degree-gap all-combinations factor-return case follows
from the left two-degree-gap case by swapping the two polynomials. -/
theorem theorem21RightFactorReturnTwoDegreeAllCombo_of_leftTwoDegree
    (hleft : theorem21LeftFactorReturnTwoDegreeAllComboStatement) :
    theorem21RightFactorReturnTwoDegreeAllComboStatement := by
  exact fun {f} {g} {r} {s} hf hg hsgn hright hdeg hcommon =>
    allComboRealRooted_comm <|
      hleft (f := g) (g := f) (r := s) (s := r)
        hg hf hsgn.symm hright.toLeftBranch_symm hdeg
        (rightDeletionPairCommonInterleaver_symm hcommon)

/-- Degree-case split needed to prove the all-combinations factor-return
principle. -/
def theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement :
    Prop :=
  theorem21LeftFactorReturnSameDegreeAllComboStatement ∧
    theorem21LeftFactorReturnSuccDegreeAllComboStatement ∧
      theorem21LeftFactorReturnTwoDegreeAllComboStatement ∧
        theorem21RightFactorReturnSameDegreeAllComboStatement ∧
          theorem21RightFactorReturnSuccDegreeAllComboStatement ∧
            theorem21RightFactorReturnTwoDegreeAllComboStatement

/-- Left all-combinations factor-return degree cases supply all six left/right
cases by symmetry. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCases_of_leftCases
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement := by
  rcases hcases with ⟨hleft_same, hleft_succ, hleft_two⟩
  exact
    ⟨hleft_same, hleft_succ, hleft_two,
      theorem21RightFactorReturnSameDegreeAllCombo_of_leftSameDegree
        hleft_same,
      theorem21RightFactorReturnSuccDegreeAllCombo_of_leftSuccDegree
        hleft_succ,
      theorem21RightFactorReturnTwoDegreeAllCombo_of_leftTwoDegree
        hleft_two⟩

/-- The explicit all-combinations factor-return principle follows from its
six restored-degree cases. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnAllCombo_of_degreeCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement := by
  rcases hcases with
    ⟨hleft_same, hleft_succ, hleft_two, hright_same, hright_succ,
      hright_two⟩
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon
    rcases hleft.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.left_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hleft_same hf hg hsgn hleft hdeg hcommon
    · exact hleft_succ hf hg hsgn hleft hdeg hcommon
    · exact hleft_two hf hg hsgn hleft hdeg hcommon
  · intro hright hcommon
    rcases hright.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.right_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hright_same hf hg hsgn hright hdeg hcommon
    · exact hright_succ hf hg hsgn hright hdeg hcommon
    · exact hright_two hf hg hsgn hright hdeg hcommon

/-- It is enough to prove the left-branch all-combinations factor-return
cases; the right branch is symmetric. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnAllCombo_of_leftCases
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnAllComboStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturnAllCombo_of_degreeCases
    (theorem21DeletionPairCommonInterleaverFactorReturnAllComboDegreeCases_of_leftCases
      hcases)

/-- Left all-combinations factor-return degree cases imply the compatibility
factor-return principle used by the reverse direction. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_leftAllComboCases
    (hcases : theorem21LeftFactorReturnAllComboDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_allCombo
    (theorem21DeletionPairCommonInterleaverFactorReturnAllCombo_of_leftCases
      hcases)

/-- Same-degree left-branch factor-return target. -/
def theorem21LeftFactorReturnSameDegreeStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        f.natDegree = g.natDegree →
          (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
            Compatible f g

/-- Succ-degree left-branch factor-return target. -/
def theorem21LeftFactorReturnSuccDegreeStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        f.natDegree = g.natDegree + 1 →
          (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
            Compatible f g

/-- Two-degree-gap left-branch factor-return target. -/
def theorem21LeftFactorReturnTwoDegreeStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        f.natDegree = g.natDegree + 2 →
          (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
            Compatible f g

/-- Translated two-degree left-branch factor-return target.  This keeps the
original sign of `g` and asks only for compatibility, avoiding the false
all-combinations strengthening. -/
def theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        f.natDegree = g.natDegree + 2 →
          (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
            Compatible
              (X * (deleteRootFactor f r).comp (X + C r))
              (g.comp (X + C r))

/-- A left endpoint cannot be in `Prec` with a right endpoint of one lower
degree.  This guards against a tempting but degree-impossible #64 route. -/
theorem not_prec_of_natDegree_eq_succ_left {f g : ℝ[X]}
    (hdeg : f.natDegree = g.natDegree + 1) :
    ¬ Prec f g := by
  intro hprec
  have hbounds := natDegree_bounds_of_prec hprec
  lia

/-- In the two-degree Liu left branch, orienting the translated deletion pair
as `deleteRootFactor f r ≺ g` is degree-impossible. -/
theorem LeftRootCountBranch.not_translatedDeletionPrec_of_twoDegree
    {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hdeg : f.natDegree = g.natDegree + 2) :
    ¬ (Prec ((deleteRootFactor f r).comp (X + C r)) ((-g).comp (X + C r)) ∨
        Prec ((-(deleteRootFactor f r)).comp (X + C r)) (g.comp (X + C r))) := by
  have hdelete_deg :
      (deleteRootFactor f r).natDegree = g.natDegree + 1 :=
    h.delete_natDegree_eq_succ_of_twoDegree hsgn.left_ne_zero hdeg
  intro horient
  rcases horient with hprec | hprec
  · have hdeg' :
        ((deleteRootFactor f r).comp (X + C r)).natDegree =
          ((-g).comp (X + C r)).natDegree + 1 := by
      simpa [Polynomial.natDegree_comp, Polynomial.natDegree_neg] using hdelete_deg
    exact (not_prec_of_natDegree_eq_succ_left hdeg') hprec
  · have hdeg' :
        ((-(deleteRootFactor f r)).comp (X + C r)).natDegree =
          (g.comp (X + C r)).natDegree + 1 := by
      simpa [Polynomial.natDegree_comp, Polynomial.natDegree_neg] using hdelete_deg
    exact (not_prec_of_natDegree_eq_succ_left hdeg') hprec

/-- The stronger boundary-`Prec` route is also degree-impossible in the
two-degree Liu left branch: the restored endpoint has degree two more than
`g`. -/
theorem LeftRootCountBranch.not_translatedBoundaryPrec_of_twoDegree
    {f g : ℝ[X]} {r s : ℝ}
    (h : LeftRootCountBranch f g r s) (hsgn : OppositeLeadingSigns f g)
    (hdeg : f.natDegree = g.natDegree + 2) :
    ¬ Prec (g.comp (X + C r))
        (X * (deleteRootFactor f r).comp (X + C r)) := by
  have hdelete_ne : deleteRootFactor f r ≠ 0 :=
    h.delete_ne_zero hsgn.left_ne_zero
  have hdelete_shift_ne :
      (deleteRootFactor f r).comp (X + C r) ≠ 0 :=
    (Polynomial.comp_X_add_C_ne_zero_iff).2 hdelete_ne
  have hdelete_deg :
      (deleteRootFactor f r).natDegree = g.natDegree + 1 :=
    h.delete_natDegree_eq_succ_of_twoDegree hsgn.left_ne_zero hdeg
  have hshift_deg :
      ((deleteRootFactor f r).comp (X + C r)).natDegree =
        (g.comp (X + C r)).natDegree + 1 := by
    simpa [Polynomial.natDegree_comp] using hdelete_deg
  have hrestored_deg :
      (X * (deleteRootFactor f r).comp (X + C r)).natDegree =
        (g.comp (X + C r)).natDegree + 2 := by
    rw [natDegree_mul X_ne_zero hdelete_shift_ne, natDegree_X, hshift_deg]
    lia
  intro hprec
  have hbounds := natDegree_bounds_of_prec hprec
  rw [hrestored_deg] at hbounds
  lia

/-- One-parameter positive right-pencil version of the translated two-degree
target.  This is the remaining genuinely mathematical leaf after endpoint
splitting and coefficient scaling have been separated out. -/
def theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      LeftRootCountBranch f g r s →
        f.natDegree = g.natDegree + 2 →
          (∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k) →
            ∀ μ : ℝ, 0 < μ →
              (X * (deleteRootFactor f r).comp (X + C r) +
                  C μ * g.comp (X + C r)).Splits

/-- The sign-normalized positive-split subtraction-family leaf gives the
translated one-parameter target for the two-degree Liu left branch. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_xSub
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement := by
  intro f g r s hf hg hsgn hleft hdeg _hcommon μ hμ
  have hdelete_deg :
      (deleteRootFactor f r).natDegree = g.natDegree + 1 :=
    hleft.delete_natDegree_eq_succ_of_twoDegree hsgn.left_ne_zero hdeg
  have hroots :=
    hleft.deletionPair_roots_le_left_largest hsgn.left_ne_zero
  rcases (hleft.delete_oppositeLeadingSigns hsgn).pos_neg_or_neg_pos with hpos | hpos
  · have hpair :
        PositiveSplitRootCountPair (deleteRootFactor f r) (-g) :=
      ⟨hpos.1, hpos.2, hleft.delete_splits hf, hg.neg, hleft.count.neg_right⟩
    have hqnn :
        HasNonnegCoeffs ((deleteRootFactor f r).comp (X + C r)) :=
      hasNonnegCoeffs_comp_X_add_C_of_roots_le
        hpos.1 (hleft.delete_splits hf) hroots.1
    have hGnn : HasNonnegCoeffs ((-g).comp (X + C r)) := by
      refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.2 hg.neg ?_
      intro t ht
      exact hroots.2 t (by simpa [Polynomial.roots_neg] using ht)
    have hdeg_pos :
        (deleteRootFactor f r).natDegree = (-g).natDegree + 1 := by
      simpa [Polynomial.natDegree_neg] using hdelete_deg
    have hsplit :=
      hsub r hpair hqnn hGnn hdeg_pos μ hμ
    simpa [sub_eq_add_neg, mul_neg] using hsplit
  · have hpair :
        PositiveSplitRootCountPair (-(deleteRootFactor f r)) g :=
      ⟨hpos.1, hpos.2, (hleft.delete_splits hf).neg, hg, hleft.count.neg_left⟩
    have hQnn :
        HasNonnegCoeffs ((-(deleteRootFactor f r)).comp (X + C r)) := by
      refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.1 (hleft.delete_splits hf).neg ?_
      intro t ht
      exact hroots.1 t (by simpa [Polynomial.roots_neg] using ht)
    have hgnn : HasNonnegCoeffs (g.comp (X + C r)) :=
      hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.2 hg hroots.2
    have hdeg_pos :
        (-(deleteRootFactor f r)).natDegree = g.natDegree + 1 := by
      simpa [Polynomial.natDegree_neg] using hdelete_deg
    have hsplit :=
      hsub r hpair hQnn hgnn hdeg_pos μ hμ
    simpa [sub_eq_add_neg, mul_neg, neg_add_rev, add_comm] using hsplit.neg

/-- Constant-right-endpoint base case for the translated two-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_right_natDegree_zero
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (_hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 0) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hdelete_deg :
      (deleteRootFactor f r).natDegree = g.natDegree + 1 :=
    hleft.delete_natDegree_eq_succ_of_twoDegree hsgn.left_ne_zero hdeg
  have hroots :=
    hleft.deletionPair_roots_le_left_largest hsgn.left_ne_zero
  rcases (hleft.delete_oppositeLeadingSigns hsgn).pos_neg_or_neg_pos with hpos | hpos
  · have hpair :
        PositiveSplitRootCountPair (deleteRootFactor f r) (-g) :=
      ⟨hpos.1, hpos.2, hleft.delete_splits hf, hg.neg, hleft.count.neg_right⟩
    have hqnn :
        HasNonnegCoeffs ((deleteRootFactor f r).comp (X + C r)) :=
      hasNonnegCoeffs_comp_X_add_C_of_roots_le
        hpos.1 (hleft.delete_splits hf) hroots.1
    have hGnn : HasNonnegCoeffs ((-g).comp (X + C r)) := by
      refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.2 hg.neg ?_
      intro t ht
      exact hroots.2 t (by simpa [Polynomial.roots_neg] using ht)
    have hdeg_pos :
        (deleteRootFactor f r).natDegree = (-g).natDegree + 1 := by
      simpa [Polynomial.natDegree_neg] using hdelete_deg
    have hGdeg : (-g).natDegree = 0 := by
      simpa [Polynomial.natDegree_neg] using hgdeg
    have hsplit :=
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
        hpair hqnn hGnn hdeg_pos hGdeg μ hμ
    simpa [sub_eq_add_neg, mul_neg] using hsplit
  · have hpair :
        PositiveSplitRootCountPair (-(deleteRootFactor f r)) g :=
      ⟨hpos.1, hpos.2, (hleft.delete_splits hf).neg, hg, hleft.count.neg_left⟩
    have hQnn :
        HasNonnegCoeffs ((-(deleteRootFactor f r)).comp (X + C r)) := by
      refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.1
        (hleft.delete_splits hf).neg ?_
      intro t ht
      exact hroots.1 t (by simpa [Polynomial.roots_neg] using ht)
    have hgnn : HasNonnegCoeffs (g.comp (X + C r)) :=
      hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.2 hg hroots.2
    have hdeg_pos :
        (-(deleteRootFactor f r)).natDegree = g.natDegree + 1 := by
      simpa [Polynomial.natDegree_neg] using hdelete_deg
    have hsplit :=
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
        hpair hQnn hgnn hdeg_pos hgdeg μ hμ
    simpa [sub_eq_add_neg, mul_neg, neg_add_rev, add_comm] using hsplit.neg

/-- Degree-one-right-endpoint case for the translated two-degree Liu
right-family target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_right_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (_hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * (deleteRootFactor f r).comp (X + C r) +
          C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hdelete_deg :
      (deleteRootFactor f r).natDegree = g.natDegree + 1 :=
    hleft.delete_natDegree_eq_succ_of_twoDegree hsgn.left_ne_zero hdeg
  have hroots :=
    hleft.deletionPair_roots_le_left_largest hsgn.left_ne_zero
  rcases (hleft.delete_oppositeLeadingSigns hsgn).pos_neg_or_neg_pos with hpos | hpos
  · have hpair :
        PositiveSplitRootCountPair (deleteRootFactor f r) (-g) :=
      ⟨hpos.1, hpos.2, hleft.delete_splits hf, hg.neg, hleft.count.neg_right⟩
    have hqnn :
        HasNonnegCoeffs ((deleteRootFactor f r).comp (X + C r)) :=
      hasNonnegCoeffs_comp_X_add_C_of_roots_le
        hpos.1 (hleft.delete_splits hf) hroots.1
    have hGnn : HasNonnegCoeffs ((-g).comp (X + C r)) := by
      refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.2 hg.neg ?_
      intro t ht
      exact hroots.2 t (by simpa [Polynomial.roots_neg] using ht)
    have hdeg_pos :
        (deleteRootFactor f r).natDegree = (-g).natDegree + 1 := by
      simpa [Polynomial.natDegree_neg] using hdelete_deg
    have hGdeg : (-g).natDegree = 1 := by
      simpa [Polynomial.natDegree_neg] using hgdeg
    have hsplit :=
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one
        hpair hqnn hGnn hdeg_pos hGdeg μ hμ
    simpa [sub_eq_add_neg, mul_neg] using hsplit
  · have hpair :
        PositiveSplitRootCountPair (-(deleteRootFactor f r)) g :=
      ⟨hpos.1, hpos.2, (hleft.delete_splits hf).neg, hg, hleft.count.neg_left⟩
    have hQnn :
        HasNonnegCoeffs ((-(deleteRootFactor f r)).comp (X + C r)) := by
      refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.1
        (hleft.delete_splits hf).neg ?_
      intro t ht
      exact hroots.1 t (by simpa [Polynomial.roots_neg] using ht)
    have hgnn : HasNonnegCoeffs (g.comp (X + C r)) :=
      hasNonnegCoeffs_comp_X_add_C_of_roots_le hpos.2 hg hroots.2
    have hdeg_pos :
        (-(deleteRootFactor f r)).natDegree = g.natDegree + 1 := by
      simpa [Polynomial.natDegree_neg] using hdelete_deg
    have hsplit :=
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one
        hpair hQnn hgnn hdeg_pos hgdeg μ hμ
    simpa [sub_eq_add_neg, mul_neg, neg_add_rev, add_comm] using hsplit.neg

/-- The positive right-pencil translated leaf gives the translated
compatibility leaf by scaling an arbitrary nonnegative linear combination. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_rightFamily
    (hright :
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamilyStatement) :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement := by
  intro f g r s hf hg hsgn hleft hdeg hcommon
  have hdelete_rr :
      deleteRootFactor f r ≠ 0 ∧ (deleteRootFactor f r).Splits :=
    hleft.delete_ne_zero_and_splits hsgn.left_ne_zero hf
  have hdelete_shift_rr :
      (deleteRootFactor f r).comp (X + C r) ≠ 0 ∧
        ((deleteRootFactor f r).comp (X + C r)).Splits :=
    isRealRooted_comp_X_add_C hdelete_rr.1 hdelete_rr.2 r
  have hrestored_split :
      (X * (deleteRootFactor f r).comp (X + C r)).Splits :=
    (isRealRooted_X_mul hdelete_shift_rr.1 hdelete_shift_rr.2).2
  have hg_shift_split : (g.comp (X + C r)).Splits :=
    (isRealRooted_comp_X_add_C hsgn.right_ne_zero hg r).2
  exact Compatible.of_splits_of_pos_right_family hrestored_split hg_shift_split
    (fun μ hμ => hright hf hg hsgn hleft hdeg hcommon μ hμ)

/-- Constant-right-endpoint base case for the translated two-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_right_natDegree_zero
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 0) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) := by
  have hdelete_rr :
      deleteRootFactor f r ≠ 0 ∧ (deleteRootFactor f r).Splits :=
    hleft.delete_ne_zero_and_splits hsgn.left_ne_zero hf
  have hdelete_shift_rr :
      (deleteRootFactor f r).comp (X + C r) ≠ 0 ∧
        ((deleteRootFactor f r).comp (X + C r)).Splits :=
    isRealRooted_comp_X_add_C hdelete_rr.1 hdelete_rr.2 r
  have hrestored_split :
      (X * (deleteRootFactor f r).comp (X + C r)).Splits :=
    (isRealRooted_X_mul hdelete_shift_rr.1 hdelete_shift_rr.2).2
  have hg_shift_split : (g.comp (X + C r)).Splits :=
    (isRealRooted_comp_X_add_C hsgn.right_ne_zero hg r).2
  exact Compatible.of_splits_of_pos_right_family hrestored_split hg_shift_split
    (fun μ hμ =>
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_right_natDegree_zero
        hf hg hsgn hleft hdeg hcommon hgdeg μ hμ)

/-- Degree-one-right-endpoint case for the translated two-degree Liu
compatibility target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_right_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 1) :
    Compatible
      (X * (deleteRootFactor f r).comp (X + C r))
      (g.comp (X + C r)) := by
  have hdelete_rr :
      deleteRootFactor f r ≠ 0 ∧ (deleteRootFactor f r).Splits :=
    hleft.delete_ne_zero_and_splits hsgn.left_ne_zero hf
  have hdelete_shift_rr :
      (deleteRootFactor f r).comp (X + C r) ≠ 0 ∧
        ((deleteRootFactor f r).comp (X + C r)).Splits :=
    isRealRooted_comp_X_add_C hdelete_rr.1 hdelete_rr.2 r
  have hrestored_split :
      (X * (deleteRootFactor f r).comp (X + C r)).Splits :=
    (isRealRooted_X_mul hdelete_shift_rr.1 hdelete_shift_rr.2).2
  have hg_shift_split : (g.comp (X + C r)).Splits :=
    (isRealRooted_comp_X_add_C hsgn.right_ne_zero hg r).2
  exact Compatible.of_splits_of_pos_right_family hrestored_split hg_shift_split
    (fun μ hμ =>
      theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_right_natDegree_one
        hf hg hsgn hleft hdeg hcommon hgdeg μ hμ)

/-- The sign-normalized positive-split subtraction-family leaf gives the
translated compatibility target. -/
theorem theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_xSub
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement :=
  theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_rightFamily
    (theorem21LeftFactorReturnTwoDegreeTranslatedRightFamily_of_xSub hsub)

/-- The translated compatibility target gives the original two-degree
factor-return leaf by descending through the translation. -/
theorem theorem21LeftFactorReturnTwoDegree_of_translatedCompatible
    (htranslated :
      theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement) :
    theorem21LeftFactorReturnTwoDegreeStatement := by
  intro f g r s hf hg hsgn hleft hdeg hcommon
  exact hleft.compatible_of_translated_restore
    (htranslated hf hg hsgn hleft hdeg hcommon)

/-- Constant-right-endpoint base case for the original two-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegree_of_right_natDegree_zero
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 0) :
    Compatible f g :=
  hleft.compatible_of_translated_restore
    (theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_right_natDegree_zero
      hf hg hsgn hleft hdeg hcommon hgdeg)

/-- Degree-one-right-endpoint case for the original two-degree left
factor-return leaf. -/
theorem theorem21LeftFactorReturnTwoDegree_of_right_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hleft : LeftRootCountBranch f g r s)
    (hdeg : f.natDegree = g.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec (deleteRootFactor f r) k ∧ Prec g k)
    (hgdeg : g.natDegree = 1) :
    Compatible f g :=
  hleft.compatible_of_translated_restore
    (theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_right_natDegree_one
      hf hg hsgn hleft hdeg hcommon hgdeg)

/-- The three left-branch factor-return cases.  The right-branch cases follow
by symmetry. -/
def theorem21LeftFactorReturnDegreeCasesStatement : Prop :=
  theorem21LeftFactorReturnSameDegreeStatement ∧
    theorem21LeftFactorReturnSuccDegreeStatement ∧
      theorem21LeftFactorReturnTwoDegreeStatement

/-- Same-degree and succ-degree leaves plus the translated two-degree target
give the full left-branch factor-return case package. -/
theorem theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_translatedTwo
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (htwo : theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  ⟨hsame, hsucc,
    theorem21LeftFactorReturnTwoDegree_of_translatedCompatible htwo⟩

/-- Same-degree and succ-degree leaves plus the positive-split subtraction
family leaf give the full left-branch factor-return case package. -/
theorem theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_xSub
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (hsub :
      positiveSplitLeftSuccDegreeTranslatedXSubRightFamilyStatement) :
    theorem21LeftFactorReturnDegreeCasesStatement :=
  theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_translatedTwo hsame hsucc
    (theorem21LeftFactorReturnTwoDegreeTranslatedCompatible_of_xSub hsub)

/-- Same-degree right-branch factor-return target. -/
def theorem21RightFactorReturnSameDegreeStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      RightRootCountBranch f g r s →
        g.natDegree = f.natDegree →
          (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
            Compatible f g

/-- Succ-degree right-branch factor-return target. -/
def theorem21RightFactorReturnSuccDegreeStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      RightRootCountBranch f g r s →
        g.natDegree = f.natDegree + 1 →
          (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
            Compatible f g

/-- Two-degree-gap right-branch factor-return target. -/
def theorem21RightFactorReturnTwoDegreeStatement : Prop :=
  ∀ {f g : ℝ[X]} {r s : ℝ},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      RightRootCountBranch f g r s →
        g.natDegree = f.natDegree + 2 →
          (∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k) →
            Compatible f g

/-- The right same-degree factor-return case follows from the left same-degree
case by swapping the two polynomials. -/
theorem theorem21RightFactorReturnSameDegree_of_leftSameDegree
    (hleft : theorem21LeftFactorReturnSameDegreeStatement) :
    theorem21RightFactorReturnSameDegreeStatement := by
  exact fun {f} {g} {r} {s} hf hg hsgn hright hdeg hcommon =>
    (hleft (f := g) (g := f) (r := s) (s := r)
      hg hf hsgn.symm hright.toLeftBranch_symm hdeg
      (rightDeletionPairCommonInterleaver_symm hcommon)).comm

/-- The right successor-degree factor-return case follows from the left
successor-degree case by swapping the two polynomials. -/
theorem theorem21RightFactorReturnSuccDegree_of_leftSuccDegree
    (hleft : theorem21LeftFactorReturnSuccDegreeStatement) :
    theorem21RightFactorReturnSuccDegreeStatement := by
  exact fun {f} {g} {r} {s} hf hg hsgn hright hdeg hcommon =>
    (hleft (f := g) (g := f) (r := s) (s := r)
      hg hf hsgn.symm hright.toLeftBranch_symm hdeg
      (rightDeletionPairCommonInterleaver_symm hcommon)).comm

/-- The right two-degree-gap factor-return case follows from the left
two-degree-gap case by swapping the two polynomials. -/
theorem theorem21RightFactorReturnTwoDegree_of_leftTwoDegree
    (hleft : theorem21LeftFactorReturnTwoDegreeStatement) :
    theorem21RightFactorReturnTwoDegreeStatement := by
  exact fun {f} {g} {r} {s} hf hg hsgn hright hdeg hcommon =>
    (hleft (f := g) (g := f) (r := s) (s := r)
      hg hf hsgn.symm hright.toLeftBranch_symm hdeg
      (rightDeletionPairCommonInterleaver_symm hcommon)).comm

/-- Constant-left-endpoint base case for the right two-degree factor-return
leaf, obtained by symmetry from the left constant-right base case. -/
theorem theorem21RightFactorReturnTwoDegree_of_left_natDegree_zero
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 0) :
    Compatible f g :=
  (theorem21LeftFactorReturnTwoDegree_of_right_natDegree_zero
    (f := g) (g := f) (r := s) (s := r)
    hg hf hsgn.symm hright.toLeftBranch_symm hdeg
    (rightDeletionPairCommonInterleaver_symm hcommon) hfdeg).comm

/-- Degree-one-left-endpoint base case for the right two-degree factor-return
leaf, obtained by symmetry from the left degree-one-right base case. -/
theorem theorem21RightFactorReturnTwoDegree_of_left_natDegree_one
    {f g : ℝ[X]} {r s : ℝ}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hright : RightRootCountBranch f g r s)
    (hdeg : g.natDegree = f.natDegree + 2)
    (hcommon : ∃ k : ℝ[X], Prec f k ∧ Prec (deleteRootFactor g s) k)
    (hfdeg : f.natDegree = 1) :
    Compatible f g :=
  (theorem21LeftFactorReturnTwoDegree_of_right_natDegree_one
    (f := g) (g := f) (r := s) (s := r)
    hg hf hsgn.symm hright.toLeftBranch_symm hdeg
    (rightDeletionPairCommonInterleaver_symm hcommon) hfdeg).comm

/-- Degree-case split needed to prove the factor-return principle. -/
def theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement :
    Prop :=
  theorem21LeftFactorReturnSameDegreeStatement ∧
    theorem21LeftFactorReturnSuccDegreeStatement ∧
      theorem21LeftFactorReturnTwoDegreeStatement ∧
        theorem21RightFactorReturnSameDegreeStatement ∧
          theorem21RightFactorReturnSuccDegreeStatement ∧
            theorem21RightFactorReturnTwoDegreeStatement

/-- Left factor-return degree cases supply all six left/right cases by
symmetry. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftCases
    (hcases : theorem21LeftFactorReturnDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement := by
  rcases hcases with ⟨hleft_same, hleft_succ, hleft_two⟩
  exact
    ⟨hleft_same, hleft_succ, hleft_two,
      theorem21RightFactorReturnSameDegree_of_leftSameDegree hleft_same,
      theorem21RightFactorReturnSuccDegree_of_leftSuccDegree hleft_succ,
      theorem21RightFactorReturnTwoDegree_of_leftTwoDegree hleft_two⟩

/-- The explicit factor-return principle follows from its six restored-degree
cases. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_degreeCases
    (hcases :
      theorem21DeletionPairCommonInterleaverFactorReturnDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement := by
  rcases hcases with
    ⟨hleft_same, hleft_succ, hleft_two, hright_same, hright_succ,
      hright_two⟩
  intro f g r s hf hg hsgn
  constructor
  · intro hleft hcommon
    rcases hleft.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.left_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hleft_same hf hg hsgn hleft hdeg hcommon
    · exact hleft_succ hf hg hsgn hleft hdeg hcommon
    · exact hleft_two hf hg hsgn hleft hdeg hcommon
  · intro hright hcommon
    rcases hright.natDegree_eq_or_eq_succ_or_eq_succ_succ
        hsgn.right_ne_zero hf hg with hdeg | hdeg | hdeg
    · exact hright_same hf hg hsgn hright hdeg hcommon
    · exact hright_succ hf hg hsgn hright hdeg hcommon
    · exact hright_two hf hg hsgn hright hdeg hcommon

/-- It is enough to prove the left-branch factor-return cases; the right branch
is symmetric. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (hcases : theorem21LeftFactorReturnDegreeCasesStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_degreeCases
    (theorem21DeletionPairCommonInterleaverFactorReturnDegreeCases_of_leftCases
      hcases)

/-- The factor-return principle follows from same/succ left leaves and the
translated two-degree compatibility target. -/
theorem theorem21DeletionPairCommonInterleaverFactorReturn_of_sameSucc_and_translatedTwo
    (hsame : theorem21LeftFactorReturnSameDegreeStatement)
    (hsucc : theorem21LeftFactorReturnSuccDegreeStatement)
    (htwo : theorem21LeftFactorReturnTwoDegreeTranslatedCompatibleStatement) :
    theorem21DeletionPairCommonInterleaverFactorReturnStatement :=
  theorem21DeletionPairCommonInterleaverFactorReturn_of_leftCases
    (theorem21LeftFactorReturnDegreeCases_of_sameSucc_and_translatedTwo
      hsame hsucc htwo)

/-- Reverse half of Liu Theorem 2.1, isolated as a statement target. -/
def theorem21RootCountBranchesToCompatibleStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      theorem21RootCountBranches f g → Compatible f g

/-- Forward half of Liu Theorem 2.1, isolated as a statement target. -/
def theorem21CompatibleToRootCountBranchesStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      Compatible f g → theorem21RootCountBranches f g

/-- Forward half extracted from the paper-shaped Liu Theorem 2.1 statement. -/
theorem theorem21CompatibleToRootCountBranches_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    theorem21CompatibleToRootCountBranchesStatement := by
  intro f g hf hg hsgn
  exact (h f g hf hg hsgn).1

/-- Reverse half extracted from the paper-shaped Liu Theorem 2.1 statement. -/
theorem theorem21RootCountBranchesToCompatible_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    theorem21RootCountBranchesToCompatibleStatement := by
  intro f g hf hg hsgn
  exact (h f g hf hg hsgn).2

/-- Reassemble Liu Theorem 2.1 from separately proved forward and reverse
directions. -/
theorem theorem21CompatibleRootCount_of_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreverse : theorem21RootCountBranchesToCompatibleStatement) :
    theorem21CompatibleRootCountStatement := by
  intro f g hf hg hsgn
  exact ⟨hforward hf hg hsgn, hreverse hf hg hsgn⟩

/-- Nonconstant reverse half of Liu Theorem 2.1, isolated as a statement
target. -/
def theorem21RootCountBranchesToCompatibleNonconstantStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        theorem21RootCountBranches f g → Compatible f g

/-- Nonconstant forward half of Liu Theorem 2.1, isolated as a statement
target. -/
def theorem21CompatibleToRootCountBranchesNonconstantStatement : Prop :=
  ∀ {f g : ℝ[X]},
    f.Splits → g.Splits → OppositeLeadingSigns f g →
      f.natDegree ≠ 0 → g.natDegree ≠ 0 →
        Compatible f g → theorem21RootCountBranches f g

/-- Forward half extracted from the nonconstant Liu Theorem 2.1 statement. -/
theorem theorem21CompatibleToRootCountBranchesNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNonconstantStatement) :
    theorem21CompatibleToRootCountBranchesNonconstantStatement := by
  intro f g hf hg hsgn hf_deg hg_deg
  exact (h f g hf hg hsgn hf_deg hg_deg).1

/-- Reverse half extracted from the nonconstant Liu Theorem 2.1 statement. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNonconstantStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement := by
  intro f g hf hg hsgn hf_deg hg_deg
  exact (h f g hf hg hsgn hf_deg hg_deg).2

/-- Reassemble the nonconstant Liu Theorem 2.1 statement from separately
proved forward and reverse directions. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_reverse
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreverse : theorem21RootCountBranchesToCompatibleNonconstantStatement) :
    theorem21CompatibleRootCountNonconstantStatement := by
  intro f g hf hg hsgn hf_deg hg_deg
  exact ⟨hforward hf hg hsgn hf_deg hg_deg,
    hreverse hf hg hsgn hf_deg hg_deg⟩

/-- The branch-retaining deletion-pair package reduces the reverse direction
of Liu Theorem 2.1 to the explicit factor-return principle. -/
theorem theorem21RootCountBranchesToCompatible_of_deletionPairFactorReturn
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21RootCountBranchesToCompatibleStatement := by
  intro f g hf hg hsgn hbranches
  have hinterleaver :
      theorem21DeletionPairCommonInterleaverBranches f g :=
    theorem21DeletionPairCommonInterleaverBranches_of_theorem21RootCountBranches
      hf hg hsgn hbranches
  rcases hinterleaver with ⟨r, s, hleft | hright⟩
  · exact (hreturn hf hg hsgn).1 hleft.1 hleft.2
  · exact (hreturn hf hg hsgn).2 hright.1 hright.2

/-- Liu Theorem 2.1 follows from the isolated forward root-count direction and
the deletion-pair factor-return principle. -/
theorem theorem21CompatibleRootCount_of_forward_and_deletionPairFactorReturn
    (hforward : theorem21CompatibleToRootCountBranchesStatement)
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21CompatibleRootCountStatement :=
  theorem21CompatibleRootCount_of_forward_and_reverse hforward
    (theorem21RootCountBranchesToCompatible_of_deletionPairFactorReturn hreturn)

/-- The deletion-pair factor-return principle also reduces the nonconstant
reverse direction of Liu Theorem 2.1. -/
theorem theorem21RootCountBranchesToCompatibleNonconstant_of_deletionPairFactorReturn
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21RootCountBranchesToCompatibleNonconstantStatement := by
  intro f g hf hg hsgn _hf_deg _hg_deg hbranches
  exact theorem21RootCountBranchesToCompatible_of_deletionPairFactorReturn
    hreturn hf hg hsgn hbranches

/-- The nonconstant Liu Theorem 2.1 statement follows from its isolated
forward direction and the deletion-pair factor-return principle. -/
theorem theorem21CompatibleRootCountNonconstant_of_forward_and_deletionPairFactorReturn
    (hforward : theorem21CompatibleToRootCountBranchesNonconstantStatement)
    (hreturn : theorem21DeletionPairCommonInterleaverFactorReturnStatement) :
    theorem21CompatibleRootCountNonconstantStatement :=
  theorem21CompatibleRootCountNonconstant_of_forward_and_reverse hforward
    (theorem21RootCountBranchesToCompatibleNonconstant_of_deletionPairFactorReturn
      hreturn)

/-- Normalized deletion-pair compatibility data obtained from Liu branch data.
The four leaves match the four possible positive-leading normalizations of the
left/right deletion branches. -/
def theorem21PositiveDeletionCompatibleBranches (f g : ℝ[X]) : Prop :=
  ∃ r s,
    (Compatible (deleteRootFactor f r) (-g) ∨
        Compatible (-(deleteRootFactor f r)) g) ∨
      (Compatible f (-(deleteRootFactor g s)) ∨
        Compatible (-f) (deleteRootFactor g s))

/-- Branch-retaining common-interleaver data imply the corresponding
normalized deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_deletionPairCommonInterleaverBranches
    {f g : ℝ[X]} (hsgn : OppositeLeadingSigns f g)
    (h : theorem21DeletionPairCommonInterleaverBranches f g) :
    theorem21PositiveDeletionCompatibleBranches f g := by
  rcases h with ⟨r, s, hleft | hright⟩
  · exact ⟨r, s, Or.inl
      (hleft.1.positiveDeletionPair_compatible_of_commonInterleaver
        hsgn hleft.2)⟩
  · exact ⟨r, s, Or.inr
      (hright.1.positiveDeletionPair_compatible_of_commonInterleaver
        hsgn hright.2)⟩

/-- Positive deletion root-count branches imply the corresponding normalized
deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_positiveDeletionCountBranches
    {f g : ℝ[X]} (h : theorem21PositiveDeletionCountBranches f g) :
    theorem21PositiveDeletionCompatibleBranches f g := by
  rcases h with ⟨r, s, hleft | hright⟩
  · rcases hleft with hfg | hfg
    · exact ⟨r, s, Or.inl (Or.inl hfg.compatible)⟩
    · exact ⟨r, s, Or.inl (Or.inr hfg.compatible)⟩
  · rcases hright with hfg | hfg
    · exact ⟨r, s, Or.inr (Or.inl hfg.compatible)⟩
    · exact ⟨r, s, Or.inr (Or.inr hfg.compatible)⟩

/-- Liu root-count branches imply normalized deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_theorem21RootCountBranches
    {f g : ℝ[X]} (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hsgn : OppositeLeadingSigns f g) (h : theorem21RootCountBranches f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_deletionPairCommonInterleaverBranches
    hsgn (theorem21DeletionPairCommonInterleaverBranches_of_theorem21RootCountBranches
      hf_splits hg_splits hsgn h)

/-- The forward direction of Liu Theorem 2.1 supplies normalized deletion
compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_theorem21RootCountBranches
    hf hg hsgn (theorem21RootCountBranches_of_compatible h hf hg hsgn hcompat)

/-- The nonconstant forward direction of Liu Theorem 2.1 supplies normalized
deletion compatibility branches. -/
theorem theorem21PositiveDeletionCompatibleBranches_of_compatible_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21PositiveDeletionCompatibleBranches f g :=
  theorem21PositiveDeletionCompatibleBranches_of_theorem21RootCountBranches
    hf hg hsgn
      (theorem21RootCountBranches_of_compatible_nonconstant h hf hg hsgn
        hf_deg hg_deg hcompat)

/-- The forward direction of Liu Theorem 2.1 supplies branch-retaining common
interleaver witnesses for the actual deletion pair. -/
theorem theorem21DeletionPairCommonInterleaverBranches_of_compatible
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    theorem21DeletionPairCommonInterleaverBranches f g :=
  theorem21DeletionPairCommonInterleaverBranches_of_theorem21RootCountBranches
    hf hg hsgn (theorem21RootCountBranches_of_compatible h hf hg hsgn hcompat)

/-- The nonconstant forward direction of Liu Theorem 2.1 supplies
branch-retaining common interleaver witnesses for the actual deletion pair. -/
theorem theorem21DeletionPairCommonInterleaverBranches_of_compatible_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    theorem21DeletionPairCommonInterleaverBranches f g :=
  theorem21DeletionPairCommonInterleaverBranches_of_theorem21RootCountBranches
    hf hg hsgn
      (theorem21RootCountBranches_of_compatible_nonconstant h hf hg hsgn
        hf_deg hg_deg hcompat)

/-- Liu Theorem 2.1, restated with branch-retaining deletion-pair
common-interleaver witnesses. -/
theorem compatible_iff_theorem21DeletionPairCommonInterleaverBranches
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g) :
    Compatible f g ↔ theorem21DeletionPairCommonInterleaverBranches f g :=
  ⟨theorem21DeletionPairCommonInterleaverBranches_of_compatible h hf hg hsgn,
    fun hbranches =>
      compatible_of_theorem21RootCountBranches h hf hg hsgn
        (theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
          hbranches)⟩

/-- The nonconstant Liu Theorem 2.1 statement, restated with branch-retaining
deletion-pair common-interleaver witnesses. -/
theorem compatible_iff_theorem21DeletionPairCommonInterleaverBranches_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0) :
    Compatible f g ↔ theorem21DeletionPairCommonInterleaverBranches f g :=
  ⟨theorem21DeletionPairCommonInterleaverBranches_of_compatible_nonconstant
      h hf hg hsgn hf_deg hg_deg,
    fun hbranches =>
      compatible_of_theorem21RootCountBranches_nonconstant h hf hg hsgn
        hf_deg hg_deg
        (theorem21RootCountBranches_of_deletionPairCommonInterleaverBranches
          hbranches)⟩

/-- Same-degree common-interleaver endpoint from the Liu-side positive-split
root-count leaf. -/
theorem sameDegreePairHasCommonInterleaver_nonneg_of_positiveSplitRootCount
    (hpack : positiveSplitSameDegreeRootCountAboveNonRootStatement) :
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  exact (hpack hf_pos hg_pos hfnn hgnn hfg hdeg hno)
    |>.pairHasCommonInterleaver_of_sameDegree hdeg

/-- Succ-degree common-interleaver endpoint from the Liu-side positive-split
root-count leaf. -/
theorem succDegreePairHasCommonInterleaver_nonneg_of_positiveSplitRootCount
    (hpack : positiveSplitSuccDegreeRootCountAboveNonRootStatement) :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement := by
  intro f g hf_pos hg_pos hfnn hgnn hfg hdeg hno
  have hf_split : f.Splits :=
    PosComboSuccDegreeLeftSplitsNonnegStatement_of_rootContinuity
      hf_pos hg_pos hfnn hgnn hfg hdeg
  exact (hpack hf_pos hg_pos hfnn hgnn hfg hdeg hno hf_split)
    |>.pairHasCommonInterleaver_of_succDegree hdeg

/-- The two positive-split root-count leaves supply the existing
positive-leading compatibility-to-common-interleaver bridge. -/
theorem
    compatiblePairHasCommonInterleaver_of_positiveSplitRootCountAboveNonRoot
    (hsame : positiveSplitSameDegreeRootCountAboveNonRootStatement)
    (hsucc : positiveSplitSuccDegreeRootCountAboveNonRootStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_pairDegreeSplit_via_nonnegShift
    (sameDegreePairHasCommonInterleaver_nonneg_of_positiveSplitRootCount hsame)
    (succDegreePairHasCommonInterleaver_nonneg_of_positiveSplitRootCount hsucc)

/-- The strict-upper non-root count leaves also route through the
positive-split package before reaching the common-interleaver endpoint. -/
theorem compatiblePairHasCommonInterleaver_of_rootCountAboveNonRoot_via_positiveSplit
    (hsame : PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement)
    (hsucc : PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_positiveSplitRootCountAboveNonRoot
    (positiveSplitSameDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot hsame)
    (positiveSplitSuccDegreeRootCountAboveNonRoot_of_rootCountAboveNonRoot hsucc)

/-- The checked same-degree analytic count spine and the succ-degree
common-left-interleaver reduction supply the compatible-pair endpoint. -/
theorem
    compatiblePairHasCommonInterleaver_of_sameDegreeAnalytic_and_succCommonLeftInterleaver
    (hsucc : PosComboNoCommonSuccDegreeCommonLeftInterleaverNonnegStatement) :
    CompatiblePairHasCommonInterleaverStatement :=
  compatiblePairHasCommonInterleaver_of_positiveSplitRootCountAboveNonRoot
    positiveSplitSameDegreeRootCountAboveNonRoot_from_analytic
    (positiveSplitSuccDegreeRootCountAboveNonRoot_of_commonLeftInterleaver
      hsucc)

/-- Finite-family Chudnovsky--Seymour package from the Liu-side
positive-split root-count leaves. -/
theorem chudnovskySeymour_fourWay_of_positiveSplitRootCountAboveNonRoot
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsame : positiveSplitSameDegreeRootCountAboveNonRootStatement)
    (hsucc : positiveSplitSuccDegreeRootCountAboveNonRootStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos (fs := fs) hrr hpos
    (compatiblePairHasCommonInterleaver_of_positiveSplitRootCountAboveNonRoot
      hsame hsucc)

/-- Finite-family Chudnovsky--Seymour package from the checked same-degree
analytic spine and the succ-degree common-left-interleaver reduction. -/
theorem
    chudnovskySeymour_fourWay_of_sameDegreeAnalytic_and_succCommonLeftInterleaver
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, (f ≠ 0 ∧ f.Splits))
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hsucc : PosComboNoCommonSuccDegreeCommonLeftInterleaverNonnegStatement) :
    ChudnovskySeymourFourWayPackage fs :=
  chudnovskySeymour_fourWay_of_pairBridgePos (fs := fs) hrr hpos
    (compatiblePairHasCommonInterleaver_of_sameDegreeAnalytic_and_succCommonLeftInterleaver
      hsucc)

/-- Liu Corollary 2.2: compatible real-rooted polynomials with opposite leading
signs have degree gap at most two. -/
def corollary22DegreeDiffStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    Compatible f g → |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2

/-- Nonconstant form of Liu Corollary 2.2. -/
def corollary22DegreeDiffNonconstantStatement : Prop :=
  ∀ f g : ℝ[X], f.Splits → g.Splits → OppositeLeadingSigns f g →
    f.natDegree ≠ 0 → g.natDegree ≠ 0 →
      Compatible f g → |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2

/-- Projection form of `corollary22DegreeDiffStatement`. -/
theorem corollary22DegreeDiff
    (h : corollary22DegreeDiffStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  h f g hf hg hsgn hcompat

/-- Projection form of `corollary22DegreeDiffNonconstantStatement`. -/
theorem corollary22DegreeDiff_nonconstant
    (h : corollary22DegreeDiffNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  h f g hf hg hsgn hf_deg hg_deg hcompat

/-- Liu Corollary 2.2 follows from the Theorem 2.1 compatibility criterion. -/
theorem corollary22DegreeDiff_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) :
    corollary22DegreeDiffStatement :=
  fun _ _ hf hg hsgn hcompat =>
    natDegree_abs_sub_le_two_of_theorem21RootCountBranches hf hg hsgn
      (theorem21RootCountBranches_of_compatible h hf hg hsgn hcompat)

/-- Nonconstant Liu Corollary 2.2 follows from the nonconstant Theorem 2.1
compatibility criterion. -/
theorem corollary22DegreeDiffNonconstant_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountNonconstantStatement) :
    corollary22DegreeDiffNonconstantStatement :=
  fun _ _ hf hg hsgn hf_deg hg_deg hcompat =>
    natDegree_abs_sub_le_two_of_theorem21RootCountBranches hf hg hsgn
      (theorem21RootCountBranches_of_compatible_nonconstant h hf hg hsgn
        hf_deg hg_deg hcompat)

theorem natDegree_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  corollary22DegreeDiff (corollary22DegreeDiff_of_theorem21CompatibleRootCount h)
    hf hg hsgn hcompat

theorem
    natDegree_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  corollary22DegreeDiff_nonconstant
    (corollary22DegreeDiffNonconstant_of_theorem21CompatibleRootCount h)
    hf hg hsgn hf_deg hg_deg hcompat

/-- Direct degree-gap consequence via the swapped branch projection of
Liu Theorem 2.1. -/
theorem natDegree_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount_symm
    (h : theorem21CompatibleRootCountStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  natDegree_abs_sub_le_two_of_theorem21RootCountBranches_symm hf hg hsgn
    (theorem21RootCountBranches_symm_of_compatible h hf hg hsgn hcompat)

/-- Nonconstant direct degree-gap consequence via the swapped branch
projection of Liu Theorem 2.1. -/
theorem
    natDegree_abs_sub_le_two_of_compatible_of_theorem21CompatibleRootCount_symm_nonconstant
    (h : theorem21CompatibleRootCountNonconstantStatement) {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits) (hsgn : OppositeLeadingSigns f g)
    (hf_deg : f.natDegree ≠ 0) (hg_deg : g.natDegree ≠ 0)
    (hcompat : Compatible f g) :
    |((f.natDegree : ℤ) - (g.natDegree : ℤ))| ≤ 2 :=
  natDegree_abs_sub_le_two_of_theorem21RootCountBranches_symm hf hg hsgn
    (theorem21RootCountBranches_symm_of_compatible_nonconstant h hf hg hsgn
      hf_deg hg_deg hcompat)

end LiuOppositeSigns
end RealRooted
