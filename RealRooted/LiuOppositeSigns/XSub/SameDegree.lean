import RealRooted.LiuOppositeSigns.PositiveSplitPair
import RealRooted.QuadraticRoot

/-!
# Liu same-degree and right-successor x-subtraction base cases

This module contains the constant and linear endpoint cases of the
positive-split translated x-subtraction pencils for the same-degree and
right-successor branches.
-/

open Polynomial Filter

namespace RealRooted
namespace LiuOppositeSigns

/-- Degree guardrail for the translated x-subtraction endpoint: in the
left-successor case, `g.comp (X + C r)` and `X * f.comp (X + C r)` differ by
two degrees, so this endpoint cannot be proved by a direct `StrictInterl` witness. -/
theorem not_positiveSplitLeftSuccDegreeTranslatedXStrictInterl
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hdeg : f.natDegree = g.natDegree + 1) :
    ¬ StrictInterl (g.comp (X + C r)) (X * f.comp (X + C r)) := by
  intro hstrictInterl
  have hF_ne : f.comp (X + C r) ≠ 0 :=
    (hpair.left_pos.comp_X_add_C r).ne_zero
  have hXF_deg :
      (X * f.comp (X + C r)).natDegree =
        (f.comp (X + C r)).natDegree + 1 :=
    natDegree_X_mul hF_ne
  have hF_deg : (f.comp (X + C r)).natDegree = f.natDegree := by simp [Polynomial.natDegree_comp]
  have hG_deg : (g.comp (X + C r)).natDegree = g.natDegree := by simp [Polynomial.natDegree_comp]
  have hgap :
      (g.comp (X + C r)).natDegree + 1 <
        (X * f.comp (X + C r)).natDegree := by
    rw [hXF_deg, hF_deg, hG_deg]
    lia
  exact hstrictInterl.not_of_left_natDegree_succ_lt_right hgap

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
  have ha_pos : 0 < a := by simpa [HasPosLeadingCoeff, hpdeg, leadingCoeff, a] using hp_pos
  have hd_nonneg : 0 ≤ d := by simpa [d] using hqnn 0
  have hpoly :
      X * p - C μ * q =
        C a * X ^ 2 + C (b - μ * c) * X + C (-μ * d) := by
    rw [hp_eq, hq_eq]
    simp [C_mul, C_sub, C_neg]
    ring
  have hprod_nonneg : 0 ≤ 4 * a * μ * d := by positivity
  have hdisc : 0 ≤ discrim a (b - μ * c) (-μ * d) := by
    rw [discrim]
    linarith [sq_nonneg (b - μ * c), hprod_nonneg]
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
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 0) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ _hμ
  have hfdeg : f.natDegree = 0 := by lia
  have hFdeg : (f.comp (X + C r)).natDegree = 0 := by simpa [Polynomial.natDegree_comp] using hfdeg
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
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree = 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ hμ
  have hfdeg : f.natDegree = 1 := by lia
  have hFdeg : (f.comp (X + C r)).natDegree = 1 := by simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree = 1 := by simpa [Polynomial.natDegree_comp] using hgdeg
  exact splits_X_mul_sub_C_mul_of_natDegree_one_one_right_nonneg
    (hpair.left_pos.comp_X_add_C r) hFdeg hGdeg hgnn hμ

/-- Low-degree right endpoint cases for the same-degree sign-normalized
x-subtraction leaf. -/
theorem positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_le_one
    {f g : ℝ[X]} {r : ℝ}
    (hpair : PositiveSplitRootCountPair f g)
    (hgnn : HasNonnegCoeffs (g.comp (X + C r)))
    (hdeg : f.natDegree = g.natDegree)
    (hgdeg : g.natDegree ≤ 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  by_cases hzero : g.natDegree = 0
  · exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_zero
      hdeg hzero
  · have hone : g.natDegree = 1 := by lia
    exact positiveSplitSameDegreeTranslatedXSubRightFamily_of_right_natDegree_one
      hpair hgnn hdeg hone

/-- Degree-one right endpoint base case for the right-successor
sign-normalized x-subtraction leaf. -/
theorem positiveSplitRightSuccDegreeTranslatedXSubRightFamily_of_right_natDegree_one
    {f g : ℝ[X]} {r : ℝ}
    (hdeg : g.natDegree = f.natDegree + 1)
    (hgdeg : g.natDegree = 1) :
    ∀ μ : ℝ, 0 < μ →
      (X * f.comp (X + C r) - C μ * g.comp (X + C r)).Splits := by
  intro μ _hμ
  have hfdeg : f.natDegree = 0 := by lia
  have hFdeg : (f.comp (X + C r)).natDegree = 0 := by simpa [Polynomial.natDegree_comp] using hfdeg
  have hGdeg : (g.comp (X + C r)).natDegree ≤ 1 := by
    simpa [Polynomial.natDegree_comp] using hgdeg.le
  exact splits_X_mul_sub_C_mul_of_left_natDegree_zero_right_natDegree_le_one
    hFdeg hGdeg μ

end LiuOppositeSigns
end RealRooted
