module

public import RealRooted.EffectiveBKW.PathCube.ResidueBound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Symmetric formulas for two real cofactor residues

We express the sum and squared difference of the two residues using symmetric
polynomials. The formulas hold for arbitrary distinct real poles and a nonreal
pair, before choosing the resolvent branch or proving any amplitude inequality.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube.RationalSeries

/-- Symmetric numerator for the sum of residues, with cofactor `X²+sX+p`. -/
noncomputable def residueSumNumerator (a b u v w s p : ℝ) : ℝ :=
  p ^ 2 + 2 * a * p * s + b * (s ^ 2 - p) - 2 * a * u * p - u * b * s -
    v * p + v * b + w * s + 2 * a * w

/-- Symmetric numerator for the difference of residues before root separation. -/
noncomputable def residueDifferenceNumerator (a b u v w s p : ℝ) : ℝ :=
  -p ^ 2 * s - 2 * a * p * (s ^ 2 - 2 * p) + b * (-s ^ 3 + 3 * p * s) +
    u * (2 * p ^ 2 + 2 * a * p * s + b * (s ^ 2 - 2 * p)) +
    v * (-p * s - 4 * a * p - b * s) + w * (s ^ 2 - 2 * p + 2 * a * s + 2 * b)

/-- The common positive cofactor denominator in symmetric coordinates. -/
noncomputable def residueDenominator (a b s p : ℝ) : ℝ :=
  p ^ 2 + 2 * a * p * s + b * s ^ 2 + (4 * a ^ 2 - 2 * b) * p +
    2 * a * b * s + b ^ 2

/-- Scaling all reciprocal roots and numerator weights preserves the real residues. -/
theorem realResidue_div (a c u v w x y : ℝ) {R : ℝ} (hR : R ≠ 0) :
    realResidue (a / R) (c / R) (u / R) (v / R ^ 2) (w / R ^ 3)
        (x / R) (y / R) = realResidue a c u v w x y := by
  have hn : numeratorValue (u / R) (v / R ^ 2) (w / R ^ 3) (x / R) =
      numeratorValue u v w x / R ^ 3 := by
    unfold numeratorValue
    field_simp [hR]
  have hd : pairDistance (a / R) (c / R) (x / R) * (x / R - y / R) =
      pairDistance a c x * (x - y) / R ^ 3 := by
    unfold pairDistance
    field_simp [hR]
  unfold realResidue
  rw [hn, hd, div_div_div_cancel_right₀ (pow_ne_zero 3 hR)]

/-- The product of squared distances is the symmetric cofactor denominator. -/
theorem pairDistance_mul (a c x y : ℝ) :
    pairDistance a c x * pairDistance a c y =
      residueDenominator a (a ^ 2 + c ^ 2) (-(x + y)) (x * y) := by
  unfold pairDistance residueDenominator
  ring

/-- The sum of the actual real residues has the symmetric numerator formula. -/
theorem realResidue_add {a c u v w x y : ℝ} (hc : 0 < c) (hxy : x ≠ y) :
    realResidue a c u v w x y + realResidue a c u v w y x =
      residueSumNumerator a (a ^ 2 + c ^ 2) u v w (-(x + y)) (x * y) /
        residueDenominator a (a ^ 2 + c ^ 2) (-(x + y)) (x * y) := by
  rw [← pairDistance_mul]
  have hx : pairDistance a c x ≠ 0 := by unfold pairDistance; positivity
  have hy : pairDistance a c y ≠ 0 := by unfold pairDistance; positivity
  unfold realResidue numeratorValue residueSumNumerator
  field_simp [hx, hy, sub_ne_zero.mpr hxy, sub_ne_zero.mpr hxy.symm]
  unfold pairDistance
  ring

/-- The squared residue difference is symmetric; the discriminant is the squared separation. -/
theorem realResidue_sub_sq {a c u v w x y : ℝ} (hc : 0 < c) (hxy : x ≠ y) :
    (realResidue a c u v w x y - realResidue a c u v w y x) ^ 2 =
      residueDifferenceNumerator a (a ^ 2 + c ^ 2) u v w (-(x + y)) (x * y) ^ 2 /
        (residueDenominator a (a ^ 2 + c ^ 2) (-(x + y)) (x * y) ^ 2 *
          ((-(x + y)) ^ 2 - 4 * (x * y))) := by
  rw [← pairDistance_mul]
  have hx : pairDistance a c x ≠ 0 := by unfold pairDistance; positivity
  have hy : pairDistance a c y ≠ 0 := by unfold pairDistance; positivity
  have hdisc : (-(x + y)) ^ 2 - 4 * (x * y) = (x - y) ^ 2 := by ring
  rw [hdisc]
  unfold realResidue numeratorValue residueDifferenceNumerator
  field_simp [hx, hy, sub_ne_zero.mpr hxy, sub_ne_zero.mpr hxy.symm]
  unfold pairDistance
  ring

end RealRooted.EffectiveBKW.PathCube.RationalSeries
