import RealRooted.PFPolynomial

/-!
# Linear-factor steps in the polynomial PF cone

This module packages the reusable order-theoretic step
`(D, F) ↦ (X + r) F + X D`. It is independent of the transforms and
combinatorial products that use it.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The linear-factor step combining a current polynomial `F` and a preceding
polynomial `D`. -/
def linearFactorStep (r : ℝ) (D F : ℝ[X]) : ℝ[X] :=
  (X + C r) * F + X * D

/-- If `D` precedes `F` in the PF cone, then `F` precedes their nonnegative
linear-factor step. -/
theorem prec0_linearFactorStep {D F : ℝ[X]} {r : ℝ}
    (hr : 0 ≤ r) (hDF : Prec0 D F)
    (hD : IsPFPolynomial D) (hF : IsPFPolynomial F) :
    Prec0 F (linearFactorStep r D F) := by
  have hX : Prec0 F (X * D) :=
    prec0_mul_X_of_prec0 hDF hD.hasNonnegCoeffs hF.hasNonnegCoeffs
  have hself : Prec0 F F := hF.prec0_self
  have hXF : Prec0 F (X * F) :=
    prec0_mul_X_of_prec0 hself hF.hasNonnegCoeffs hF.hasNonnegCoeffs
  have hcomboX :
      Prec0 F (C (1 : ℝ) * (X * D) + C (1 : ℝ) * (X * F)) :=
    prec0_nonneg_combo_right_of_common_left_of_nonneg hX hXF
      hD.X_mul.hasNonnegCoeffs hF.X_mul.hasNonnegCoeffs zero_le_one zero_le_one
  have hcomboXnn :
      HasNonnegCoeffs
        (C (1 : ℝ) * (X * D) + C (1 : ℝ) * (X * F)) := by
    simpa using hD.X_mul.hasNonnegCoeffs.add hF.X_mul.hasNonnegCoeffs
  have hcombo :
      Prec0 F
        (C (1 : ℝ) *
            (C (1 : ℝ) * (X * D) + C (1 : ℝ) * (X * F)) +
          C r * F) :=
    prec0_nonneg_combo_right_of_common_left_of_nonneg hcomboX hself
      hcomboXnn hF.hasNonnegCoeffs zero_le_one hr
  simp only [C_1, one_mul] at hcombo
  rw [linearFactorStep]
  convert hcombo using 1
  ring

/-- The nonnegative linear-factor step preserves the polynomial PF cone. -/
theorem linearFactorStep_isPF {D F : ℝ[X]} {r : ℝ}
    (hr : 0 ≤ r) (hDF : Prec0 D F)
    (hD : IsPFPolynomial D) (hF : IsPFPolynomial F) :
    IsPFPolynomial (linearFactorStep r D F) := by
  have hprec := prec0_linearFactorStep hr hDF hD hF
  have hnn : HasNonnegCoeffs (linearFactorStep r D F) := by
    rw [linearFactorStep]
    exact ((isPFPolynomial_X_add_C hr).mul hF).hasNonnegCoeffs.add
      hD.X_mul.hasNonnegCoeffs
  by_cases hF0 : F = 0
  · rw [linearFactorStep, hF0, mul_zero, zero_add]
    exact hD.X_mul
  rcases hprec with hleft0 | hright0 | hstrict
  · exact False.elim (hF0 hleft0)
  · simpa [hright0] using IsPFPolynomial.zero
  · exact IsPFPolynomial.of_realRooted_nonneg hnn hstrict.2.1.2

end RealRooted
