module

public import RealRooted.BrandenLeite.AffineNegativePower
public import RealRooted.Toeplitz.HessenbergRows
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerOne
import Mathlib.Tactic.Ring

/-! # Hessenberg rows as canonical exponent-one negative-power coefficients -/

public section

namespace RealRooted.BrandenLeite

/-- A Hessenberg row agrees with the canonical negative-power coefficient at exponent one. -/
theorem hessenbergRow_eq_affineNegativePowerCoeff
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (k : ℕ) :
    hessenbergRow A k =
      affineNegativePowerCoeff 1 (hessenbergDet A : PowerSeries ℝ) PowerSeries.X k := by
  let H := hessenbergDenominator A
  have hH : PowerSeries.constantCoeff H = 1 := by
    simpa [H] using constantCoeff_hessenbergDenominator A
  have hcanonical := PowerSeries.mul_subst_binomialSeries_neg_one H hH
  have hold : H * hessenbergRowSeries A = 1 := by
    rw [hessenbergRowSeries]
    exact PowerSeries.mul_invOfUnit _ _ (by simpa [H] using hH)
  have heq : hessenbergRowSeries A =
      PowerSeries.subst (H - 1)
        (PowerSeries.binomialSeries (Polynomial ℝ) (-1 : Polynomial ℝ)) := by
    calc
      _ = hessenbergRowSeries A *
          (H * PowerSeries.subst (H - 1)
            (PowerSeries.binomialSeries (Polynomial ℝ) (-1 : Polynomial ℝ))) := by
          rw [hcanonical, mul_one]
      _ = (H * hessenbergRowSeries A) *
          PowerSeries.subst (H - 1)
            (PowerSeries.binomialSeries (Polynomial ℝ) (-1 : Polynomial ℝ)) := by ring
      _ = _ := by rw [hold, one_mul]
  rw [hessenbergRow, heq]
  simp [affineNegativePowerCoeff, H, hessenbergDenominator, hessenbergCoeffs]

end RealRooted.BrandenLeite
