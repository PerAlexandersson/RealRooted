module

public import RealRooted.BrandenLeite.AffineLogarithm
import RealRooted.Mathlib.RingTheory.PowerSeries.LogarithmMul
import RealRooted.Mathlib.RingTheory.PowerSeries.LogarithmPositive
import Mathlib.Tactic

/-! # Ring maps and constant parameter coefficients of formal logarithms -/

public section

open PowerSeries

namespace RealRooted.BrandenLeite

/-- Setting the affine parameter to zero recovers the negative logarithm of
its constant denominator series. -/
theorem coeff_zero_affineLogCoeff (Q B : PowerSeries ℝ)
    (hQ : constantCoeff Q = 1) (hB : constantCoeff B = 0) (n : ℕ) :
    (affineLogCoeff Q B n).coeff 0 = coeff n (-logOf Q) := by
  let H := map Polynomial.C Q - C Polynomial.X * map Polynomial.C B
  let φ : Polynomial ℝ →+* ℝ := Polynomial.evalRingHom 0
  have hH : constantCoeff H = 1 := constantCoeff_map_C_sub_C_X_mul_map_C hQ hB
  have hmap : map φ H = Q := by
    ext m
    simp [H, φ, coeff_map]
  have hlog : map φ (-logOf H) = -logOf Q := by
    rw [map_neg, map_logOf φ H hH, hmap]
  have hc := congrArg (coeff n) hlog
  simpa only [coeff_map, affineLogCoeff, H, φ,
    Polynomial.coe_evalRingHom, ← Polynomial.coeff_zero_eq_eval_zero] using hc

/-- A nonempty positive linear product gives a strictly positive constant
parameter coefficient in every positive logarithmic row. -/
theorem coeff_zero_affineLogCoeff_prod_linear_pos {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (B : PowerSeries ℝ)
    (hB : constantCoeff B = 0) {n : ℕ} (hn : n ≠ 0) :
    0 < (affineLogCoeff
      (∏ i ∈ s, (1 - C (α i) * X : PowerSeries ℝ)) B n).coeff 0 := by
  rw [coeff_zero_affineLogCoeff _ _ (by simp) hB]
  exact coeff_neg_logOf_prod_one_sub_C_mul_X_pos s hs α hα hn

end RealRooted.BrandenLeite
