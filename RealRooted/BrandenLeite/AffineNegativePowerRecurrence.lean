module

import RealRooted.Mathlib.RingTheory.PowerSeries.BinomialDerivative
public import RealRooted.BrandenLeite.AffineNegativePower
public import Mathlib.Basic.Real.Basic
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerRecurrence
import Mathlib.Tactic

/-! Finite coefficient recurrences for canonical affine negative powers. -/

public section

open scoped BigOperators

open PowerSeries

namespace RealRooted.BrandenLeite

/-- The initial row of a normalized affine negative power is one. -/
theorem affineNegativePowerCoeff_zero (κ : ℝ) (Q B : PowerSeries ℝ)
    (hQ : constantCoeff Q = 1) (hB : constantCoeff B = 0) :
    affineNegativePowerCoeff κ Q B 0 = 1 := by
  let H := map Polynomial.C Q - C Polynomial.X * map Polynomial.C B
  have hH : constantCoeff H = 1 := constantCoeff_map_C_sub_C_X_mul_map_C hQ hB
  exact (show coeff 0 (subst (H - 1)
      (binomialSeries (Polynomial ℝ) (-Polynomial.C κ))) = 1 by
    simpa only [coeff_zero_eq_constantCoeff_apply] using
      constantCoeff_subst_binomialSeries_neg (Polynomial.C κ) H hH)

/-- Every coefficient of a canonical affine negative power satisfies the
finite differential recurrence, divided by its nonzero row number. -/
theorem coeff_affineNegativePowerCoeff_recurrence
    (κ : ℝ) (Q B : PowerSeries ℝ)
    (hQ : constantCoeff Q = 1) (hB : constantCoeff B = 0)
    (n i : ℕ) :
    (affineNegativePowerCoeff κ Q B (n + 1)).coeff i =
      -((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ k ∈ Finset.range (n + 1),
          ((n - k : ℕ) + κ * (k + 1 : ℕ)) *
            ∑ j ∈ Finset.range (i + 1),
              (Polynomial.C (coeff (k + 1) Q) -
                Polynomial.X * Polynomial.C (coeff (k + 1) B)).coeff j *
                (affineNegativePowerCoeff κ Q B (n - k)).coeff (i - j) := by
  let H := map Polynomial.C Q - C Polynomial.X * map Polynomial.C B
  have hH : constantCoeff H = 1 := constantCoeff_map_C_sub_C_X_mul_map_C hQ hB
  have hr := coeff_recurrence_of_negPower_ode (Polynomial.C κ) H _
    (by simpa only [coeff_zero_eq_constantCoeff_apply] using hH)
    (subst_binomialSeries_neg_ode (Polynomial.C κ) H hH) n
  have hcoeff (k : ℕ) : coeff k H =
      Polynomial.C (coeff k Q) - Polynomial.X * Polynomial.C (coeff k B) := by
    simp [H, coeff_C_mul]
  have hreindex :
      ∑ j ∈ Finset.range (n + 1),
        ((j : Polynomial ℝ) + Polynomial.C κ * (n + 1 - j : ℕ)) *
          coeff (n + 1 - j) H *
          affineNegativePowerCoeff κ Q B j =
      ∑ k ∈ Finset.range (n + 1),
        Polynomial.C ((n - k : ℕ) + κ * (k + 1 : ℕ)) *
          (coeff (k + 1) H * affineNegativePowerCoeff κ Q B (n - k)) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hidx : n + 1 - (n - k) = k + 1 := by lia
    simp only [Nat.add_sub_cancel, hidx]
    simp only [map_add, map_mul, Polynomial.C_eq_natCast, mul_assoc]
  rw [← Nat.cast_add_one] at hr
  change ((n + 1 : ℕ) : Polynomial ℝ) *
      affineNegativePowerCoeff κ Q B (n + 1) =
      -∑ j ∈ Finset.range (n + 1),
        ((j : Polynomial ℝ) + Polynomial.C κ * (n + 1 - j : ℕ)) *
          coeff (n + 1 - j) H * affineNegativePowerCoeff κ Q B j at hr
  rw [hreindex] at hr
  rw [← Polynomial.C_eq_natCast] at hr
  have hi := congrArg (fun p : Polynomial ℝ => p.coeff i) hr
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_neg, Polynomial.finsetSum_coeff] at hi
  simp only [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hcoeff] at hi
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  apply (mul_left_cancel₀ hn)
  rw [hi]
  field_simp

end RealRooted.BrandenLeite
