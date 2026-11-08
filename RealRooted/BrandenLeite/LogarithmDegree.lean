module

import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerPositive
public import RealRooted.BrandenLeite.AffineLogarithm
import RealRooted.BrandenLeite.LogarithmicCoefficients
import RealRooted.BrandenLeite.AffineLogarithmZero
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerDegree
import Mathlib.Tactic

/-! # Exact degrees and positive coefficients of canonical logarithmic rows -/

public section

open PowerSeries

namespace RealRooted.BrandenLeite

/-- The logarithmic row's nonconstant parameter coefficients inherit the
exact support shift from powers of the numerator series. -/
theorem coeff_affineLogCoeff_zero_and_pos
    (Q B : PowerSeries ℝ) (r : ℕ) (hQ : constantCoeff Q = 1) (hr : r ≠ 0)
    (hB : ∀ n, 0 ≤ coeff n B) (hBzero : ∀ n < r, coeff n B = 0)
    (hBpos : 0 < coeff r B)
    (hQpos : ∀ (k : ℕ), k ≠ 0 → ∀ m, 0 < coeff m
      (subst (Q - 1) (binomialSeries ℝ (-(k : ℝ)))))
    {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) :
    (n < r * k → (affineLogCoeff Q B n).coeff k = 0) ∧
      (r * k ≤ n → 0 < (affineLogCoeff Q B n).coeff k) := by
  have hB0 : constantCoeff B = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hBzero 0 (Nat.pos_of_ne_zero hr)
  rw [coeff_affineLogCoeff_of_ne_zero Q B hQ hB0 hn hk]
  exact const_mul_coeff_pow_mul_zero_and_pos
    (one_div_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hk)) B _ r hB hBzero hBpos
    (hQpos k hk) k n

/-- A positive logarithmic constant coefficient and positive integer negative
powers of the denominator give the exact degree and all coefficient signs. -/
theorem natDegree_affineLogCoeff_and_coeff_pos
    (Q B : PowerSeries ℝ) (r : ℕ) (hQ : constantCoeff Q = 1) (hr : r ≠ 0)
    (hB : ∀ n, 0 ≤ coeff n B) (hBzero : ∀ n < r, coeff n B = 0)
    (hBpos : 0 < coeff r B)
    (hQpos : ∀ (k : ℕ), k ≠ 0 → ∀ m, 0 < coeff m
      (subst (Q - 1) (binomialSeries ℝ (-(k : ℝ)))))
    {n : ℕ} (hn : n ≠ 0) (hzero : 0 < (affineLogCoeff Q B n).coeff 0) :
    (affineLogCoeff Q B n).natDegree = n / r ∧
      ∀ k ≤ n / r, 0 < (affineLogCoeff Q B n).coeff k := by
  refine Polynomial.natDegree_eq_div_and_coeff_pos_of_support hr fun k => ?_
  by_cases hk : k = 0
  · subst hk
    exact ⟨fun h => absurd h (by simp), fun _ => hzero⟩
  · exact coeff_affineLogCoeff_zero_and_pos Q B r hQ hr hB hBzero hBpos hQpos hn hk

/-- Positive linear-factor denominators give logarithmic rows of exact
degree `n/r`, with every coefficient through that degree strictly positive. -/
theorem affineLogCoeff_prod_linear_degree_and_pos {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (B : PowerSeries ℝ) (r : ℕ) (hr : r ≠ 0)
    (hB : ∀ n, 0 ≤ coeff n B) (hBzero : ∀ n < r, coeff n B = 0)
    (hBpos : 0 < coeff r B) {n : ℕ} (hn : n ≠ 0) :
    let Q := ∏ i ∈ s, (1 - C (α i) * X : PowerSeries ℝ)
    (affineLogCoeff Q B n).natDegree = n / r ∧
      ∀ k ≤ n / r, 0 < (affineLogCoeff Q B n).coeff k := by
  dsimp
  apply natDegree_affineLogCoeff_and_coeff_pos _ B r (by simp) hr hB hBzero hBpos
  · intro k hk m
    exact coeff_subst_binomialSeries_neg_prod_linear_pos s hs α hα
      (by exact_mod_cast Nat.pos_of_ne_zero hk) m
  · exact hn
  · apply coeff_zero_affineLogCoeff_prod_linear_pos s hs α hα B
    · rw [← coeff_zero_eq_constantCoeff_apply]
      exact hBzero 0 (Nat.pos_of_ne_zero hr)
    · exact hn

end RealRooted.BrandenLeite
