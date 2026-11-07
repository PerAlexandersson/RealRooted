module

import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerDegree
import RealRooted.Mathlib.Algebra.Polynomial.LinearFactors
public import RealRooted.Basic.ProperPosition
public import RealRooted.Mathlib.RingTheory.PowerSeries.AffineLogarithm
import RealRooted.BrandenLeite.LogarithmicInterlacing
import RealRooted.Mathlib.RingTheory.PowerSeries.LogarithmDegree

/-! The logarithmic Brändén–Leite theorem for factored data. -/

public section

open Polynomial

namespace RealRooted.BrandenLeite

/-- For a nonempty positive product denominator and a PF product numerator
vanishing to order `r`, every positive-index logarithmic coefficient row is
nonzero and split, with strictly negative roots, exact degree `n/r`, positive
coefficients through that degree, and oriented consecutive interlacing. -/
theorem affineLogCoeff_factor_properties
    {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
    (hβ : ∀ j ∈ t, 0 ≤ β j) {c : ℝ} (hc : 0 < c)
    (r : ℕ) (hr : 0 < r) (n : ℕ) (hn : n ≠ 0) :
    let Q : Polynomial ℝ := ∏ i ∈ s, (1 - C (α i) * X)
    let B : Polynomial ℝ := C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X)
    let ℓ := fun m => PowerSeries.affineLogCoeff (Q : PowerSeries ℝ) B m
    ℓ n ≠ 0 ∧ (ℓ n).Splits ∧ (∀ x ∈ (ℓ n).roots, x < 0) ∧
      (ℓ n).natDegree = n / r ∧ (∀ k ≤ n / r, 0 < (ℓ n).coeff k) ∧
      Interl (ℓ n) (ℓ (n + 1)) := by
  let Q : Polynomial ℝ := ∏ i ∈ s, (1 - C (α i) * X)
  let B : Polynomial ℝ := C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X)
  let ℓ := fun m => PowerSeries.affineLogCoeff (Q : PowerSeries ℝ) B m
  have hQcoe : (Q : PowerSeries ℝ) =
      ∏ i ∈ s, (1 - PowerSeries.C (α i) * PowerSeries.X : PowerSeries ℝ) :=
    Polynomial.coe_prod_one_sub_C_mul_X s α
  have hBcoe : (B : PowerSeries ℝ) = PowerSeries.C c * PowerSeries.X ^ r *
      ∏ j ∈ t, (1 + PowerSeries.C (β j) * PowerSeries.X : PowerSeries ℝ) :=
    Polynomial.coe_C_mul_X_pow_prod_one_add_C_mul_X c r t β
  obtain ⟨hBnonneg, hBzero, hBpositive⟩ :=
    PowerSeries.coeff_C_mul_X_pow_prod_linear t β hβ hc r
  have hdegree := PowerSeries.affineLogCoeff_prod_linear_degree_and_pos
    s hs α hα _ r hr hBnonneg hBzero hBpositive hn
  dsimp only at hdegree
  rw [← hQcoe, ← hBcoe] at hdegree
  obtain ⟨hpf, hi⟩ := affineLogCoeff_factor_pf_and_interl s hs α hα t β hβ hc r hr n hn
  have hzero : 0 < (ℓ n).coeff 0 := hdegree.2 0 (Nat.zero_le _)
  have hne : ℓ n ≠ 0 := by
    intro hz
    simp only [hz, Polynomial.coeff_zero, lt_self_iff_false] at hzero
  exact ⟨hne, (hpf.ne_zero_and_splits hne).2,
    roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne hpf.hasNonnegCoeffs hzero.ne',
    hdegree.1, hdegree.2, hi⟩

end RealRooted.BrandenLeite
